package org.unisonweb.util


import java.util.function._

import org.unisonweb.compilation2.{U, U0}

/** Unboxed functions and continuations / callbacks. */
object Unboxed {

  /** A continuation receiving 1 value of type `A`, potentially unboxed. */
  abstract class K[-A] { self =>
    def apply(u: U, a: A): Unit
    final def toK2[B]: K2[A,B] = (u,a,u2,b) => self(u,a)
  }

  /** A continuation receiving an A and a B, both potentially unboxed. */
  abstract class K2[-A,-B] { def apply(u: U, a: A, u2: U, b: B): Unit }

  /** A continuation receiving an A, B, and C, all potentially unboxed. */
  abstract class K3[-A,-B,-C] { def apply(u: U, a: A, u2: U, b: B, u3: U, c: C): Unit }

  /**
   * Denotes functions `A -> B`. Unlike Scala's `A => B`, this function
   * can be passed unboxed input, and we can consume its output without
   * boxing.
   */
  abstract class F1[-A,+B] { self =>

    /**
     * Holy shit! A function from `A -> B` represented as a "continuation transformer".
     * The continuation which accepts a `B` value (potentially unboxed) is transformed
     * into a continuation which accepts an `A` value (potentially unboxed).
     *
     * The requirement that an `F1` be able to pass along an extra `X`, parametrically,
     * effectively adds products to the category.
     */
    def apply[X]: K2[B,X] => K2[A,X]

    /** Compose two `F1`s. */
    def map[C](f: F1[B,C]): F1[A,C] = new F1[A,C] {
      def apply[x] =
        kcx => self.apply(f.apply(kcx))
    }

    def andThen: K[B] => K[A] = kb => {
      val f = self.apply[AnyRef](kb.toK2)
      (u,a) => f(u,a,U0,null)
    }
  }

  /**
   * Denotes functions `(A,B) -> C`. Unlike Scala's `(A,B) => C`, this function
   * can be passed unboxed input, and we can consume its output without
   * boxing.
   */
  abstract class F2[-A,-B,+C] {

    def apply[X]: K2[C,X] => K3[A,B,X]

    final def andThen: K[C] => K2[A,B] =
      kc => { val kabx = apply(kc.toK2[AnyRef])
              (u,a,u2,b) => kabx(u,a,u2,b,U0,null) }
  }

  /**
   * Marker type with no instances. A `F[Unboxed[T]]` indicates that `F`
   * does not use the boxed portion of its representation and that there
   * exists a `U => T` for extracting a `T` from the unboxed portion of
   * its representation.
   */
  // todo: correct comment
  sealed abstract class Unboxed[U]

  trait IsUnboxed[T] {
    def fromScala(t: T): U
    def toScala(u: U): T
  }

  trait IsNumeric[T] extends IsUnboxed[T] {
    val zero: T
    def plus(a: T, b: T): T
    def minus(a: T, b: T): T
  }

  object IsUnboxed {
    implicit object doubleIsUnboxed {//extends IsNumeric[Double] {
      @inline final def fromScala(t: Double): U = U(java.lang.Double.doubleToRawLongBits(t))
      @inline final def toScala(u: U): Double = java.lang.Double.longBitsToDouble(u)
      @inline final val zero: Double = 0.0
      @inline final def plus(a: Double, b: Double): Double = a + b
      @inline final def minus(a: Double, b: Double): Double = a - b
    }
    implicit object boolIsUnboxed {//extends IsUnboxed[Boolean] {
      @inline final def fromScala(t: Boolean): U = if (t) U.True else U.False
      @inline final def toScala(u: U): Boolean = u == U.True
    }

    implicit object longIsUnboxed {//extends IsNumeric[Long] {
      @inline final def fromScala(t: Long): U = U(t)
      @inline final def toScala(u: U): Long = u.toLong
      @inline final val zero: Long = 0l
      @inline final def plus(a: Long, b: Long): Long = a + b
      @inline final def minus(a: Long, b: Long): Long = a - b
    }

    implicit object intIsUnboxed extends IsNumeric[Int] {
      @inline final def fromScala(t: Int): U = t.toLong
      @inline final def toScala(u: U): Int = u.toInt
      @inline final val zero: Int = 0
      @inline final def plus(a: Int, b: Int): Int = a + b
      @inline final def minus(a: Int, b: Int): Int = a - b
    }
  }

  object K {
    val noop: K[Any] = (_,_) => {}
  }

  /**
   * A continuation which invokes `t` whenver `cond` is nonzero on the
   * input, and which invokes `f` whenever `cond` is zero on the input.
   */
  def choose[A](cond: F1[A,Unboxed[Boolean]], t: K[A], f: K[A]): K[A] = {
    val ccond = cond[A](
      (u,_,u2,a) => if (IsUnboxed.boolIsUnboxed.toScala(u)) t(u2,a) else f(u2,a))
    (u,a) => ccond(u,a,u,a)
  }

//  object Ex1 {
//    abstract class K[-A] { def apply(u: U, a: A): Unit }
//    trait F1[A,B] { def apply(k: K[B]): K[A] } // try to impl choose if this the rep
//    def choose[A](cond: F1[A,Unboxed[Boolean]], t: K[A], f: K[A]): K[A] = {
//      val kb = new K[Unboxed[Boolean]] {
//        override def apply(u: U, a: Unboxed[Boolean]): Unit =
//          if (u != U0) t(u,a) else (f(u,a))
//      }
//      val ccond: K[A] = cond(kb)
//      (u,a) => ccond(u,a)
//    }
//  }

  /**
   * A continuation which acts as `segment1` until `cond` emits 0, then
   * acts as `segment2` forever thereafter.
   */
  def switchWhen0[A](cond: F1[A,Unboxed[Boolean]], segment1: K[A], segment2: K[A]): () => K[A] = () => {
    var switched = false
    val ccond = cond[A]((u,_,u2,a) =>
                          if (switched || !IsUnboxed.boolIsUnboxed.toScala(u)) {
                            switched = true
                            segment2(u2, a)
                          } else segment1(u2, a))
    (u,a) => ccond(u,a,u,a)
  }

  object F1 {
    /**
     * Convert a Scala `A => B` to an `F1[A,B]` that acts on boxed input and produces boxed output.
     * Named `B_B` since it takes one boxed input and produces boxed output.
     */
    def B_B[A,B](f: A => B): F1[A,B] = new F1[A,B] {
      def apply[x] = kbx => (u,a,u2,x) => kbx(U0, f(a), u2, x)
    }

    // todo: confirm `f` really operates on unboxed, or fix
    import java.util.function.{DoublePredicate, DoubleUnaryOperator, IntUnaryOperator}
    def I_I(f: IntUnaryOperator) = new F1[Unboxed[Int], Unboxed[Int]] {
      override def apply[X]: K2[Unboxed[Int], X] => K2[Unboxed[Int], X] =
        kout => (u,_,u2,x2) =>
          kout(
            IsUnboxed.intIsUnboxed.fromScala(
              f.applyAsInt(IsUnboxed.intIsUnboxed.toScala(u))
            ), null, u2, x2
          )
    }

    def L_L(f: LongUnaryOperator) = new F1[Unboxed[Long], Unboxed[Long]] {
      import IsUnboxed.longIsUnboxed.{fromScala, toScala}
      override def apply[X]: K2[Unboxed[Long], X] => K2[Unboxed[Long], X] =
        kout => (u,_,u2,x2) =>
          kout(fromScala(f.applyAsLong(toScala(u))), null, u2, x2)
    }

    def D_D(f: DoubleUnaryOperator) = new F1[Unboxed[Double], Unboxed[Double]] {
      import IsUnboxed.doubleIsUnboxed.{fromScala, toScala}
      def apply[X]: K2[Unboxed[Double], X] => K2[Unboxed[Double], X] =
        kout => (u,_,u2,x) =>
          kout(fromScala(f.applyAsDouble(toScala(u))), null, u2, x)
    }

    def D_B(f: DoublePredicate) = new F1[Unboxed[Double], Unboxed[Boolean]] {
      import IsUnboxed.boolIsUnboxed.fromScala
      import IsUnboxed.doubleIsUnboxed.toScala
      def apply[X]: K2[Unboxed[Boolean], X] => K2[Unboxed[Double], X] =
        kout => (u,_,u2,x) =>
          kout(fromScala(f.test(toScala(u))), null, u2, x)
    }

    def I_B(f: IntPredicate) = new F1[Unboxed[Int], Unboxed[Boolean]] {
      import IsUnboxed.intIsUnboxed.toScala
      import IsUnboxed.boolIsUnboxed.fromScala
      def apply[X]: K2[Unboxed[Boolean], X] => K2[Unboxed[Int], X] =
        kout => (u,_,u2,x) =>
          kout(fromScala(f.test(toScala(u))), null, u2, x)
    }

    def L_B(f: LongPredicate) = new F1[Unboxed[Long], Unboxed[Boolean]] {
      import IsUnboxed.longIsUnboxed.toScala
      import IsUnboxed.boolIsUnboxed.fromScala
      def apply[X]: K2[Unboxed[Boolean], X] => K2[Unboxed[Long], X] =
        kout => (u,_,u2,x) =>
          kout(fromScala(f.test(toScala(u))), null, u2, x)
    }

    // still doesn't specialize Function1 :(
//    def U_U[@specialized(scala.Int, scala.Long, scala.Double) A: IsUnboxed,
//            @specialized(scala.Boolean, scala.Int, scala.Long, scala.Double) B: IsUnboxed]
//            (f: A => B): F1[Unboxed[A], Unboxed[B]] =
//      new F1[Unboxed[A], Unboxed[B]] {
//        def apply[x]: K2[Unboxed[B], x] => K2[Unboxed[A], x] =
//          kout => (u, _, u2, x) =>
//            kout(IsUnboxed.fromScala(f(IsUnboxed.toScala[A](u))), null, u2, x)
//      }

    type U_U = UnboxedUnaryOperator
    abstract class UnboxedUnaryOperator { def apply(u: U): U }
    abstract class BooleanUnaryOperator { def apply(b: Boolean): Boolean }
  }

  object F2 {
    /**
     * Convert a Scala `(A,B) => C` to an `F2[A,B,C]` that acts on boxed input and produces boxed output.
     * Named `BB_B` since it takes two boxed input and produces boxed output.
     */
    def XX_X[A,B,C](f: (A,B) => C): F2[A,B,C] = new F2[A,B,C] {
      def apply[x] = kcx => (u,a,u2,b,u3,x) => kcx(U0, f(a,b), u3, x)
    }

    /**
     * An `F2[Unboxed[U],Unboxed[U],Unboxed[U]]` which works on unboxed input and produces unboxed output.
     * Named `UU_U` since it takes two unboxed input and produces unboxed output.
     */
    def UU_U(fn: UU_U): F2[Unboxed[U],Unboxed[U],Unboxed[U]] = new F2[Unboxed[U],Unboxed[U],Unboxed[U]] {
      def apply[x] = kux => (u,_,u2,_,u3,x) => kux(fn(u,u2),null,u3,x)
    }

    type UU_U = UnboxedBinaryOperator
    abstract class UnboxedBinaryOperator { def apply(u: U, u2: U): U }
    abstract class DoubleBinaryPredicate { def apply(u: Double, u2: Double): Boolean }
    abstract class LongBinaryPredicate { def apply(u: Long, u2: Long): Boolean }

    def II_I_val(fn: IntBinaryOperator): F2[Unboxed[Int], Unboxed[Int], Unboxed[Int]] = {
      val i = IsUnboxed.intIsUnboxed
      class II_I extends F2[Unboxed[Int], Unboxed[Int], Unboxed[Int]] {
        def apply[x] =
          kux =>
            (u,_,u2,_,u3,x) => {
              val s = i.toScala(u)//: @inline
              val s2 = i.toScala(u2)//: @inline
              val sr = fn.applyAsInt(s, s2)
              val ur = i.fromScala(sr)//: @inline
              kux(ur, null, u3, x)
            }
      }
      new II_I
    }

    def II_I_import(fn: IntBinaryOperator): F2[Unboxed[Int], Unboxed[Int], Unboxed[Int]] = {
      import IsUnboxed.intIsUnboxed.{toScala, fromScala}
      class II_I extends F2[Unboxed[Int], Unboxed[Int], Unboxed[Int]] {
        def apply[x] =
          kux =>
            (u,_,u2,_,u3,x) => {
              val s = toScala(u)//: @inline
              val s2 = toScala(u2)//: @inline
              val sr = fn.applyAsInt(s, s2)
              val ur = fromScala(sr)//: @inline
              kux(ur, null, u3, x)
            }
      }
      new II_I
    }

    def II_I_manually_inline(fn: IntBinaryOperator): F2[Unboxed[Int], Unboxed[Int], Unboxed[Int]] = {
      class II_I extends F2[Unboxed[Int], Unboxed[Int], Unboxed[Int]] {
        def apply[x] =
          kux =>
            (u,_,u2,_,u3,x) => {
              kux(fn.applyAsInt(u.toInt, u2.toInt).toLong, null, u3, x)
            }
      }
      new II_I
    }

    def LL_L(fn: LongBinaryOperator) = new F2[Unboxed[Long], Unboxed[Long], Unboxed[Long]] {
      import IsUnboxed.longIsUnboxed.{toScala,fromScala}
      def apply[x] =
        kux =>
          (u,_,u2,_,u3,x) =>
            kux(fromScala(fn.applyAsLong(toScala(u),toScala(u2))),null,u3,x)
    }
  }
}
