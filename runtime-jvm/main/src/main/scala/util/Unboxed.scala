package org.unisonweb.util

import java.util.function.{DoublePredicate, DoubleUnaryOperator, IntUnaryOperator}

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
  trait IsUnboxed[@specialized(scala.Unit, scala.Boolean, scala.Int, scala.Float, scala.Long, scala.Double) T] {
    def fromScala(t: T): U
    def toScala(u: U): T
  }
  object IsUnboxed {
    implicit val doubleIsUnboxed: IsUnboxed[Double] = new IsUnboxed[Double] {
      def fromScala(t: Double): U = t
      def toScala(u: U): Double = u
    }
    implicit val boolIsUnboxed: IsUnboxed[Boolean] = new IsUnboxed[Boolean] {
      def fromScala(t: Boolean): U = if (t) 1.0 else 0.0
      def toScala(u: U): Boolean = u != 0.0
    }
// todo: Long can't be safely represented as Double due to potential "signaling NaN" transformation
//    implicit val longIsUnboxed: IsUnboxed[Long] = new IsUnboxed[Long] {
//      override def fromScala(t: Long): U = java.lang.Double.longBitsToDouble(t)
//      override def toScala(u: U): Long = ???
//    }

    implicit val intIsUnboxed: IsUnboxed[Int] = new IsUnboxed[Int] {
      def fromScala(t: Int): U = java.lang.Double.longBitsToDouble(t)
      def toScala(u: U): Int = java.lang.Double.doubleToRawLongBits(u).toInt
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

//  trait _F1[A,B] { def apply(k: K[B]): K[A] } // try to impl choose if this the rep
//  def _choose[A](cond: _F1[A,Null], t: K[A], f: K[A]): K[A] = {
//    val ccond = cond[A]((u,a) => if (u != U0) t(u,a) else (f(u,a)))
//    (u,a) => ccond(u,a)
//  }

  /**
   * A continuation which acts as `segment1` until `cond` emits 0, then
   * acts as `segment2` forever thereafter.
   */
  def switchWhen0[A](cond: F1[A,Unboxed[Boolean]], segment1: K[A], segment2: K[A]): () => K[A] = () => {
    var switched = false
    val ccond = cond[A]((u,_,u2,a) => if (u == U0) { switched = true; segment1(u2,a) } else segment2(u2,a))
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
    def U_U(f: IntUnaryOperator) = new F1[Unboxed[Int], Unboxed[Int]] {
      override def apply[X]: K2[Unboxed[Int], X] => K2[Unboxed[Int], X] =
        kout => (u,x,u2,x2) =>
          kout(
            IsUnboxed.intIsUnboxed.fromScala(
              f.applyAsInt(IsUnboxed.intIsUnboxed.toScala(u))
            ), x, u2, x2
          )
    }

    def U_U(f: DoubleUnaryOperator) = new F1[Unboxed[Double], Unboxed[Double]] {
      def apply[X]: K2[Unboxed[Double], X] => K2[Unboxed[Double], X] =
        kout => (u,x,u2,x2) =>
          kout(
            IsUnboxed.doubleIsUnboxed.fromScala(
              f.applyAsDouble(IsUnboxed.doubleIsUnboxed.toScala(u))
            ), x, u2, x2
          )
    }

    def U_U(f: DoublePredicate) = new F1[Unboxed[Double], Unboxed[Boolean]] {
      def apply[X]: K2[Unboxed[Boolean], X] => K2[Unboxed[Double], X] =
        kout => (u,x,u2,x2) =>
          kout(
            IsUnboxed.boolIsUnboxed.fromScala(
              f.test(IsUnboxed.doubleIsUnboxed.toScala(u))
            ), x.asInstanceOf, u2, x2
          )
    }

//    def U_U[A,B](f: A => B)(implicit A: IsUnboxed[A], B: IsUnboxed[B]) =
//      new F1[Unboxed[A], Unboxed[B]] {
//        def apply[x] = kout => (u,x,u2,x2) =>
//          kout(
//            B.fromScala(f(A.toScala(u))), x.asInstanceOf,
//            u2, x2
//          )
//      }
  }

  object F2 {
    /**
     * Convert a Scala `(A,B) => C` to an `F2[A,B,C]` that acts on boxed input and produces boxed output.
     * Named `BB_B` since it takes two boxed input and produces boxed output.
     */
    def BB_B[A,B,C](f: (A,B) => C): F2[A,B,C] = new F2[A,B,C] {
      def apply[x] = kcx => (u,a,u2,b,u3,x) => kcx(U0, f(a,b), u3, x)
    }

    /**
     * An `F2[Unboxed[U],Unboxed[U],Unboxed[U]]` which works on unboxed input and produces unboxed output.
     * Named `UU_U` since it takes two unboxed input and produces unboxed output.
     */
    def UU_U(fn: UU_U): F2[Unboxed[U],Unboxed[U],Unboxed[U]] = new F2[Unboxed[U],Unboxed[U],Unboxed[U]] {
      def apply[x] = kux => (u,_,u2,_,u3,x) => kux(fn(u,u2),null,u3,x)
    }

    abstract class UU_U { def apply(u: U, u2: U): U }
  }
}
