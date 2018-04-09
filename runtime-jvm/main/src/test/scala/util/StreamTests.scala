package org.unisonweb.util

import org.unisonweb.ABT.Name
import org.unisonweb.EasyTest._
import org.unisonweb.compilation2._
import org.unisonweb.{Lib2, UnisonToScala}
import org.unisonweb.compilation2.Value.Lambda
import Unboxed.F1._
import Unboxed.F2._

object StreamTests {
  val tests = suite("Stream")(
    test("take/drop") { implicit T =>
      equal(
        Stream.from(0).take(5).drop(3).sumInt,
        (0 until 5).drop(3).sum
      )
    },
    test("map") { implicit T =>
      equal(
        Stream.from(0).take(10000).map(I_I(_ + 1)).sumInt,
        (0 until 10000).map(_ + 1).sum
      )
    },
    test("filter") { implicit T =>
      equal(
        Stream.from(0).take(10000).filter(I_B(_ % 2 == 0)).sumInt,
        (0 until 10000).filter(_.toDouble % 2 == 0).sum
      )
    },
    test("takeWhile") { implicit T =>
      equal(
        Stream.from(0).take(100).takeWhile(I_B(_ < 50)).sumInt,
        (0 until 100).takeWhile(_ < 50).sum
      )
    },
    test("dropWhile") { implicit T =>
      equal(
        Stream.from(0).take(100).dropWhile(I_B(_ < 50)).sumInt,
        (0 until 100).dropWhile(_ < 50).sum
      )
    },
    test("zipWith") { implicit T =>
      val s1 = Stream.from(0)
      val s2 = scala.collection.immutable.Stream.from(0)
      equal(
        s1.zipWith(s1.drop(1))(II_I_val(_ * _)).take(100).sumInt,
        s2.zip(s2.drop(1)).map { case (a,b) => a * b }.take(100).sum
      )
    },
    test("toSequence") { implicit T =>
      equal(
        Stream.from(0).take(10000).toSequence { (u, _) => u },
        Sequence.apply(0 until 10000: _*).map(_.toDouble)
      )
    },
    test("foldLeft-scalaPlus") { implicit T =>
      val plus: Unboxed.F2[U, U, U] = Unboxed.F2.XX_X(_ + _)
      equal(
        Stream.from(0l).take(10000).box[U](identity)
          .foldLeft(U0, U0)(plus)((_,a) => a),
        (0 until 10000).sum.toDouble
      )
    },
    test("foldLeft-unisonPlus") { implicit T =>
      val plusU = UnisonToScala.toUnboxed2(Lib2.builtins(Name("+")) match { case Return(lam: Lambda) => lam })
      val env = (new Array[U](20), new Array[B](20), new StackPtr(0), Result())
      equal(
        Stream.from(0).take(10000).asInstanceOf[Stream[Param]] // todo: does this work because the nulls can be cast to Param?
                                    .foldLeft(U0, null:Param)(plusU(env))((u,_) => u),
        (0 until 10000).sum.toDouble
      )
    }
  )
}
