package org.unisonweb.util

import org.unisonweb.ABT.Name
import org.unisonweb.EasyTest._
import org.unisonweb.compilation2._
import org.unisonweb.{Lib2, UnisonToScala}
import org.unisonweb.compilation2.Value.Lambda
import Unboxed.F1.U_U

object StreamTests {
  val tests = suite("Stream")(
    test("take/drop") { implicit T =>
      equal(
        Stream.from(0.0).take(10000).drop(30).sum,
        (0 until 10000).drop(30).sum.toDouble)
    },
    test("map") { implicit T =>
      equal(
        Stream.from(0.0).take(10000).map(U_U((_: Double) + 1)).sum,
        (0 until 10000).map(_ + 1).sum.toDouble
      )
    },
    test("filter") { implicit T =>
      equal(
        Stream.from(0.0).take(10000).filter(U_U((_ : Double) % 2 == 0)).sum,
        (0 until 10000).filter(_.toDouble % 2 == 0).sum.toDouble
      )
    },
    test("takeWhile") { implicit T =>
      equal(
        Stream.from(0.0).take(100).takeWhile(U_U((_:Double) < 50)).sum,
        (0 until 100).takeWhile(_ < 50).sum.toDouble
      )
    },
    test("dropWhile") { implicit T =>
      equal(
        Stream.from(0.0).take(100).dropWhile(U_U((_:Double) < 50)).sum,
        (0 until 100).dropWhile(_ < 50).sum.toDouble
      )
    },
    test("toSequence") { implicit T =>
      equal(
        Stream.from(0.0).take(10000).toSequence { (u, _) => u },
        Sequence.apply(0 until 10000: _*).map(_.toDouble)
      )
    },
    test("foldLeft-scalaPlus") { implicit T =>
      val plus: Unboxed.F2[U, U, U] = Unboxed.F2.BB_B(_ + _)
      equal(
        Stream.from(0.0).take(10000).box[U](identity)
          .foldLeft(U0, U0)(plus)((_,a) => a),
        (0 until 10000).sum.toDouble
      )
    },
    test("foldLeft-unisonPlus") { implicit T =>
      val plusU = UnisonToScala.toUnboxed2(Lib2.builtins(Name("+")) match { case Return(lam: Lambda) => lam })
      val env = (new Array[U](20), new Array[B](20), new StackPtr(0), Result())
      equal(
        Stream.from(0.0).take(10000).asInstanceOf[Stream[Param]] // todo: does this work because the nulls can be cast to Param?
                                    .foldLeft(U0, null:Param)(plusU(env))((u,_) => u),
        (0 until 10000).sum.toDouble
      )
    }
  )
}
