package org.unisonweb

import Term.{Term,Name}
import compilation.{CurrentRec, RecursiveVars, IsNotTail}

object compilation2 {

  type U = Double // unboxed values
  val U0: U = 0.0
  type B = Param // boxed values
  type R = Result

  val K = 4

  abstract class Computation(val decompile: Term) { self =>
    /*
     * Computations take a stack as an argument, represented
     * with a mix of regular parameters and arrays. We have
     * separate stacks for boxed and unboxed parameters.
     *
     * Layout of parameters:
     *   x0 is the top of the stack, x1 is below it, we call these "registers".
     *   x0b is the top boxed stack element, x1b is below it, etc.
     *   stackB(top) has 4 elements above it in the stack
     *   stackB(top - 1) has 5 elements above it in the stack
     *   stackB(0) is the bottom of the stack
     *   stackU is the same, but for unboxed values.
     *
     * To push onto the stack, x0 is copied to x1, x1 is copied to
     * x2, and x3 is "spilled" into the array portion of the stack.
     * As an important optimization, if x3 is no longer being referenced
     * by the subsequent computation, this spilling can be elided.
     */
    def apply(rec: Lambda, x0: U, x1: U, x2: U, x3: U, stackU: Array[U],
                           x0b: B, x1b: B, x2b: B, x3b: B, stackB: Array[B],
                           top: Int,
                           r: R): U

    def incrementTop: Computation = new Computation(null) {
      def apply(rec: Lambda, x0: U, x1: U, x2: U, x3: U, stackU: Array[U],
                             x0b: B, x1b: B, x2b: B, x3b: B, stackB: Array[B],
                             top: Int,
                             r: R): U =
        self(rec, x0, x1, x2, x3, stackU, x0b, x1b, x2b, x3b, stackB, top + 1, r)
    }

    /** Push `this` onto the stack, then call into `body`. */
    def push1(env: Vector[Name], freeVars: Set[Name])(binding: Computation): Computation =
      new Computation(null) { // okay if null since a `let` will never be decompiled
        val pushU = push1U(env, freeVars)
        val pushB = push1B(env, freeVars)
        def apply(rec: Lambda, x0: U, x1: U, x2: U, x3: U, stackU: Array[U],
                               x0b: B, x1b: B, x2b: B, x3b: B, stackB: Array[B],
                               top: Int,
                               r: R): U = {
          val vbinding = eval(binding, rec, x0, x1, x2, x3, stackU, x0b, x1b, x2b, x3b, stackB, top, r)
          val vbindingb = r.boxed
          self(rec, vbinding,  x0,  x1,  x2,  pushU(stackU, top, x3),
                    vbindingb, x0b, x1b, x2b, pushB(stackB, top, x3b),
                    top, r)
        }
      }

    /**
     * Given a continuation, `body`, sets the result of this computation to the `index`
     * stack position, before calling into `body`. 0 refers to top of the stack (register 0),
     * 1 refers to register below that, and so on.
     */
    def bindTo(index: Int)(body: Computation): Computation = {
      val bodyIsSelf = body.isInstanceOf[Self]
      index match {
        case 0 => new Computation(null) {
          def apply(rec: Lambda, x0: U, x1: U, x2: U, x3: U, stackU: Array[U],
                                 x0b: B, x1b: B, x2b: B, x3b: B, stackB: Array[B],
                                 top: Int,
                                 r: R): U = {
            val vself = eval(self, rec, x0, x1, x2, x3, stackU, x0b, x1b, x2b, x3b, stackB, top, r)
            val vselfb = r.boxed
            if (bodyIsSelf)
              rec.body(rec, vself,  x1,  x2,  x3, stackU, vselfb, x1b, x2b, x3b, stackB, top, r)
            else
              body(rec, vself,  x1,  x2,  x3, stackU, vselfb, x1b, x2b, x3b, stackB, top, r)
          }
        }
        case 1 => new Computation(null) {
          def apply(rec: Lambda, x0: U, x1: U, x2: U, x3: U, stackU: Array[U],
                                 x0b: B, x1b: B, x2b: B, x3b: B, stackB: Array[B],
                                 top: Int,
                                 r: R): U = {
            val vself = eval(self, rec, x0, x1, x2, x3, stackU, x0b, x1b, x2b, x3b, stackB, top, r)
            val vselfb = r.boxed
            if (bodyIsSelf)
              rec.body(rec, x0, vself, x2, x3, stackU, x0b, vselfb, x2b, x3b, stackB, top, r)
            else
              body(rec, x0, vself, x2, x3, stackU, x0b, vselfb, x2b, x3b, stackB, top, r)
          }
        }
        case 2 => new Computation(null) {
          def apply(rec: Lambda, x0: U, x1: U, x2: U, x3: U, stackU: Array[U],
                                 x0b: B, x1b: B, x2b: B, x3b: B, stackB: Array[B],
                                 top: Int,
                                 r: R): U = {
            val vself = eval(self, rec, x0, x1, x2, x3, stackU, x0b, x1b, x2b, x3b, stackB, top, r)
            val vselfb = r.boxed
            if (bodyIsSelf)
              rec.body(rec, x0,  x1,  vself,  x3, stackU, x0b, x1b, vselfb, x3b, stackB, top, r)
            else
              body(rec, x0,  x1,  vself,  x3, stackU, x0b, x1b, vselfb, x3b, stackB, top, r)
          }
        }
        case 3 => new Computation(null) {
          def apply(rec: Lambda, x0: U, x1: U, x2: U, x3: U, stackU: Array[U],
                                 x0b: B, x1b: B, x2b: B, x3b: B, stackB: Array[B],
                                 top: Int,
                                 r: R): U = {
            val vself = eval(self, rec, x0, x1, x2, x3, stackU, x0b, x1b, x2b, x3b, stackB, top, r)
            val vselfb = r.boxed
            if (bodyIsSelf)
              rec.body(rec, x0,  x1,  x3,  vself,  stackU, x0b, x1b, x3b, vselfb, stackB, top, r)
            else
              body(rec, x0,  x1,  x3,  vself,  stackU, x0b, x1b, x3b, vselfb, stackB, top, r)
          }
        }
        case index => new Computation(null) {
          val m = index - K
          def apply(rec: Lambda, x0: U, x1: U, x2: U, x3: U, stackU: Array[U],
                                 x0b: B, x1b: B, x2b: B, x3b: B, stackB: Array[B],
                                 top: Int,
                                 r: R): U = {
            val vself = eval(self, rec, x0, x1, x2, x3, stackU, x0b, x1b, x2b, x3b, stackB, top, r)
            val vselfb = r.boxed
            stackU(top + m) = vself
            stackB(top + m) = vselfb
            if (bodyIsSelf)
              rec.body(rec, x0,  x1,  x3,  vself,  stackU, x0b, x1b, x3b, vselfb, stackB, top, r)
            else
              body(rec, x0,  x1,  x3,  vself,  stackU, x0b, x1b, x3b, vselfb, stackB, top, r)
          }
        }
      }
    }

    def dynamicCall(args: Array[Computation]): Computation = new Computation(null) {
      def apply(rec: Lambda, x0: U, x1: U, x2: U, x3: U, stackU: Array[U],
                             x0b: B, x1b: B, x2b: B, x3b: B, stackB: Array[B],
                             top: Int,
                             r: R): U = {
        ???
        // basically, evaluate this, then check
      }
    }
  }

  object Computation {

    /** Push `arg` onto the stack, then evaluate body. */
    def call1(name: Name, arg: Computation)(body: Computation): Computation =
      body.push1(Vector(name), Set.empty)(arg)

    /** Push `arg` onto the stack, then evaluate body. */
    def call(args: List[(Name,Computation)])(body: Computation): Computation = args match {
      case Nil => body
      case (name, arg) :: args => call1(name, arg)(call(args)(body))
    }
  }

  case class Self(name: Name) extends Computation(Term.Var(name)) {
    def apply(rec: Lambda, x0: U, x1: U, x2: U, x3: U, stackU: Array[U],
                           x0b: B, x1b: B, x2b: B, x3b: B, stackB: Array[B],
              top: Int, r: R): U = { r.boxed = rec; U0 }
  }

  case class Return(v: Value) extends Computation(v.decompile) {
    val c = v match {
      case Num(n) =>
        compile(_ => ???)(Term.Num(n), Vector.empty,
                          CurrentRec.none, RecursiveVars.empty, false)
      case f : Lambda => new Computation(f.decompile) {
        def apply(rec: Lambda, x0: U, x1: U, x2: U, x3: U, stackU: Array[U],
                               x0b: B, x1b: B, x2b: B, x3b: B, stackB: Array[B],
                               top: Int,
                               r: R): U = { r.boxed = f; U0 }
      }
    }
    def apply(rec: Lambda, x0: U, x1: U, x2: U, x3: U, stackU: Array[U],
                           x0b: B, x1b: B, x2b: B, x3b: B, stackB: Array[B],
                           top: Int,
                           r: R): U =
      c(rec, x0, x1, x2, x3, stackU, x0b, x1b, x2b, x3b, stackB, top, r)
  }

  abstract class Push1U { def apply(arr: Array[U], top: Int, u: U): Array[U] }
  abstract class Push1B { def apply(arr: Array[B], top: Int, u: B): Array[B] }

  def push1U(env: Vector[Name], freeVars: Set[Name]): Push1U =
    // if x3 is garbage or we no longer care about it, avoid setting
    if (env.length < K || !freeVars.contains(env(K - 1))) new Push1U {
      def apply(arr: Array[U], top: Int, u: U) = arr
    }
    else new Push1U {
      val i = env.length - K
      def apply(arr: Array[U], top: Int, u: U) = { arr(top + i) = u; arr }
    }

  def push1B(env: Vector[Name], freeVars: Set[Name]): Push1B =
    // if x3 is garbage or we no longer care about it, avoid setting
    if (env.length < K || !freeVars.contains(env(K - 1))) new Push1B {
      def apply(arr: Array[B], top: Int, b: B) = arr
    }
    else new Push1B {
      val i = env.length - K
      def apply(arr: Array[B], top: Int, b: B) = { arr(top + i) = b; arr }
    }

  def compile(builtins: Name => Computation)(
    e: Term, env: Vector[Name], currentRec: CurrentRec, recVars: RecursiveVars,
    isTail: Boolean): Computation =
    e match {
      case Term.Num(n) => new Computation(e) {
        def apply(rec: Lambda, x1: U, x2: U, x3: U, x4: U, stackU: Array[U],
                               x1b: B, x2b: B, x3b: B, x4b: B, stackB: Array[B],
                               top: Int,
                               r: R): U = { r.boxed = null; n } // todo - think through whether can elide
      }
      case Term.Builtin(name) => builtins(name)
      case Term.Compiled2(param) => Return(param.toValue)
      case Term.Self(name) => new Self(name)
      case Term.Var(name) => compileVar(e, name, env, currentRec)
      case Term.Let1(name, b, body) =>
        val cb = compile(builtins)(b, env, currentRec, recVars, isTail = false)
        val cbody = compile(builtins)(body, name +: env, currentRec.shadow(name),
                            recVars - name, isTail)
        cbody.push1(env, Term.freeVars(body))(cb)
      case Term.Lam(names, body) =>
        val freeVars = Term.freeVars(e)
        // The lambda is closed
        if (freeVars.isEmpty) {
          val cbody = compile(builtins)(body, names.reverse.toVector,
                              CurrentRec.none, RecursiveVars.empty, isTail = true)
          Return(Lambda(names.length, cbody, e))
        }
        else {
          val compiledFrees: Map[Name,Computation] =
            (freeVars -- recVars.get).view.map {
              name => (name, compileVar(Term.Var(name), name, env, currentRec))
            }.toMap
          val compiledFreeRecs: Map[Name,ParamLookup] =
            freeVars.intersect(recVars.get).view.map {
              name => (name, compileRef(Term.Var(name), name, env, currentRec))
            }.toMap
          new Computation(e) {
            def apply(rec: Lambda, x0: U, x1: U, x2: U, x3: U, stackU: Array[U],
                                   x0b: B, x1b: B, x2b: B, x3b: B, stackB: Array[B],
                                   top: Int,
                                   r: R): U = {
              val evaledFreeVars: Map[Name, Term] = compiledFrees.mapValues {
                c =>
                  val evaluatedVar =
                    c(rec, x0, x1, x2, x3, stackU, x0b, x1b, x2b, x3b, stackB, top, r)
                  val value = Value(evaluatedVar, r.boxed)
                  Term.Compiled2(value)
              }

              val evaledRecVars: Map[Name, Term] = compiledFreeRecs.transform {
                (name, lookup) =>
                  if (currentRec.contains(name)) Term.Self(name)
                  else {
                    val evaluatedVar = lookup(rec, x0b, x1b, x2b, x3b, stackB, top)
                    if (evaluatedVar eq null) sys.error(name + " refers to null stack slot.")
                    require (evaluatedVar.isRef)
                    Term.Compiled2(evaluatedVar)
                  }
              }

              val lam2 = Term.Lam(names: _*)(
                body = ABT.substs(evaledFreeVars ++ evaledRecVars)(body)
              )
              assert(Term.freeVars(lam2).isEmpty)
              r.boxed = compile(builtins)(
                lam2, Vector(), CurrentRec.none, RecursiveVars.empty, false
              ) match {
                case Return(v) => v
                case _ => sys.error("compiling a lambda with no free vars should always produce a Return")
              }
              U0
            }
          }
        }

      case Term.Apply(Term.Apply(fn, args), args2) => // converts nested applies to a single apply
        compile(builtins)(Term.Apply(fn, (args ++ args2):_*), env, currentRec, recVars, isTail)

      case Term.Apply(fn, Nil) => sys.error("the parser isn't supposed to produce this")

      case Term.Apply(fn, args) =>
        val compiledArgs: List[Computation] =
          args.view.map(arg => compile(builtins)(arg, env, currentRec, recVars, IsNotTail)).toList

        val cfn: Computation = compile(builtins)(fn, env, currentRec, recVars, IsNotTail)

        def saturatedCall(body: Computation, n: Int) =
          compiledArgs.take(n)
            .reverse.zipWithIndex // 0th arg becomes bottom of stack
            .foldRight(body) { (argi, body) => argi._1.bindTo(argi._2)(body) }
            // .makeTailCall(isTail)

        cfn match {
          // static call, fully saturated
          case Return(lam @ Lambda(arity, body, _)) if arity == args.length =>
            saturatedCall(body, args.length)

          // self call, fully saturated
          case Self(v) if currentRec.contains(v, args.length) =>
            saturatedCall(cfn, args.length)

          // static call, overapplied
          case Return(lam @ Lambda(arity, body, decompiled)) if arity > args.length =>
            saturatedCall(cfn, arity).dynamicCall(compiledArgs drop arity toArray)

          // static call, underapplied
          case Return(lam @ Lambda(arity, body, decompiled)) if arity < args.length => ???

          // dynamic call
          case _ => cfn.dynamicCall(compiledArgs toArray)
        }

      case Term.LetRec(List((name, binding)), body) =>
        // 1. compile the body
        // 2. compile all of the bindings into an Array[Computation]
        // 3. construct the Computation

        val cbinding = binding match {
          case l@Term.Lam(argNames, bindingBody) =>
            val newCurrentRec = CurrentRec(name, argNames.size).shadow(argNames)
            if (hasTailRecursiveCall(newCurrentRec, bindingBody))
              // construct the wrapper lambda to catch the SelfTailCalls
              ???
            else // compile the lambda as Normal
              compile(builtins)(l, name +: env, newCurrentRec, recVars + name, IsNotTail)
          case b => // not a lambda, not recursive, could have been a Let1
            compile(builtins)(Term.Let1(name, binding)(body), env, currentRec, recVars, IsNotTail)
        }

        val cbody = compile(builtins)(body, name +: env, currentRec.shadow(name), recVars + name, isTail)

        val pushU = push1U(env, Term.freeVars(body) ++ Term.freeVars(binding))
        val pushB = push1B(env, Term.freeVars(body) ++ Term.freeVars(binding))

        // this
        new Computation(e) {
          override def apply(rec: Lambda, x0: U, x1: U, x2: U, x3: U, stackU: Array[U],
                                          x0b: B, x1b: B, x2b: B, x3b: B, stackB: Array[B],
                                          top: Int, r: R): U = {
            lazy val evaledBinding: Ref =
              // eval(cbinding, rec, U0,            x0, x1, x2, pushU(stackU, x3),
              //                     evaledBinding, x0b, x1b, x2b, pushB(stackB, x3b))
              // this might be the general case; for let rec 1, probably can do something simpler?
              // todo: later, can we avoid putting this onto the stack at all? maybe by editing environment
              new Ref(name, () => Value(eval(cbinding, rec, x0, x1, x2, x3, stackU,
                                                            x0b, x1b, x2b, x3b, stackB, top, r), r.boxed))

            eval(cbody, rec, U0,            x0, x1, x2, pushU(stackU, top, x3),
                             evaledBinding, x0b, x1b, x2b, pushB(stackB, top, x3b), top, r)

          }
        }

      case Term.LetRec(bindings, body) => ???
    }

  def hasTailRecursiveCall(rec: CurrentRec, term: Term): Boolean = ???

  @inline
  def eval(c: Computation, rec: Lambda,
           x0: U,  x1: U,  x2: U,  x3: U,  stackU: Array[U],
           x0b: B, x1b: B, x2b: B, x3b: B, stackB: Array[B],
           top: Int,
           r: R): U =
    try c(rec, x0, x1, x2, x3, stackU, x0b, x1b, x2b, x3b, stackB, top, r)
    catch { case TailCall => loop(r, top) }

  def loop(r: R, top: Int): U = {
    while (true) {
      try return r.tailCall.body(r.tailCall, r.x0, r.x1, r.x2, r.x3, r.stackU,
                                 r.x0b, r.x1b, r.x2b, r.x3b, r.stackB, top, r)
      catch { case TailCall => }
    }
    U0
  }

  abstract class Param {
    def toValue: Value
    def isRef: Boolean = false
  }

  class Ref(val name: Name, computeValue: () => Value) extends Param {
    lazy val value = computeValue()
    def toValue = value
    override def isRef = true
  }

  abstract class Value extends Param {
    def toValue = this
    def decompile: Term
  }
  object Value {
    def apply(u: U, b: Value): Value = if (b eq null) Num(u) else b
  }
  case class Num(n: U) extends Value {
    def decompile = Term.Num(n)
  }
  case class Lambda(arity: Int, body: Computation, decompile: Term) extends Value {
    def maxBinderDepth = Term.maxBinderDepth(decompile)
  }

  case object SelfCall extends Throwable { override def fillInStackTrace = this }
  case object TailCall extends Throwable { override def fillInStackTrace = this }

  case class Result(var boxed: Value,
                    var tailCall: Lambda,
                    // Tail call arguments
                    var x0: U, var x1: U, var x2: U, var x3: U, var stackU: Array[U],
                    var x0b: B, var x1b: B, var x2b: B, var x3b: B, var stackB: Array[B])

  // todo - could pass info here about the type of variable, whether it is boxed or
  // unboxed, and optimize for this case
  def compileVar(e: Term, name: Name, env: Vector[Name], currentRec: CurrentRec): Computation =
    if (currentRec.contains(name)) new Computation(e) {
      def apply(rec: Lambda, x0: U, x1: U, x2: U, x3: U, stackU: Array[U],
                             x0b: B, x1b: B, x2b: B, x3b: B, stackB: Array[B],
                             top: Int,
                             r: R): U = { r.boxed = rec; U0 }

    }
    else env.indexOf(name) match {
      case -1 => sys.error("unbound name: " + name)
      case 0 => new Computation(e) {
        def apply(rec: Lambda, x0: U, x1: U, x2: U, x3: U, stackU: Array[U],
                               x0b: B, x1b: B, x2b: B, x3b: B, stackB: Array[B],
                               top: Int,
                               r: R): U = { if (x0b ne null) r.boxed = x0b.toValue; x0 }

      }
      case 1 => new Computation(e) {
        def apply(rec: Lambda, x0: U, x1: U, x2: U, x3: U, stackU: Array[U],
                               x0b: B, x1b: B, x2b: B, x3b: B, stackB: Array[B],
                               top: Int,
                               r: R): U = { if (x1b ne null) r.boxed = x1b.toValue; x1 }

      }
      case 2 => new Computation(e) {
        def apply(rec: Lambda, x0: U, x1: U, x2: U, x3: U, stackU: Array[U],
                               x0b: B, x1b: B, x2b: B, x3b: B, stackB: Array[B],
                               top: Int,
                               r: R): U = { if (x2b ne null) r.boxed = x2b.toValue; x2 }

      }
      case 3 => new Computation(e) {
        def apply(rec: Lambda, x0: U, x1: U, x2: U, x3: U, stackU: Array[U],
                               x0b: B, x1b: B, x2b: B, x3b: B, stackB: Array[B],
                               top: Int,
                               r: R): U = { if (x3b ne null) r.boxed = x3b.toValue; x3 }

      }
      case n => val m = n - K; new Computation(e) {
        def apply(rec: Lambda, x0: U, x1: U, x2: U, x3: U, stackU: Array[U],
                               x0b: B, x1b: B, x2b: B, x3b: B, stackB: Array[B],
                               top: Int,
                               r: R): U = {
          if (stackB(m) ne null) r.boxed = stackB(top + m).toValue
          stackU(top + m)
        }
      }
    }

  def compileRef(e: Term, name: Name, env: Vector[Name], currentRec: CurrentRec): ParamLookup = {
    if (currentRec.contains(name)) new ParamLookup {
      def apply(rec: Lambda, x0b: B, x1b: B, x2b: B, x3b: B, stackB: Array[B], top: Int) =
        rec
    }
    else env.indexOf(name) match {
      case -1 => sys.error("unbound name: " + name)
      case 0 => new ParamLookup { def apply(rec: Lambda, x0b: B, x1b: B, x2b: B, x3b: B, stackB: Array[B], top: Int) = x0b }
      case 1 => new ParamLookup { def apply(rec: Lambda, x0b: B, x1b: B, x2b: B, x3b: B, stackB: Array[B], top: Int) = x1b }
      case 2 => new ParamLookup { def apply(rec: Lambda, x0b: B, x1b: B, x2b: B, x3b: B, stackB: Array[B], top: Int) = x2b }
      case 3 => new ParamLookup { def apply(rec: Lambda, x0b: B, x1b: B, x2b: B, x3b: B, stackB: Array[B], top: Int) = x3b }
      case n => val m = n - K; new ParamLookup {
        def apply(rec: Lambda, x0b: B, x1b: B, x2b: B, x3b: B, stackB: Array[B], top: Int) =
          stackB(top + m)
      }
    }
  }

  abstract class ParamLookup {
    def apply(rec: Lambda, x0b: B, x1b: B, x2b: B, x3b: B, stackB: Array[B], top: Int): B
  }
}
