package proofpeer.proofscript.naiveinterpreter

import proofpeer.proofscript.logic._

object NativeFunctions {

  type Result = Either[StateValue, String]
  type F = (State, StateValue) => Result

  private def wrap(f : F) : F = {
    def g(state : State, value : StateValue) : Result = {
      try {
        f(state, value)
      } catch {
        case ex: Utils.KernelException => Right(ex.reason)
      }
    }
    g
  }

  private def reflexive_(state : State, tm : StateValue) : Result = {
    tm match {
      case TermValue(tm) => 
        Left(TheoremValue(state.context.reflexive(tm)))
      case _ => Right("Term value expected")
    }
  }

  val reflexive = wrap(reflexive_)

  private def transitive_(state : State, tm : StateValue) : Result = {
    val ctx = state.context
    tm match {
      case TupleValue(tuple) if tuple.size >= 2 =>
        var thm : Theorem = null
        for (t <- tuple) {
          t match {
            case TheoremValue(t) =>
              if (thm == null) 
                thm = ctx.lift(t)
              else 
                thm = ctx.transitive(thm, ctx.lift(t))
            case _ => 
              Right("all arguments to transitive must be theorems")
          }  
        }
        Left(TheoremValue(thm))
      case _ => Right("at least two theorems expected")
    }
  }

  val transitive = wrap(transitive_)

}