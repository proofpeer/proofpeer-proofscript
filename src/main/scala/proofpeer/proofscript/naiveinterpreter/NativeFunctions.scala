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


}