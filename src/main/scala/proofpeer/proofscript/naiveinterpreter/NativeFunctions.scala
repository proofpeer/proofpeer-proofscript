package proofpeer.proofscript.naiveinterpreter

import proofpeer.proofscript.logic._

object NativeFunctions {

  type Result = Either[StateValue, String]
  type F = (State, StateValue) => Result

  val environment : Map[String, F] = 
    Map(
      "reflexive" -> reflexive,
      "transitive" -> transitive,
      "combine" -> combine
    )

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
      case TupleValue(tuple) if tuple.size >= 1 =>
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
      case _ => Right("non-empty vector of theorems expected")
    }
  }

  val transitive = wrap(transitive_)

  private def combine_(state : State, tm : StateValue) : Result = {
    val ctx = state.context
    tm match {
      case TupleValue(tuple) if tuple.size >= 1 =>
        var thm : Theorem = null
        for (t <- tuple) {
          t match {
            case TheoremValue(t) =>
              if (thm == null) 
                thm = ctx.lift(t)
              else 
                thm = ctx.comb(thm, ctx.lift(t))
            case _ => 
              Right("all arguments to combine must be theorems")
          }  
        }
        Left(TheoremValue(thm))
      case _ => Right("non-empty vector of theorems expected")
    }    
  }

  val combine = wrap(combine_)

}