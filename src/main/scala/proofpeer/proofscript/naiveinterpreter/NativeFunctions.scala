package proofpeer.proofscript.naiveinterpreter

import proofpeer.proofscript.logic._

object NativeFunctions {

  type Result = Either[StateValue, String]
  type F = (State, StateValue) => Result

  def environment : Map[String, F] = 
    Map(
      "reflexive" -> reflexive,
      "transitive" -> transitive,
      "combine" -> combine,
      "normalize" -> normalize,
      "instantiate" -> instantiate,
      "modusponens" -> modusponens,
      "equivalence" -> equivalence,
      "abstract" -> abs
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

  private def normalize_(state : State, tm : StateValue) : Result = {
    tm match {
      case TermValue(tm) =>
        Left(TheoremValue(state.context.normalize(tm)))
      case _ => Right("Term value expected")
    }
  }

  val normalize = wrap(normalize_)

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

  def instantiate_(state : State, tm : StateValue) : Result = {
    val ctx = state.context
    tm match {
      case TupleValue(values) if !values.isEmpty =>
        values.head match {
          case TheoremValue(thm) =>
            var insts : List[Option[Term]] = List()
            for (arg <- values.tail) {
              arg match {
                case NilValue => insts = None :: insts
                case TermValue(tm) => insts = Some(tm) :: insts
                case _ => return Right("invalid argument to instantiate")
              }
            }
            Left(TheoremValue(ctx.instantiate(ctx.lift(thm), insts.reverse)))
          case _ => Right("first argument is expected to be a theorem")
        }
      case _ => Right("non-empty argument list expected")
    }
  }

  val instantiate = wrap(instantiate_)

  def modusponens_(state : State, theorems : StateValue) : Result = {
    val ctx = state.context
    theorems match {
      case TupleValue(tuple) if tuple.size >= 1 =>
        var thm : Theorem = null
        for (t <- tuple) {
          t match {
            case TheoremValue(t) =>
              if (thm == null) 
                thm = ctx.lift(t)
              else 
                thm = ctx.modusponens(ctx.lift(t), thm)
            case _ => 
              Right("all arguments to modusponens must be theorems")
          }  
        }
        Left(TheoremValue(thm))
      case _ => Right("non-empty vector of theorems expected")
    }    
  }

  val modusponens = wrap(modusponens_)

  def equivalence_(state : State, theorems : StateValue) : Result = {
    theorems match {
      case TupleValue(Vector(TheoremValue(a), TheoremValue(b))) =>
        val ctx = state.context
        Left(TheoremValue(ctx.equiv(ctx.lift(a), ctx.lift(b))))
      case _ => 
        Right("equivalence expects two theorems as arguments")
    }
  }

  val equivalence = wrap(equivalence_)

  def abs_(state : State, thm : StateValue) : Result = {
    thm match {
      case TheoremValue(thm) => Left(TheoremValue(state.context.abs(state.context.lift(thm))))
      case _ => Right("abstract expects a theorem as argument")
    }
  }

  val abs = wrap(abs_)

}