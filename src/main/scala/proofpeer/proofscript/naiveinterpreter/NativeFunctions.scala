package proofpeer.proofscript.naiveinterpreter

import proofpeer.proofscript.logic._

object NativeFunctions {

  type Result = Either[StateValue, String]
  type F = (Eval, State, StateValue) => Result

  def environment : Map[String, F] = 
    Map(
      "reflexive" -> wrap(reflexive),
      "transitive" -> wrap(transitive),
      "combine" -> wrap(combine),
      "normalize" -> wrap(normalize),
      "instantiate" -> wrap(instantiate),
      "modusponens" -> wrap(modusponens),
      "equivalence" -> wrap(equivalence),
      "abstract" -> wrap(abs),
      "term" -> wrap(convert_to_term),
      "string" -> wrap(convert_to_string),
      "size" -> wrap(compute_size),
      "fresh" -> wrap(fresh),
      "destcomb" -> wrap(destcomb),
      "destabs" -> wrap(destabs)
    )

  private def wrap(f : F) : F = {
    def g(eval : Eval, state : State, value : StateValue) : Result = {
      try {
        f(eval, state, value)
      } catch {
        case ex: Utils.KernelException => Right(ex.reason)
      }
    }
    g
  }

  private def reflexive(eval : Eval, state : State, tm : StateValue) : Result = {
    tm match {
      case TermValue(tm) => 
        Left(TheoremValue(state.context.reflexive(tm)))
      case _ => Right("Term value expected")
    }
  }  

  private def normalize(eval : Eval, state : State, tm : StateValue) : Result = {
    tm match {
      case TermValue(tm) =>
        Left(TheoremValue(state.context.normalize(tm)))
      case _ => Right("Term value expected")
    }
  }

  private def transitive(eval : Eval, state : State, tm : StateValue) : Result = {
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

  private def combine(eval : Eval, state : State, tm : StateValue) : Result = {
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

  private def instantiate(eval : Eval, state : State, tm : StateValue) : Result = {
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

  private def modusponens(eval : Eval, state : State, theorems : StateValue) : Result = {
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
                thm = ctx.modusponens(thm, ctx.lift(t))
            case _ => 
              Right("all arguments to modusponens must be theorems")
          }  
        }
        Left(TheoremValue(thm))
      case _ => Right("non-empty vector of theorems expected")
    }    
  }

  private def equivalence(eval : Eval, state : State, theorems : StateValue) : Result = {
    theorems match {
      case TupleValue(Vector(TheoremValue(a), TheoremValue(b))) =>
        val ctx = state.context
        Left(TheoremValue(ctx.equiv(ctx.lift(a), ctx.lift(b))))
      case _ => 
        Right("equivalence expects two theorems as arguments")
    }
  }

  private def abs(eval : Eval, state : State, thm : StateValue) : Result = {
    thm match {
      case TheoremValue(thm) => Left(TheoremValue(state.context.abs(state.context.lift(thm))))
      case _ => Right("abstract expects a theorem as argument")
    }
  }

  private def convert_to_term(eval : Eval, state : State, value : StateValue) : Result = {
    value match {
      case _ : TermValue => Left(value)
      case TheoremValue(thm) => Left(TermValue(state.context.lift(thm).proposition))
      case s : StringValue => Left(TermValue(Syntax.parseTerm(eval.aliases, 
        eval.logicNameresolution, state.context, s.toString)))
      case _ => Right("cannot convert to term: " + eval.display(state, value))
    }
  }

  private def stringValue(s : String) : StringValue = {
    StringValue(proofpeer.general.StringUtils.codePoints(s))
  }

  private def convert_to_string(eval : Eval, state : State, value : StateValue) : Result = {
    value match {
      case _ : StringValue => Left(value)
      case TermValue(t) => Left(stringValue(Syntax.checkprintTerm(eval.aliases, 
        eval.logicNameresolution, state.context, t)))
      case TheoremValue(thm) => Left(stringValue(Syntax.checkprintTerm(eval.aliases, 
        eval.logicNameresolution, state.context, state.context.lift(thm).proposition)))
      case IntValue(i) => Left(stringValue("" + i))
      case _ => Right("cannot convert to string: " + eval.display(state, value))
    }
  }

  private def compute_size(eval : Eval, state : State, value : StateValue) : Result = {
    value match {
      case StringValue(s) => Left(IntValue(s.size))
      case TupleValue(v) => Left(IntValue(v.size))
      case _ => Right("size is not defined for: " + eval.display(state, value))
    }  
  }

  private def fresh(eval : Eval, state : State, value : StateValue) : Result = {
    value match {
      case s : StringValue =>
        Syntax.parsePreterm(s.toString) match {
          case Some(Preterm.PTmName(Name(None, name), _)) =>
            val freshName = state.context.mkFresh(name)
            Left(stringValue(freshName.toString))
          case _ => Right("constant name without namespace or index required")       
        }
      case _ => Right("fresh expects a string as its argument")
    }
  }

  private def destcomb(eval : Eval, state : State, tm : StateValue) : Result = {    
    val ctx = state.context
    tm match {
      case TermValue(Term.Comb(f, g)) => Left(TupleValue(Vector(TermValue(f), TermValue(g))))
      case TermValue(f) => Left(NilValue)
      case _ => Right("term expected")
    }    
  }

  private def destabs(eval : Eval, state : State, tm : StateValue) : Result = {    
    val ctx = state.context
    tm match {
      case TermValue(t) => 
        ctx.destAbs(t) match {
          case None => Left(NilValue)
          case Some((context, x, body)) =>
            Left(TupleValue(Vector(ContextValue(context), TermValue(x), TermValue(body))))
        }
      case _ => Right("term expected")
    }    
  }


}