package proofpeer.proofscript.logic

import proofpeer.general.continuation._

sealed trait Domain
case class TypeDomain(ty : Pretype) extends Domain
case class SetDomain(tm : Preterm) extends Domain
case class Binding(name : IndexedName, domain : Option[Domain])

sealed trait Preterm {
	def typeOf : Pretype
}

object Preterm {

  import Utils.Integer
  import Pretype.PTyQuote
 
  case class PTmTyping(tm : Preterm, typeOf : Pretype) extends Preterm
  case class PTmName(name : Name, typeOf : Pretype) extends Preterm
  case class PTmAbs(x : IndexedName, ty : Pretype, body : Preterm, body_ty : Pretype) extends Preterm {
  	def typeOf = Pretype.PTyFun(ty, body_ty)
  }
  case class PTmComb(f : Preterm, x : Preterm, higherorder : Option[Boolean], typeOf : Pretype) extends Preterm
  /** quoted is going to be either ParseTree.Expr or ParseTree.Pattern */
  case class PTmQuote(quoted : Any, typeOf : Pretype) extends Preterm 
  case class PTmTerm(tm : Term, ty : Type) extends Preterm {
    lazy val typeOf : Pretype = Pretype.translate(ty)
  }
  case class PTmError(reason : String) extends Preterm {
  	def typeOf = Pretype.PTyAny
  }

  def pTmEquals(left : Preterm, right : Preterm) : Preterm = {
  	pTmBinaryOp(Kernel.equals, left, right)
  }
  
  def pTmAbsOverUniverse(x : IndexedName, body : Preterm) : Preterm = {
    PTmAbs(x, Pretype.PTyUniverse, body, Pretype.PTyAny)
  }

  def pTmAbs(binding : Binding, body : Preterm) : Preterm = {
    binding match {
      case Binding(x, None) => 
        PTmAbs(x, Pretype.PTyAny, body, Pretype.PTyAny)
      case Binding(x, Some(TypeDomain(ty))) =>
        PTmAbs(x, ty, body, Pretype.PTyAny)
      case Binding(x, Some(SetDomain(tm))) =>
        pTmBinaryOp(Kernel.fun, tm, pTmAbsOverUniverse(x, body))
    }
  }

  def pTmAbs(xs : List[Binding], body : Preterm) : Preterm = {
    var p = body
    for (x <- xs) {
      p = pTmAbs(x, p)
    }
    p
  }

  def pTmForall(binding : Binding, body : Preterm) : Preterm = {
    binding match {
      case Binding(x, Some(SetDomain(tm))) =>
        pTmBinaryOp(Kernel.forallin, tm, pTmAbsOverUniverse(x, body))
      case _ =>
        pTmUnaryOp(Kernel.forall, pTmAbs(binding, body))
    }
  }

  def pTmForall(xs : List[Binding], body : Preterm) : Preterm = {
    var p = body
    for (x <- xs) {
      p = pTmForall(x, p)
    }
    p
  }

  def pTmExists(binding : Binding, body : Preterm) : Preterm = {
    binding match {
      case Binding(x, Some(SetDomain(tm))) =>
        pTmBinaryOp(Kernel.existsin, tm, pTmAbsOverUniverse(x, body))
      case _ =>
        pTmUnaryOp(Kernel.exists, pTmAbs(binding, body))
    }
  }

  def pTmExists(xs : List[Binding], body : Preterm) : Preterm = {
    var p = body
    for (x <- xs) {
      p = pTmExists(x, p)
    }
    p
  }

  def pTmSetComprehension(xs : List[Binding], f : Preterm, predicate : Option[Preterm]) : Preterm = {
    if (xs.isEmpty) PTmError("set comprehension without binders")
    else {
      xs.head match {
        case Binding(x, Some(SetDomain(domain))) =>
          if (xs.tail.isEmpty) {
            val xdomain = 
              predicate match { 
                case None => domain
                case Some(predicate) => 
                  pTmBinaryOp(Kernel.set_separation, domain, pTmAbsOverUniverse(x, predicate))
              }
            pTmBinaryOp(Kernel.set_replacement, xdomain, pTmAbsOverUniverse(x, f))
          } else {
            val body = pTmSetComprehension(xs.tail, f, predicate)
            val family = pTmSetComprehension(List(xs.head), body, None)
            pTmUnaryOp(Kernel.set_bigunion, family)
          }
        case _ => PTmError("set comprehension binder must range over set")
      }
    }
  }
  
  def pTmSet(elems : List[Preterm]) : Preterm = {
    if (elems.isEmpty) 
      pTmConst(Kernel.empty_set)
    else if (elems.tail.isEmpty) 
      pTmUnaryOp(Kernel.set_singleton, elems.head)
    else 
      pTmBinaryOp(Kernel.set_union, pTmSet(elems.tail), pTmUnaryOp(Kernel.set_singleton, elems.head))
  }

  def pTmTuple(elems : List[Preterm]) : Preterm = {
  	if (elems.isEmpty)
  		Utils.failwith("there is no empty tuple")
  	else if (elems.tail.isEmpty)
  		elems.head
  	else {
  		pTmBinaryOp(Kernel.pair, pTmTuple(elems.tail), elems.head)
  	}	
  }

  def pTmBinaryOp(name : Name, left : Preterm, right : Preterm) : Preterm = 
    PTmComb(PTmComb(PTmName(name, Pretype.PTyAny), left, Some(true), Pretype.PTyAny), right, Some(true), Pretype.PTyAny)

  def pTmUnaryOp(name : Name, operand : Preterm) : Preterm = 
    PTmComb(PTmName(name, Pretype.PTyAny), operand, Some(true), Pretype.PTyAny)

  def pTmConst(name : Name) : Preterm = PTmName(name, Pretype.PTyAny)

  def pTmQuote(quoted : Any) : Preterm = PTmQuote(quoted, Pretype.PTyAny)

  def instQuotes[F, T](
    inst : (PTmQuote, Continuation[Either[Preterm, F], T]) => Thunk[T], 
    instTy : (PTyQuote, Continuation[Either[Pretype, F], T]) => Thunk[T],
    tm : Preterm, 
    cont : Continuation[Either[Preterm, F], T]) : Thunk[T] = 
  {
    tm match {
      case PTmTyping(tm, ty) => 
        instQuotes[F, T](inst, instTy, tm, {
          case Left(tm) => 
            Pretype.instQuotes[F, T](instTy, ty, {
              case Left(ty) => cont(Left(PTmTyping(tm, ty)))
              case Right(f) => cont(Right(f))
            })
          case f => cont(f)
        })
      case PTmAbs(x, ty, body, body_ty) =>
        instQuotes[F, T](inst, instTy, body, {
          case Left(body) => 
            Pretype.instQuotes[F, T](instTy, ty, {
              case Right(f) => cont(Right(f))
              case Left(ty) =>
                Pretype.instQuotes[F, T](instTy, body_ty, {
                  case Right(f) => cont(Right(f))
                  case Left(body_ty) => cont(Left(PTmAbs(x, ty, body, body_ty)))
                })
            })
          case f => cont(f)
        })
      case PTmComb(f, g, higherorder, typeof) =>
        instQuotes[F, T](inst, instTy, f, left =>
          instQuotes[F, T](inst, instTy, g, right =>
            (left, right) match {
              case (Left(f), Left(g)) => 
                Pretype.instQuotes[F, T](instTy, typeof, {
                  case Right(f) => cont(Right(f))
                  case Left(typeof) => cont(Left(PTmComb(f, g, higherorder, typeof)))
                })
              case (f @ Right(_), _) => cont(f)
              case (_, g @ Right(_)) => cont(g)              
            }))
      case q : PTmQuote => inst(q, cont)
      case name : PTmName => cont(Left(name))
      case error : PTmError => cont(Left(error))
      case tm : PTmTerm => cont(Left(tm))
    }
  }

  def computeFresh(tm : Preterm, min : Integer) : Integer = {
  	tm match {
  		case PTmTyping(tm, ty) => 
  			computeFresh(tm, Pretype.computeFresh(ty, min))
  		case PTmAbs(x, ty, body, body_ty) => 
  		  computeFresh(body, Pretype.computeFresh(body_ty, Pretype.computeFresh(ty, min)))
  		case PTmComb(f, x, _, ty) =>
  		  computeFresh(f, computeFresh(x, Pretype.computeFresh(ty, min)))
  		case PTmName(name, ty) =>
  		  Pretype.computeFresh(ty, min)
      case PTmQuote(_, ty) =>
        Pretype.computeFresh(ty, min)
      case tm : PTmTerm => min
  		case error : PTmError => Utils.failwith("internal error: computeFresh")
  	}
  }

  def listErrors(tm : Preterm, errors : List[PTmError]) : List[PTmError] = {
  	tm match {
  		case PTmTyping(tm, _) => listErrors(tm, errors)
  		case PTmAbs(_, _, body, _) => listErrors(body, errors)
  		case PTmComb(f, x, _, _) => listErrors(f, listErrors(x, errors))
  		case e : PTmError => e::errors
  		case _ : PTmName => errors
  		case _ : PTmQuote => errors
      case _ : PTmTerm => errors
  	}
  }

  private def listTyQuotes(ty : Pretype, quotes : List[Either[PTmQuote, PTyQuote]]) : List[Either[PTmQuote, PTyQuote]] = {
    val tyQuotes = Pretype.listQuotes(ty).map(q => Right(q))
    tyQuotes ++ quotes
  }

  def listQuotes(tm : Preterm, quotes : List[Either[PTmQuote, PTyQuote]]) : List[Either[PTmQuote, PTyQuote]] = {
  	tm match {
  		case PTmTyping(tm, ty) => listQuotes(tm, listTyQuotes(ty, quotes))
  		case PTmAbs(_, xty, body, bodyty) => listQuotes(body, listTyQuotes(xty, listTyQuotes(bodyty, quotes)))
  		case PTmComb(f, x, _, ty) => listQuotes(f, listQuotes(x, listTyQuotes(ty, quotes)))
  		case q : PTmQuote => Left(q)::quotes
  		case _ : PTmError => quotes
  		case _ : PTmName => quotes
      case _ : PTmTerm => quotes
  	}
  }

  def listErrors(tm : Preterm) : List[PTmError] = listErrors(tm, List())

  def listQuotes(tm : Preterm) : List[Either[PTmQuote, PTyQuote]] = listQuotes(tm, List())

  def hasQuotes(tm : Preterm) : Boolean = !listQuotes(tm).isEmpty

  def removeAny(tm : Preterm, fresh : Integer, quotes : Map[Integer, Pretype.PTyQuote]) 
    : (Preterm, Integer, Map[Integer, Pretype.PTyQuote]) = 
  {
  	tm match {
  		case PTmTyping(tm, ty) => 
  		  val (rtm, u, q1) = removeAny(tm, fresh, quotes)
  		  val (rty, v, q) = Pretype.removeAny(ty, u, q1)
  		  (PTmTyping(rtm, rty), v, q)
  		case PTmAbs(x, ty, body, body_ty) =>
  		  val (rty, u, q1) = Pretype.removeAny(ty, fresh, quotes)
  		  val (rbody, v, q2) = removeAny(body, u, q1)
  		  val (rbody_ty, w, q) = Pretype.removeAny(body_ty, v, q2)
  		  (PTmAbs(x, rty, rbody, rbody_ty), w, q)
  		case PTmComb(f, x, higherorder, ty) =>
  		  val (rf, u, q1) = removeAny(f, fresh, quotes)
  		  val (rx, v, q2) = removeAny(x, u, q1)
  		  val (rty, w, q) = Pretype.removeAny(ty, v, q2)
  		  (PTmComb(rf, rx, higherorder, rty), w, q)
  		case PTmName(name, ty) =>
  		  val (rty, u, q) = Pretype.removeAny(ty, fresh, quotes)
  		  (PTmName(name, rty), u, q)
      case PTmQuote(quote, ty) =>
        val (rty, u, q) = Pretype.removeAny(ty, fresh, quotes)
        (PTmQuote(quote, rty), u, q)
      case tm : PTmTerm => (tm, fresh, quotes)
  		case _ : PTmError => Utils.failwith("internal error: removeAny")
  	}
  } 

  def cantBeUniv(ty : Pretype) : Boolean = {
  	ty match {
  		case Pretype.PTyProp => true
  		case Pretype.PTyFun(_,_) => true
  		case _ => false
  	}
  }

  def cantBeFun(ty : Pretype) : Boolean = {
  	ty match {
  		case Pretype.PTyUniverse => true
  		case Pretype.PTyProp => true
  		case _ => false
  	}
  }

  def computeHigherOrderFlag(comb : PTmComb) : Option[Boolean] = {
    comb match {
      case PTmComb(f, x, higherorder, ty) =>
        higherorder match {
          case None =>
            val fty = f.typeOf
            if (cantBeUniv(fty) || cantBeUniv(x.typeOf) || cantBeUniv(ty))
              Some(true)
            else if (cantBeFun(fty))
              Some(false)
            else None 
          case _ => higherorder
        }
    }  
  }

  def computeTypeEqualities(context : TypingContext, tm : Preterm, eqs : Set[(Pretype, Pretype)]) : Set[(Pretype, Pretype)] = {
  	tm match {
  		case PTmTyping(tm, ty) =>
  			computeTypeEqualities(context, tm, eqs) + (ty -> tm.typeOf)
  	  case PTmName(name, ty) =>
  	  	context.lookup(name) match {
  	  		case None => eqs
  	  		case Some(name_ty) => eqs + (ty -> name_ty)
  	  	}
  	  case PTmAbs(x, ty, body, body_ty) =>
  	    computeTypeEqualities(context.addVar(x, ty), body, eqs) + (body_ty -> body.typeOf)
  	  case tmComb @ PTmComb(f, x, _higherorder, ty) =>
  	    val eqs1 = computeTypeEqualities(context, x, computeTypeEqualities(context, f, eqs))
  	    computeHigherOrderFlag(tmComb) match {
  	    	case Some(false) =>
  	    		eqs1 + (f.typeOf -> Pretype.PTyUniverse) + (x.typeOf -> Pretype.PTyUniverse) + (ty -> Pretype.PTyUniverse)
  	    	case Some(true) =>
  	    		eqs1 + (f.typeOf -> Pretype.PTyFun(x.typeOf, ty))
  	    	case None =>
  	    	  eqs1
  	    }
      case PTmQuote(q, ty) =>
        eqs
      case tm : PTmTerm =>
        eqs
  		case _ : PTmError => Utils.failwith("internal error: computeTypeEqualities")
  	}
  }

  def updateHigherOrderFlags(tm : Preterm) : Preterm = {
    tm match {
      case PTmTyping(tm, ty) => 
        PTmTyping(updateHigherOrderFlags(tm), ty)
      case PTmAbs(x, ty, body, body_ty) => 
        PTmAbs(x, ty, updateHigherOrderFlags(body), body_ty)
      case tmComb @ PTmComb(f, x, higherorder, ty) =>
        PTmComb(updateHigherOrderFlags(f), updateHigherOrderFlags(x), computeHigherOrderFlag(tmComb), ty)
      case _ => tm
    }
  }

  def subst(s : Integer => Option[Pretype], tm : Preterm) : Preterm = {
  	def stm(tm : Preterm) : Preterm = subst(s, tm)
  	def sty(ty : Pretype) : Pretype = Pretype.subst(s, ty)
  	tm match {
  		case PTmTyping(tm, ty) => PTmTyping(stm(tm), sty(ty))
  		case PTmName(name, ty) => PTmName(name, sty(ty))
  		case PTmAbs(x, ty, body, body_ty) => PTmAbs(x, sty(ty), stm(body), sty(body_ty))
  		case PTmComb(f, x, higherorder, ty) => PTmComb(stm(f), stm(x), higherorder, sty(ty))
  		case PTmQuote(q, ty) => PTmQuote(q, sty(ty))
      case tm : PTmTerm => tm
      case _ : PTmError => Utils.failwith("internal error: subst")
  	}
  } 

  def translate(context : Context, tm : Term) : Preterm = {
    context.typeOfTerm(tm) match {
      case Some(ty) => PTmTerm(tm, ty)
      case None => Utils.failwith("wrapTranslate: term cannot be typed in given context")
    }
  }

  def translate(context : Context, tm : CTerm) : Preterm = {
    val liftedTm = context.lift(tm)
    PTmTerm(liftedTm.term, liftedTm.typeOf)
  }

  private def translateTerm(tm : Term) : Preterm = {
    tm match {
      case c : Term.PolyConst => PTmName(c.name, Pretype.translate(KernelUtils.typeOfPolyConst(c).get))
      case Term.Const(name) => PTmName(name, Pretype.PTyAny) 
      case Term.Var(name) => PTmName(Name(None, name), Pretype.PTyAny) 
      case Term.Comb(f, g) => PTmComb(translateTerm(f), translateTerm(g), Some(true), Pretype.PTyAny)
      case Term.Abs(name, ty, body) => PTmAbs(name, Pretype.translate(ty), translateTerm(body), Pretype.PTyAny)
    }
  }

  def translate(context : TypingContext, tm : Preterm) : Term = {
  	tm match {
  		case PTmTyping(tm, ty) => 
  			translate(context, tm)
  		case PTmName(name, ty) => 
  			context.resolve(name, ty) match {
  				case None => Utils.failwith("name resolution failed in Preterm.translate for: "+name)
  				case Some(t) => t
  			}
  		case PTmAbs(x, ty, body, _) => 
  			Term.Abs(x, Pretype.translate(ty), translate(context.addVar(x, ty), body))  
  	  case PTmComb(f, x, _, _) =>
  	  	val u = translate(context, f)
  	  	val v = translate(context, x)
  	  	if (f.typeOf == Pretype.PTyUniverse) {  	  		
  	  		Term.Comb(Term.Comb(Term.Const(Kernel.funapply), u), v)
  	  	} else {
  	  		Term.Comb(u, v)
  	  	}
      case PTmTerm(tm, _) => tm
      case _ : PTmQuote => Utils.failwith("internal error: translate")
  		case _ : PTmError => Utils.failwith("internal error: translate")  		
  	}
  }

  def checkNameTypes(context : TypingContext, tm : Preterm, fresh : Integer) : (Preterm, Integer) = {
  	tm match {
  		case PTmName(name, ty) =>
  			context.lookupPolymorphic(name, fresh) match {
  				case None => (PTmError("unknown name: "+name), fresh)
  				case Some((_, ty1, fresh1, _)) => 
  					if (fresh1 == fresh) 
  						(tm, fresh)
  					else {
  						if (ty == Pretype.PTyAny) {
  							(PTmName(name, ty1), fresh1)
  						} else {
  							(PTmTyping(tm, ty1), fresh1)
  						}
  					}
  			}
  		case PTmTyping(tm, ty) => 
  			val (t, fresh1) = checkNameTypes(context, tm, fresh)
  			(PTmTyping(t, ty), fresh1)
  		case PTmAbs(x, ty, body, body_ty) =>
  			val (t, fresh1) = checkNameTypes(context.addVar(x, ty), body, fresh)
  			(PTmAbs(x, ty, t, body_ty), fresh1)
  		case PTmComb(f, x, higherorder, ty) =>
  			val (t1, fresh1) = checkNameTypes(context, f, fresh)
  			val (t2, fresh2) = checkNameTypes(context, x, fresh1)
  			(PTmComb(t1, t2, higherorder, ty), fresh2)
      case q: PTmQuote => 
        (q, fresh)
      case tm : PTmTerm =>
        (tm, fresh)
  		case _ : PTmError => Utils.failwith("internal error: checkNameTypes")
  	}
  }

  def inferTypes1(context : TypingContext, tm : Preterm, vars : Map[Integer, Pretype]) : Option[(Preterm, Map[Integer, Pretype])] = {
  	val eqs = computeTypeEqualities(context, tm, Set())
  	val s = Pretype.solve(eqs)
  	if (s == null) None 
    else {
      val t = updateHigherOrderFlags(subst(n => s.get(n), tm))
      val f = s.get _
      val vs = vars.mapValues(pretype => Pretype.subst(f, pretype))
      Some((t, vs))
    }
  }

  def inferTypes(context : TypingContext, term : Preterm, vars : Map[Integer, Pretype]) : Option[(Preterm, Map[Integer, Pretype])] = {
  	var t = term
    var typeVars = vars
  	do {  	
  		inferTypes1(context, t, typeVars) match {
  			case None => return None
  			case Some((s, vars)) =>
  				if (s == t) return Some((t, typeVars))
  				t = s
          typeVars = vars
  		}
  	} while (true)
  	Utils.failwith("internal error")
  }

  def inferPolymorphicPreterm(context : TypingContext, term : Preterm) 
    : Either[(Preterm, Map[Integer, Pretype.PTyQuote], Map[Integer, Pretype]), List[PTmError]] = 
  {
    try {
      val (checkedTerm, checkedFresh) = checkNameTypes(context, term, computeFresh(term, 0))
      val errors = listErrors(checkedTerm)
      if (!errors.isEmpty) return Right(errors)
      val (t, fresh, quotes) = removeAny(checkedTerm, checkedFresh, Map())
      val typeVars = quotes.map({case (i, v) => (i, Pretype.PTyVar(i))})
      inferTypes(context, t, typeVars) match {
        case None => Right(List(PTmError("term is ill-typed")))
        case Some((t, typeVars)) => Left((t, quotes, typeVars))
      }
    } catch {
      case e : Utils.KernelException =>
        Right(List(PTmError(e.reason)))
    }
  }

  def inferPreterm(context : TypingContext, term : Preterm) : Either[Preterm, List[PTmError]] = {
  	inferPolymorphicPreterm(context, term) match {
  		case Right(errors) => Right(errors)
  		case Left((t, quotes, _)) => 
        if (!quotes.isEmpty) Utils.failwith("term contains type quotes")
  			val tNoVars = updateHigherOrderFlags(subst(n => Some(Pretype.PTyUniverse), t))
        Left(tNoVars)
  	}
  }

  def inferTerm(context : TypingContext, term : Preterm) : Either[Term, List[PTmError]] = {
    inferPreterm(context, term) match {
      case Left(t) => Left(translate(context, t))
      case Right(errors) => Right(errors)
    }
  }

  def inferCTerm(context : TypingContext, term : Preterm) : Either[CTerm, List[PTmError]] = {
    inferPreterm(context, term) match {
      case Left(t) => Left(context.context.certify(translate(context, t)))
      case Right(errors) => Right(errors)
    }
  }

  private def strip_comb(term : Preterm) : (Preterm, List[(Preterm, Option[Boolean], Pretype)]) = {
    term match {
      case PTmComb(f, g, higherorder, ty) =>
        val (u, vs) = strip_comb(f) 
        (u, vs :+ (g, higherorder, ty))
      case _ => (term, List())
    }
  }

  private def countHigherOrderPatternCombs(f : Preterm, args : List[(Preterm, Option[Boolean], Pretype)],
    vars : Set[IndexedName]) : Int = 
  {
    f match {
      case q : PTmQuote => 
        var c : Int = 0
        var localVars : Set[IndexedName] = Set()
        for (arg <- args) {
          arg match {
            case (_, Some(false), _) => return c
            case (PTmName(name, ty), _, _) if name.namespace.isEmpty && 
              vars.contains(name.name) && !localVars.contains(name.name) 
            => 
              localVars = localVars + name.name
              c = c + 1
            case _ => return c
          }
        }
        c
      case _ => 0
    }
  }

  private def decideHigherOrderFlags(term : Preterm, vars : Set[IndexedName]) : Preterm = {
    term match {
      case PTmTyping(tm, ty) => PTmTyping(decideHigherOrderFlags(tm, vars), ty)
      case PTmAbs(x, ty, body, body_ty) =>
        PTmAbs(x, ty, decideHigherOrderFlags(body, vars + x), body_ty)
      case comb : PTmComb =>
        val (u, vs) = strip_comb(comb)
        val c = countHigherOrderPatternCombs(u, vs, vars)
        val metacombs = vs.take(c).map(x => (decideHigherOrderFlags(x._1, vars), Some(true), x._3))
        val setcombs = vs.drop(c).map(x => (decideHigherOrderFlags(x._1, vars), 
          if (x._2.isDefined) x._2 else Some(false), x._3))
        var result : Preterm = decideHigherOrderFlags(u, vars)
        for ((g, higherorder, ty) <- (metacombs ++ setcombs)) {
          result = PTmComb(result, g, higherorder, ty)
        }
        result
      case t => t
    }
  }

  def inferPattern(context : TypingContext, term : Preterm) 
    : Either[(Preterm, Map[Integer, Pretype.PTyQuote], Map[Integer, Pretype]), List[PTmError]] = 
  {
    inferPolymorphicPreterm(context, term) match {
      case Right(errors) => Right(errors)
      case Left((t, quotes, typesOfQuotes)) =>
        val tDecided = decideHigherOrderFlags(t, Set())
        inferTypes(context, tDecided, typesOfQuotes) match {
          case None =>
            // not sure if this can happen or not:
            Right(List(PTmError("term is ill-typed after deciding all higherorder flags"))) 
          case Some((t, typesOfQuotes)) => Left((t, quotes, typesOfQuotes))
        }
    }
  }

  type NameResolution = Name => Either[Name, Set[Namespace]]

  val unknownResolution : NameResolution = name => Right(Set())

  trait TypingContext {
  	def lookupPolymorphic(name : Name, fresh : Integer) : Option[(Name, Pretype, Integer, Boolean)] // like lookup, but also works for polymorphic constants
  	def lookup(name : Name) : Option[Pretype] // returns None for polymorphic constants!
  	def resolve(name : Name, ty : Pretype) : Option[Term] // returns None for polymorphic constants!
  	def addVar(name : IndexedName, ty : Pretype) : TypingContext
    def context : Context
  }

  def obtainTypingContext(context : Context) : TypingContext = {
  	new TC(context, List())
  }

  private class TC(val context : Context, vars : List[(IndexedName, Pretype)]) 
  	extends TypingContext 
  {
  	private def polyTypeOf(name : Name, fresh : Integer) : Option[Pretype] = {
  		import Pretype._
  		name match {
  			case Kernel.forall => Some(PTyFun(PTyFun(PTyVar(fresh), PTyProp), PTyProp))
  			case Kernel.exists => Some(PTyFun(PTyFun(PTyVar(fresh), PTyProp), PTyProp))
  			case Kernel.equals => Some(PTyFun(PTyVar(fresh), PTyFun(PTyVar(fresh), PTyProp)))
  			case _ => None
  		}
  	}
  	private def lookupName(_name : Name, fresh : Integer) : Option[(Name, Pretype, Integer, Boolean)] = {
      val name =
        context.resolveLogicalName(_name) match {
          case Left(name) => name
          case Right(_) => return None
        }
  		polyTypeOf(name, fresh) match {
  			case Some(ty) => Some((name, ty, fresh + 1, false))
  			case None => 
  				context.typeOfConst(name) match {
  					case None => None
  					case Some(ty) => Some((name, Pretype.translate(ty), fresh, false))
  				}
  		}	
  	}
  	def lookupPolymorphic(name : Name, fresh : Integer) : Option[(Name, Pretype, Integer, Boolean)] = {
  		if (name.namespace.isDefined) 
  			lookupName(name, fresh)
  		else {
  			val u = name.name
  			for ((v, ty) <- vars) {
  				if (u == v) {
  					return Some(name, ty, fresh, true)
  				}
  			}
        lookupName(name, fresh)
  		}
  	}
  	def lookup(name : Name) : Option[Pretype] = {
  		lookupPolymorphic(name, 0) match {
  			case None => None
  			case Some((_, ty, fresh, _)) => if (fresh > 0) None else Some(ty)
  		}
  	}
  	private def resolveConst(name : Name, ty : Pretype) : Option[Term] = {
			lookupPolymorphic(name, 0) match {
				case None => None
				case Some((name, t, fresh, _)) =>
					if (fresh == 0) {
						if (t == ty) Some(Term.Const(name)) else None
					} else {
						import Pretype._
						(name, ty) match {
							case (Kernel.forall, PTyFun(PTyFun(alpha, PTyProp), PTyProp)) =>
								Some(Term.PolyConst(Kernel.forall, Pretype.translate(alpha)))
							case (Kernel.exists, PTyFun(PTyFun(alpha, PTyProp), PTyProp)) =>
								Some(Term.PolyConst(Kernel.exists, Pretype.translate(alpha)))
							case (Kernel.equals, PTyFun(alpha, PTyFun(beta, PTyProp))) if alpha == beta =>
								Some(Term.PolyConst(Kernel.equals, Pretype.translate(alpha)))
							case _ => None
						}
					}
			}  			
  	}
  	def resolve(name : Name, ty : Pretype) : Option[Term] = {
  		if (!name.namespace.isDefined) {
  			val u = name.name
  			for ((v, _) <- vars) {
  				if (u == v) {
  					return Some(Term.Var(u))
  				}
  			}
        resolveConst(name, ty)
			} else resolveConst(name, ty)
  	}
  	def addVar(x : IndexedName, ty : Pretype) : TypingContext = {
  		new TC(context, (x, ty)::vars)
  	}
  }
}