package proofpeer.proofscript.logic

sealed trait Domain
case class TypeDomain(ty : Pretype) extends Domain
case class SetDomain(tm : Preterm) extends Domain
case class Binding(name : IndexedName, domain : Option[Domain])

sealed trait Preterm {
	def typeOf : Pretype
}
object Preterm {
 
  case class PTmTyping(tm : Preterm, typeOf : Pretype) extends Preterm
  case class PTmName(name : Name, typeOf : Pretype) extends Preterm
  case class PTmAbs(x : IndexedName, ty : Pretype, body : Preterm, body_ty : Pretype) extends Preterm {
  	def typeOf = Pretype.PTyFun(ty, body_ty)
  }
  case class PTmComb(f : Preterm, x : Preterm, higherorder : Option[Boolean], typeOf : Pretype) extends Preterm
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
  		case PTmError(_) => min
  	}
  }

  def listErrors(tm : Preterm, errors : List[PTmError]) : List[PTmError] = {
  	tm match {
  		case PTmTyping(tm, _) => listErrors(tm, errors)
  		case PTmAbs(_, _, body, _) => listErrors(body, errors)
  		case PTmComb(f, x, _, _) => listErrors(f, listErrors(x, errors))
  		case PTmName(_,_) => errors
  		case e : PTmError => e::errors
  	}
  }

  def listErrors(tm : Preterm) : List[PTmError] = listErrors(tm, List())

  def removeAny(tm : Preterm, fresh : Integer) : (Preterm, Integer) = {
  	tm match {
  		case PTmTyping(tm, ty) => 
  		  val (rtm, u) = removeAny(tm, fresh)
  		  val (rty, v) = Pretype.removeAny(ty, u)
  		  (PTmTyping(rtm, rty), v)
  		case PTmAbs(x, ty, body, body_ty) =>
  		  val (rty, u) = Pretype.removeAny(ty, fresh)
  		  val (rbody, v) = removeAny(body, u)
  		  val (rbody_ty, w) = Pretype.removeAny(body_ty, v)
  		  (PTmAbs(x, rty, rbody, rbody_ty), w)
  		case PTmComb(f, x, higherorder, ty) =>
  		  val (rf, u) = removeAny(f, fresh)
  		  val (rx, v) = removeAny(x, u)
  		  val (rty, w) = Pretype.removeAny(ty, v)
  		  (PTmComb(rf, rx, higherorder, rty), w)
  		case PTmName(name, ty) =>
  		  val (rty, u) = Pretype.removeAny(ty, fresh)
  		  (PTmName(name, rty), u)
  		case PTmError(_)  => (tm, fresh)
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
  	  case PTmComb(f, x, _higherorder, ty) =>
  	    val eqs1 = computeTypeEqualities(context, x, computeTypeEqualities(context, f, eqs))
  	    val higherorder = 
  	      _higherorder match {
  	    	  case None =>
  	    	  	val fty = f.typeOf
  	    	  	if (cantBeUniv(fty) || cantBeUniv(x.typeOf) || cantBeUniv(ty))
  	    	  	  Some(true)
  	    	  	else if (cantBeFun(fty))
  	    	  	  Some(false)
  	    	  	else None 
  	    	  case _ => _higherorder
  	      }
  	    higherorder match {
  	    	case Some(false) =>
  	    		eqs1 + (f.typeOf -> Pretype.PTyUniverse) + (x.typeOf -> Pretype.PTyUniverse) + (ty -> Pretype.PTyUniverse)
  	    	case Some(true) =>
  	    		eqs1 + (f.typeOf -> Pretype.PTyFun(x.typeOf, ty))
  	    	case None =>
  	    	  eqs1
  	    }
  	  case _ : PTmError => eqs
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
  		case e : PTmError => e
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
  		case e : PTmError => Utils.failwith("preterm contains error")  		
  	}
  }

  def checkNameTypes(context : TypingContext, tm : Preterm, fresh : Integer) : (Preterm, Integer) = {
  	tm match {
  		case PTmName(name, ty) =>
  			context.lookupPolymorphic(name, fresh) match {
  				case None => (PTmError("unknown name: "+name), fresh)
  				case Some((ty1, fresh1)) => 
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
  		case e : PTmError => (e, fresh)
  	}
  }

  def inferTypes1(context : TypingContext, tm : Preterm) : Option[Preterm] = {
  	val eqs = computeTypeEqualities(context, tm, Set())
  	val s = Pretype.solve(eqs)
  	if (s == null) None else Some(subst(n => s.get(n), tm))
  }

  def inferTypes(context : TypingContext, term : Preterm) : Option[Preterm] = {
  	var t = term
  	do {  	
  		inferTypes1(context, t) match {
  			case None => return None
  			case Some(s) =>
  				if (s == t) return Some(t)
  				t = s
  		}
  	} while (true)
  	Utils.failwith("internal error")
  }

  def inferTerm(context : TypingContext, term : Preterm) : Either[Term, List[PTmError]] = {
  	val (checkedTerm, checkedFresh) = checkNameTypes(context, term, computeFresh(term, 0))
  	val errors = listErrors(checkedTerm)
  	if (!errors.isEmpty) return Right(errors)
  	val (t, fresh) = removeAny(checkedTerm, checkedFresh)
  	inferTypes(context, t) match {
  		case None => Right(List(PTmError("term is ill-typed")))
  		case Some(t) => 
  			val tNoVars = subst(n => Some(Pretype.PTyUniverse), t)
  			// this inferTypes is unnecessary, let's do it anyway for now
  			inferTypes(context, tNoVars) match {
  				case None => 
  				  // Some careful thinking tells us that this case can never happen.
  				  // To see why: the only way this can happen is that conflicting comb constraints
  				  // are added in computeTypeEqualities when eliminating the variables. In particular there
  				  // must be a PTmComb term for which the computed higher-order was None before, and is Some(_) now,
  				  // and the added constraints produce a conflict.  
  				  // Case analysis shows that this cannot happen:
  				  // 1. Because the computed higher-order was None before, we know that before this holds:
  				  //    - f.typeOf is a variable 
  				  //    - x.typeOf is a variable or universe
  				  //    - typeOf is a variable or universe
  				  // 2. If the computed higher-order is Some(true) after, we know that afterwards:
  				  //		- One of f.typeOf, x.typeOf and typeOf must be prop or fun
  				  //    But this contradicts 1., so 2. is not possible.
  				  // 3. If the computed higher-order is Some(false) after, the added constraints are that:
  				  //    f.typeOf is a universe, x.typeOf is a universe, and typeOf is a universe
  				  //    All of these constraints are a consequence of 1. and the fact that the substitution
  				  //    replaces all variables by universe, so no conflict can arise.
  					Utils.failwith("internal error: term is ill-typed after eliminating all type variables")
  				case Some(t) => 
  				  Left(translate(context, t))
  			}
  	}
  }

  trait TypingContext {
  	def lookupPolymorphic(name : Name, fresh : Integer) : Option[(Pretype, Integer)] // like lookup, but also works for polymorphic constants
  	def lookup(name : Name) : Option[Pretype] // returns None for polymorphic constants!
  	def resolve(name : Name, ty : Pretype) : Option[Term] // returns None for polymorphic constants!
  	def addVar(name : IndexedName, ty : Pretype) : TypingContext
  }

  def obtainTypingContext(nr : NameResolution, context : Context) : TypingContext = {
  	new TC(nr.resolveContext(context), context, List())
  }

  private class TC(r : NameResolution.Resolution, context : Context, vars : List[(IndexedName, Pretype)]) 
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
  	private def lookupName(name : Name, fresh : Integer) : Option[(Pretype, Integer)] = {
  		polyTypeOf(name, fresh) match {
  			case Some(ty) => Some((ty, fresh + 1))
  			case None => 
  				context.typeOfConst(name) match {
  					case None => None
  					case Some(ty) => Some((Pretype.translate(ty), fresh))
  				}
  		}	
  	}
  	def lookupPolymorphic(name : Name, fresh : Integer) : Option[(Pretype, Integer)] = {
  		if (name.namespace.isDefined) 
  			lookupName(name, fresh)
  		else {
  			val u = name.name
  			for ((v, ty) <- vars) {
  				if (u == v) {
  					return Some(ty, fresh)
  				}
  			}
  			r.get(u) match {
  				case None => None
  				case Some(name) => lookupName(name, fresh)
  			}
  		}
  	}
  	def lookup(name : Name) : Option[Pretype] = {
  		lookupPolymorphic(name, 0) match {
  			case None => None
  			case Some((ty, fresh)) => if (fresh > 0) None else Some(ty)
  		}
  	}
  	private def resolveConst(name : Name, ty : Pretype) : Option[Term] = {
			lookupPolymorphic(name, 0) match {
				case None => None
				case Some((t, fresh)) =>
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
  			r.get(u) match {
  				case None => None
  				case Some(name) => resolveConst(name, ty)
  			}
			} else resolveConst(name, ty)
  	}
  	def addVar(x : IndexedName, ty : Pretype) : TypingContext = {
  		new TC(r, context, (x, ty)::vars)
  	}
  }
}