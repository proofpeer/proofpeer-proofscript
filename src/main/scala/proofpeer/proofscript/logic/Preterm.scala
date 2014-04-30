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
  case class PTmForall(x : IndexedName, ty : Pretype, body : Preterm) extends Preterm {
  	def typeOf = Pretype.PTyProp
  }
  case class PTmExists(x : IndexedName, ty : Pretype, body : Preterm) extends Preterm {
  	def typeOf = Pretype.PTyProp
  }
  case class PTmEquals(left : Preterm, right : Preterm) extends Preterm {
  	def typeOf = Pretype.PTyProp
  }
  case class PTmComb(f : Preterm, x : Preterm, higherorder : Option[Boolean], typeOf : Pretype) extends Preterm
  case class PTmError(reason : String) extends Preterm {
  	def typeOf = Pretype.PTyAny
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
      case Binding(x, None) =>
        PTmForall(x, Pretype.PTyAny, body)
      case Binding(x, Some(TypeDomain(ty))) =>
        PTmForall(x, ty, body)
      case Binding(x, Some(SetDomain(tm))) =>
        pTmBinaryOp(Kernel.forallin, tm, pTmAbsOverUniverse(x, body))
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
      case Binding(x, None) =>
        PTmExists(x, Pretype.PTyAny, body)
      case Binding(x, Some(TypeDomain(ty))) =>
        PTmExists(x, ty, body)
      case Binding(x, Some(SetDomain(tm))) =>
        pTmBinaryOp(Kernel.existsin, tm, pTmAbsOverUniverse(x, body))
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
  		case PTmForall(x, ty, body) => 
  		  computeFresh(body, Pretype.computeFresh(ty, min))
  		case PTmExists(x, ty, body) => 
  		  computeFresh(body, Pretype.computeFresh(ty, min))
  		case PTmEquals(left, right) =>
  		  computeFresh(left, computeFresh(right, min))
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
  		case PTmForall(_, _, body) => listErrors(body, errors)
  		case PTmExists(_, _, body) => listErrors(body, errors)
  		case PTmEquals(left, right) => listErrors(right, listErrors(left, errors))
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
  		case PTmForall(x, ty, body) =>
  		  val (rty, u) = Pretype.removeAny(ty, fresh)
  		  val (rbody, v) = removeAny(body, u)
  		  (PTmForall(x, rty, rbody), v)
  		case PTmExists(x, ty, body) =>
  		  val (rty, u) = Pretype.removeAny(ty, fresh)
  		  val (rbody, v) = removeAny(body, u)
  		  (PTmExists(x, rty, rbody), v)
  		case PTmEquals(left, right) =>
  		  val (rleft, u) = removeAny(left, fresh)
  		  val (rright, v) = removeAny(right, u)
  		  (PTmEquals(rleft, rright), v)  
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
  	  case PTmForall(x, ty, body) =>
  	    computeTypeEqualities(context.addVar(x, ty), body, eqs) + (body.typeOf -> Pretype.PTyProp)
  	  case PTmExists(x, ty, body) =>
  	    computeTypeEqualities(context.addVar(x, ty), body, eqs) + (body.typeOf -> Pretype.PTyProp)
  	  case PTmEquals(left : Preterm, right : Preterm) =>
  	    val eqs1 = computeTypeEqualities(context, left, eqs)
  	    val eqs2 = computeTypeEqualities(context, right, eqs1)
  	    eqs2 + (left.typeOf -> right.typeOf)
  	  case PTmComb(f, x, _higherorder, ty) =>
  	    val eqs1 = computeTypeEqualities(context, x, computeTypeEqualities(context, f, eqs))
  	    val higherorder = 
  	      _higherorder match {
  	    	  case None =>
  	    	  	val fty = f.typeOf
  	    	  	if (cantBeUniv(fty) || cantBeUniv(x.typeOf) || cantBeUniv(ty))
  	    	  	  Some(true)
  	    	  	else if (cantBeFun(fty) || fty == x)
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
  		case PTmForall(x, ty, body) => PTmForall(x, sty(ty), stm(body))
  		case PTmExists(x, ty, body) => PTmExists(x, sty(ty), stm(body))
  		case PTmEquals(left, right) => PTmEquals(stm(left), stm(right))
  		case PTmComb(f, x, higherorder, ty) => PTmComb(stm(f), stm(x), higherorder, sty(ty))
  		case e : PTmError => e
  	}
  } 

  def translate(context : TypingContext, tm : Preterm) : Term = {
  	tm match {
  		case PTmTyping(tm, ty) => 
  			translate(context, tm)
  		case PTmName(name, ty) => 
  			context.resolve(name) match {
  				case None => Utils.failwith("name resolution failed in Preterm.translate")
  				case Some(Left(t)) => t
  				case Some(Right(t)) => t 
  			}
  		case PTmAbs(x, ty, body, _) => 
  			Term.Abs(x, Pretype.translate(ty), translate(context.addVar(x, ty), body))  
  	  case PTmForall(x, ty, body) =>
  	  	val xty = Pretype.translate(ty)
  	  	val abs = Term.Abs(x, xty, translate(context.addVar(x, ty), body))
  	  	Term.Comb(Term.PolyConst(Kernel.forall, xty), abs)
  	  case PTmExists(x, ty, body) =>
  	  	val alpha = Pretype.translate(ty)
  	  	val abs = Term.Abs(x, alpha, translate(context.addVar(x, ty), body))
  	  	Term.Comb(Term.PolyConst(Kernel.exists, alpha), abs) 
  	  case PTmEquals(left, right) =>
  	  	val alpha = Pretype.translate(left.typeOf)
  	  	val l = translate(context, left)
  	  	val r = translate(context, right)
  	  	Term.Comb(Term.Comb(Term.PolyConst(Kernel.equals, alpha), l), r)	
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

  def checkNameTypes(context : TypingContext, tm : Preterm) : Preterm = {
  	tm match {
  		case PTmName(name, ty) =>
  			context.lookup(name) match {
  				case None => PTmError("unknown name: "+name)
  				case _ => tm
  			}
  		case PTmTyping(tm, ty) => PTmTyping(checkNameTypes(context, tm), ty)
  		case PTmAbs(x, ty, body, body_ty) =>
  			PTmAbs(x, ty, checkNameTypes(context.addVar(x, ty), body), body_ty)
  		case PTmForall(x, ty, body) => 
  		  PTmForall(x, ty, checkNameTypes(context.addVar(x, ty), body))
  		case PTmExists(x, ty, body) =>
  		  PTmExists(x, ty, checkNameTypes(context.addVar(x, ty), body))
  		case PTmEquals(left, right) =>
  		  PTmEquals(checkNameTypes(context, left), checkNameTypes(context, right))
  		case PTmComb(f, x, higherorder, ty) =>
  			PTmComb(checkNameTypes(context, f), checkNameTypes(context, x), higherorder, ty)
  		case e : PTmError => e
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
  	val errors = listErrors(checkNameTypes(context, term))
  	if (!errors.isEmpty) return Right(errors)
  	val (t, fresh) = removeAny(term, computeFresh(term, 0))
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
  	def lookup(name : Name) : Option[Pretype]
  	def resolve(name : Name) : Option[Either[Term.Var, Term.Const]]
  	def addVar(name : IndexedName, ty : Pretype) : TypingContext
  }

  def obtainTypingContext(r : NameResolution.Resolution, context : Context) : TypingContext = {
  	new TC(r, context, List())
  }

  private class TC(r : NameResolution.Resolution, context : Context, vars : List[(IndexedName, Pretype)]) 
  	extends TypingContext 
  {
  	def lookup(name : Name) : Option[Pretype] = {
  		if (name.namespace.isDefined) {
  			context.typeOfConst(name) match {
  				case None => None
  				case Some(ty) => Some(Pretype.translate(ty))
  			}
  		} else {
  			val u = name.name
  			for ((v, ty) <- vars) {
  				if (u == v) {
  					return Some(ty)
  				}
  			}
  			r.get(u) match {
  				case None => None
  				case Some(name) => 
  					context.typeOfConst(name) match {
  						case None => Utils.failwith("internal error: name is not defined, but should be: "+name)
  						case Some(ty) => Some(Pretype.translate(ty))
  					}
  			}
  		}
  	}
  	def resolve(name : Name) : Option[Either[Term.Var, Term.Const]] = {
  		if (name.namespace.isDefined) {
  			context.typeOfConst(name) match {
  				case None => None
  				case Some(_) => Some(Right(Term.Const(name)))
  			}
  		} else {
  			val u = name.name
  			for ((v, _) <- vars) {
  				if (u == v) {
  					return Some(Left(Term.Var(u)))
  				}
  			}
  			r.get(u) match {
  				case None => None
  				case Some(name) => Some(Right(Term.Const(name)))
  			}
  		}  		
  	}
  	def addVar(x : IndexedName, ty : Pretype) : TypingContext = {
  		new TC(r, context, (x, ty)::vars)
  	}
  }


}