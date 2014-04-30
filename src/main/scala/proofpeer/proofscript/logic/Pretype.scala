package proofpeer.proofscript.logic

sealed trait Pretype
object Pretype {
  case object PTyUniverse extends Pretype
  case object PTyProp extends Pretype
  case class PTyFun(domain : Pretype, range : Pretype) extends Pretype
  case object PTyAny extends Pretype
  case class PTyVar(n : Integer) extends Pretype // type variables are only used during type inference 

  // Computes an integer n such that
  // 1. n >= min 
  // 2. for all m >= n: PTyVar(m) does not appear in ty
  def computeFresh(ty : Pretype, min : Integer) : Integer = {
    ty match {
      case PTyVar(n) =>
        if (n < min) min else n + 1
      case PTyFun(domain, range) =>
        computeFresh(range, computeFresh(domain, min))
      case _ => min
    }
  }

  def occurs(n : Integer, ty : Pretype) : Boolean = {
  	ty match {
  		case PTyVar(m) => n == m
  		case PTyFun(domain, range) => occurs(n, domain) || occurs(n, range)
  		case _ => false
  	}
  }

  // Removes all occurrences of PTyAny by fresh variables.
  def removeAny(ty : Pretype) : Pretype = {
  	removeAny(ty, computeFresh(ty, 0))._1
  }

  def removeAny(ty : Pretype, fresh : Integer) : (Pretype, Integer) = {
  	ty match {
  	  case PTyAny => (PTyVar(fresh), fresh + 1)
  	  case PTyFun(domain, range) =>
  	    val (rdomain, u) = removeAny(domain, fresh)
  	    val (rrange, v) = removeAny(range, u)
  	    (PTyFun(rdomain, rrange), v)
  	  case _ => (ty, fresh)
  	}
  }

  // Solves a set of equations between types. None of the types may contain PTyAny.
  // Returns null if there is no solution.
  def solve(eqs : Set[(Pretype, Pretype)]) : Map[Integer, Pretype] = {
  	var equations = eqs
  	var continueTransforming = true
  	do {
  	  val transformed = transform(equations)
  	  if (transformed == null) return null
  	  continueTransforming = (transformed != equations)
  	  equations = transformed
  	} while (continueTransforming)
  	var s : Map[Integer, Pretype] = Map()
  	for ((PTyVar(n), t) <- equations) {	
  		s = s + (n -> t)
  	}
  	s
  }

  def subst(s : Integer => Option[Pretype], ty : Pretype) : Pretype = {
  	ty match {
  		case PTyVar(n) =>
  		  s(n) match {
  		  	case None => ty
  		  	case Some(ty) => ty
  		  }
  		case PTyFun(domain, range) =>
  		  PTyFun(subst(s, domain), subst(s, range))
  		case _ => ty
  	}
  }

  def subst(n : Integer, s : Pretype, ty : Pretype) : Pretype = {
  	subst(m => if (n == m) Some(s) else None, ty)
  }

  private def substEqs(n : Integer, t : Pretype, _eqs: Set[(Pretype, Pretype)]) : Set[(Pretype, Pretype)] = {
  	var eqs : Set[(Pretype, Pretype)] = Set()
  	for ((left, right) <- _eqs) {
  		eqs = eqs + (subst(n, t, left) -> subst(n, t, right))
  	}
    eqs
  }

  private def transform(_eqs : Set[(Pretype, Pretype)]) : Set[(Pretype, Pretype)] = {
  	var transformed : Set[(Pretype, Pretype)] = Set()
  	var eqs = _eqs
  	while (!eqs.isEmpty) {
  		val (left, right) = eqs.head
  		eqs = eqs.tail
  		if (left != right) {
  	  	(left, right) match {
  	  		case (PTyFun(domain1, range1), PTyFun(domain2, range2)) =>
  	  		  transformed = transformed + (domain1 -> domain2) + (range1 -> range2)
  	  		case (PTyVar(n), t) =>
  	  			if (occurs(n, t)) return null
  	  			transformed = substEqs(n, t, transformed) + (left -> right)
  	  			eqs = substEqs(n, t, eqs)
  	  	  case (t, PTyVar(n)) =>
  	  	    transformed = transformed + (right -> left)
  	  	  case _ =>
  	  	    return null
  	  	}
  		}
  	}
  	transformed
  }

  def translate(ty : Pretype) : Type = {
  	ty match {
  		case PTyUniverse => Type.Universe
  		case PTyProp => Type.Prop
  		case PTyFun(domain, range) => Type.Fun(translate(domain), translate(range))
  		case _ => Utils.failwith("cannot translate PTyAny or PTyVar into proper Type")
  	}
  }

}

