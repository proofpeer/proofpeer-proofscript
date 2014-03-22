package proofpeer.proofscript.logic

import Term._
import Type._
import Utils._

object KernelUtils {

  def isQualifiedName(name : Name) : Boolean = name.namespace.isDefined
  
  def isQualifiedTerm(term : Term) : Boolean = {
    term match {
      case PolyConst(name, alpha) => isQualifiedName(name)
      case Const(name) => isQualifiedName(name)
      case Comb(f, x) => isQualifiedTerm(f) && isQualifiedTerm(x)
      case Abs(name, ty, body) => isQualifiedTerm(body)
      case Var(name) => true
    }
  }
  
  def typeOfTerm(c : Context, vars : Map[IndexedName, Type], term : Term) : Option[Type] = {
    term match {
      case PolyConst(name, alpha) =>
        name match {
          case Kernel.equals => Some(Fun(alpha, Fun(alpha, Prop)))
          case Kernel.forall | Kernel.exists => Some(Fun(Fun(alpha, Prop), Prop))
          case Kernel.choose => Some(Fun(Fun(alpha, Prop), alpha))            
          case _ => None
        }
      case Const(name) => c.typeOfConst(name)
      case Var(name) => vars.get(name)
      case Comb(f, x) => 
        (typeOfTerm(c, vars, f), typeOfTerm(c, vars, x)) match {
          case (Some(Fun(fdomain, frange)), Some(xty)) if fdomain == xty =>
            Some(frange)
          case _ => None
        }
      case Abs(name, ty, body) =>
        typeOfTerm(c, vars + (name -> ty), body) match {
          case Some(bodyty) => Some(Fun(ty, bodyty))
          case None => None            
        }
    }
  }

  def collectConsts(term : Term) : Set[Name] = collectConsts(term, Set())
  
  def collectConsts(term : Term, consts : Set[Name]) : Set[Name] = {
    term match {
      case Const(name) => consts + name
      case PolyConst(name, _) => consts + name
      case Comb(f, g) => collectConsts(g, collectConsts(f, consts))
      case Abs(_, _, body) => collectConsts(body, consts)
      case Var(_) => consts
    }
  }
  
  def mk_implies(hyp : Term, concl : Term) : Term = {
    Comb(Comb(Const(Kernel.implies), hyp), concl)
  }
  
  def mk_equals(ty : Type, left : Term, right : Term) : Term = {
    Comb(Comb(PolyConst(Kernel.equals, ty), left), right)    
  }
  
  def maxIndex(x : Option[Option[Integer]], y : Option[Option[Integer]]) : Option[Option[Integer]] = {
    (x, y) match {
      case (None, m) => m
      case (m, None) => m
      case (Some(x), Some(y)) =>
        (x, y) match {
          case (None, m) => Some(m)
          case (m, None) => Some(m)
          case (Some(x), Some(y)) => Some(Some(if (x > y) x else y))
        }
    }
  }
  
  def incIndex(x : Option[Option[Integer]]) : Option[Integer] = {
    x match {
      case None => None
      case Some(None) => Some(1)
      case Some(Some(x)) => Some(x + 1)
    }
  }
  
  def findHighestVarIndex(name : String, term : Term) : Option[Option[Integer]] = {
    term match {
      case Const(_) => None
      case PolyConst(_, _) => None
      case Comb(f, g) => 
        val fi = findHighestVarIndex(name, f)
        val gi = findHighestVarIndex(name, g)
        maxIndex(fi, gi)
      case Abs(varname, _, body) =>
        val vi = if (varname.name == name) Some(varname.index) else None
        val bi = findHighestVarIndex(name, body)
        maxIndex(vi, bi)
      case Var(varname) =>
        if (varname.name == name) Some(varname.index) else None
    }
  }
  
  // naive substitution, does not check for variable capture
  def substConst(term : Term, name : Name, substitute : Term) : Term = {
    term match {
      case Const(cname) if cname == name => substitute
      case Comb(f, g) => Comb(substConst(f, name, substitute), substConst(g, name, substitute))
      case Abs(x, ty, body) => Abs(x, ty, substConst(body, name, substitute))
      case _ => term
    }
  }
  
  def mk_abs(name : Name, ty : Type, prop : Term) : Term = {
    val index = incIndex(findHighestVarIndex(name.name.name, prop))
    val varname = IndexedName(name.name.name, index)
    Abs(varname, ty, substConst(prop, name, Var(varname)))
  }
  
  def mk_forall(name : Name, ty : Type, prop : Term) : Term = {
    Comb(PolyConst(Kernel.forall, ty), mk_abs(name, ty, prop))
  }
  
  def mk_exists(name : Name, ty : Type, prop : Term) : Term = {
    Comb(PolyConst(Kernel.exists, ty), mk_abs(name, ty, prop))
  }
    
  def subst(term : Term, substitution : Map[IndexedName, Term], vars : Set[IndexedName]) : Term = {
    term match {
      case Var(varname) =>
        substitution.get(varname) match {
          case Some(t) => t
          case None => term
        }
      case Comb(f, g) =>
        Comb(subst(f, substitution, vars), subst(g, substitution, vars))
      case Abs(varname, ty, body) =>
        if (vars.contains(varname)) {
          var name = varname.name
          var index : Integer = if (varname.index.isDefined) varname.index.get + 1 else 1   
          var newvarname : IndexedName = null
          do {
            newvarname = IndexedName(name, Some(index))
            index = index + 1
          } while (vars.contains(newvarname))
          Abs(newvarname, ty, subst(body, substitution + (varname -> Var(newvarname)), vars + newvarname))  
        } else {
          Abs(varname, ty, subst(body, substitution, vars + varname))
        }
      case _ => term
    }
  } 
  
  def substVar(term : Term, varname : IndexedName, sterm : Term) : Term = {
    subst(term, Map(varname -> sterm), freeVars(sterm) + varname)
  }
  
  def freeVars(term : Term, bVars : Set[IndexedName], fVars : Set[IndexedName]) : Set[IndexedName] = {
    term match {
      case Var(varname) =>
        if (bVars.contains(varname)) fVars else fVars + varname
      case Comb(f, g) =>
        freeVars(g, bVars, freeVars(f, bVars, fVars))
      case Abs(varname, _, body) =>
        freeVars(body, bVars + varname, fVars)
      case _ => fVars
    }    
  }
  
  def freeVars(term : Term) : Set[IndexedName] = freeVars(term, Set(), Set())
  
  def beta(term : Term) : Term = {
    term match {
      case Comb(Abs(x, ty, body), y) => substVar(body, x, y)
      case _ => failwith("term is not beta-reducible")
    }
  }
   
}