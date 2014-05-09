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
  
  def mk_equals(left : Term, right : Term, ty : Type) : Term = {
    Comb(Comb(PolyConst(Kernel.equals, ty), left), right)    
  }
  
  def dest_binop(term : Term) : (Name, Term, Term) = {
    term match {
      case Comb(Comb(Const(name), left), right) => (name, left, right)
      case _ => failwith("dest_binop: term is not a binary operation")
    }
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
  
  def incIndex(x : IndexedName) : IndexedName = {
    val index : Integer = 
      x.index match {
        case None => 1
        case Some(i) => i + 1
      }
    IndexedName(x.name, Some(index))
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

  def findHighestVarIndex(term : Term) : Option[Option[Integer]] = {
    term match {
      case Const(_) => None
      case PolyConst(_, _) => None
      case Comb(f, g) => 
        val fi = findHighestVarIndex(f)
        val gi = findHighestVarIndex(g)
        maxIndex(fi, gi)
      case Abs(varname, _, body) =>
        val vi = Some(varname.index)
        val bi = findHighestVarIndex(body)
        maxIndex(vi, bi)
      case Var(varname) =>
        Some(varname.index)
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
    
  // vars should contain all variables appearing free in substitution (including the keys)
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
    if (sterm == Var(varname))
      term
    else
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
  
  // Is equivalent to freeVars(term).contains(varname)
  def isFreeIn(name : IndexedName, term : Term) : Boolean = {
    term match {
      case Var(varname) => varname == name
      case Comb(f, g) => isFreeIn(name, f) || isFreeIn(name, g)
      case Abs(varname, _, body) => (varname != name) && isFreeIn(name, body)
      case _ => false
    }
  }
  
  def beta(term : Term) : Term = {
    term match {
      case Comb(Abs(x, ty, body), y) => substVar(body, x, y)
      case _ => failwith("beta: term is not reducible")
    }
  }
  
  def eta(term : Term) : Term = {
    term match {
      case Abs(x, ty, Comb(f, Var(y))) if x == y =>
        if (!isFreeIn(x, f)) 
          f
        else
          failwith("eta: variable appears free in function")
      case _ =>
        failwith("eta: term is not reducible")
    }
  }
  
  def dest_equals(term : Term) : (Term, Term, Type) = {
    term match {
      case Comb(Comb(PolyConst(Kernel.equals, ty), left), right) =>
        (left, right, ty)
      case _ => failwith("dest_equals: term is not an equality")
    }
  }
  
  def alpha_equivalent(u : Term, v : Term) : Boolean = {
    if (u == v) return true
    incIndex(maxIndex(findHighestVarIndex(u), findHighestVarIndex(v))) match {
      case None => false
      case Some(freshIndex) => alpha_equivalent(u, Map(), v, Map(), freshIndex)
    }
  }
  
  def alpha_equivalent(u : Term, su : Map[IndexedName, Integer], 
                       v : Term, sv : Map[IndexedName, Integer], 
                       freshIndex : Integer) : Boolean = 
  {
    (u, v) match {
      case (Var(uname), Var(vname)) =>
        (su.get(uname), sv.get(vname)) match {
          case (None, None) => uname == vname
          case (Some(i), Some(j)) => i == j
          case _ => false
        }
      case (Comb(fu, gu), Comb(fv, gv)) =>
        alpha_equivalent(fu, su, fv, sv, freshIndex) &&
        alpha_equivalent(gu, su, gv, sv, freshIndex)
      case (Abs(ux, uty, ubody), Abs(vx, vty, vbody)) =>
        if (ux == vx) {
          uty == vty && alpha_equivalent(ubody, su, vbody, sv, freshIndex)
        } else {
          uty == vty && alpha_equivalent(ubody, su + (ux -> freshIndex), vbody, sv + (vx -> freshIndex), freshIndex + 1)
        }
      case _ => u == v
    }
  }
  
  def is_forall(term : Term) : Boolean = {
    term match {
      case Comb(PolyConst(Kernel.forall, _), Abs(_, _, _)) => true
      case _ => false
    }    
  }
  
  def dest_forall(term : Term) : (IndexedName, Type, Term) = {
    term match {
      case Comb(PolyConst(Kernel.forall, _), Abs(x, ty, body)) => 
        (x, ty, body)
      case _ =>
        failwith("dest_forall: all-quantification expected")
    }
  }

  def is_exists(term : Term) : Boolean = {
    term match {
      case Comb(PolyConst(Kernel.exists, _), Abs(_, _, _)) => true
      case _ => false
    }    
  }

  def dest_exists(term : Term) : (IndexedName, Type, Term) = {
    term match {
      case Comb(PolyConst(Kernel.exists, _), Abs(x, ty, body)) => 
        (x, ty, body)
      case _ =>
        failwith("dest_exists: existential quantification expected")
    }
  }
  
  // assumes that hyp has no free variables
  def mk_implies_prenex(hyp : Term, concl : Term) : Term = {
    concl match {
      case Comb(PolyConst(Kernel.forall, _), Abs(x, ty, body)) => 
        Comb(PolyConst(Kernel.forall, ty), Abs(x, ty, mk_implies_prenex(hyp, body)))
      case Comb(PolyConst(Kernel.exists, _), Abs(x, ty, body)) => 
        Comb(PolyConst(Kernel.exists, ty), Abs(x, ty, mk_implies_prenex(hyp, body)))
      case _ =>
        var tm : Term = concl
        while (true) {
          tm match {
            case Comb(Comb(Const(Kernel.implies), p), q) =>
              if (alpha_equivalent(p, tm)) return concl else tm = q
            case _ =>
              return mk_implies(hyp, concl)
          }
        }
        failwith("internal error in mk_implies_prenex")
    }
  }  
  
  def strip_forall_unique(term : Term) : (List[(IndexedName, Type)], Term) = {
    val (_, qs, t) = strip_forall_unique(term, -1)
    (qs, t)
  }

  def strip_forall_unique(term_ : Term, max_ : Int) : (Set[IndexedName], List[(IndexedName, Type)], Term) = {
    var names : Set[IndexedName] = Set()
    var quantifiers : List[(IndexedName, Type)] = List()
    var term : Term = term_
    var max : Int = max_
    while (is_forall(term) && (max < 0 || max > 0)) {
      val (x, ty, tm) = dest_forall(term)
      var y = x
      while (names.contains(y)) {
        y = incIndex(y)
      }
      term = substVar(tm, x, Var(y))
      names = names + y
      quantifiers = (y, ty) :: quantifiers
      max = max - 1
    }
    (names, quantifiers.reverse, term)
  }
  
  def instantiate(context : Context, p : Term, insts : List[Option[Term]]) : Term = {
    val (names, quantifiers, term) = strip_forall_unique(p, insts.size)
    if (insts.size != quantifiers.size) failwith("instantiate: too many instantiations")
    var vars : Set[IndexedName] = names
    var substitution : Map[IndexedName, Term] = Map()
    var terms : List[Option[Term]] = insts
    var quants : List[(IndexedName, Type)] = quantifiers
    var notInstantiated : List[(IndexedName, Type)] = List()
    while (!quants.isEmpty) {
      val (x, xty) = quants.head
      terms.head match {
        case None =>
          notInstantiated = (x, xty) :: notInstantiated
        case Some(t) =>
          if (context.typeOfTerm(t) == Some(xty)) {
            vars = freeVars(t, Set(), vars)
            substitution = substitution + (x -> t)
          } else {
            failwith("instantiate: instantiation has wrong type / is not well-formed")
          }
      }
      quants = quants.tail
      terms = terms.tail
    }
    var prop : Term = subst(term, substitution, vars)
    for ((x, xty) <- notInstantiated) {
      prop = Comb(PolyConst(Kernel.forall, xty), Abs(x, xty, prop))
    }
    prop
  }
   
}