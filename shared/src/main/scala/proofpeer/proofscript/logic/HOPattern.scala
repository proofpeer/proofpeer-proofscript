package proofpeer.proofscript.logic

sealed trait HOPattern
object HOPattern {

import Utils._

case class Const(name : Name, ty : Pretype) extends HOPattern
case class Var(name : IndexedName, ty : Pretype) extends HOPattern
case class MetaVar(name : Integer, ty : Pretype) extends HOPattern
case class Abs(x : IndexedName, ty : Pretype, body : HOPattern) extends HOPattern
case class Comb(f : HOPattern, g : HOPattern) extends HOPattern

// converts a term which is assumed to be valid in the context into a HOPattern
// part of the conversion is beta-normalization, as HOPatterns must be in beta-normalform by definition
def term2HOP(context : Context, term : Term) : HOPattern = {
  term2HOP(context, KernelUtils.betaNormalform(term), Map())
}

private def term2HOP(context : Context, term : Term, vars : Map[IndexedName, Pretype]) : HOPattern = {
  term match {
    case c : Term.PolyConst => Const(c.name, Pretype.translate(context.typeOfTerm(c).get))
    case c : Term.Const => Const(c.name, Pretype.translate(context.typeOfTerm(c).get))
    case Term.Comb(f, g) => Comb(term2HOP(context, f, vars), term2HOP(context, g, vars))
    case Term.Abs(name, ty, body) => 
      val pty = Pretype.translate(ty)
      Abs(name, pty, term2HOP(context, body, vars + (name -> pty)))
    case Term.Var(name) => Var(name, vars(name))
  }  
}

// converts a hopattern which has no metavars or type variables
def hop2Term(term : HOPattern) : Term = {
  term match {
    case Const(name, ty) =>
      Kernel.destPolymorphicType(name, Pretype.translate(ty)) match {
        case None => Term.Const(name)
        case Some(alpha) => Term.PolyConst(name, alpha)
      }
    case Var(name, _) => Term.Var(name)
    case Abs(x, ty, body) => Term.Abs(x, Pretype.translate(ty), hop2Term(body))
    case Comb(f, g) => Term.Comb(hop2Term(f), hop2Term(g))
    case _ : MetaVar => failwith("cannot convert hop with meta variables to term")
  }
}

// takes a properly type inferred preterm (via Preterm.inferPolymorphicPreterm);
// all higherorder flags are supposed to be resolved;
// returns a HOPattern and a mapping from meta variable indices to corresponding quotations,
// and a mapping from type variable indices to corresponding quotations
def preterm2HOP(typingContext : Preterm.TypingContext, preterm : Preterm) 
  : (HOPattern, Map[Integer, Preterm.PTmQuote]) = 
{
  preterm2HOP(typingContext, preterm, Map())
}

private def pretype2Pattern(pretype : Pretype, quotes : Map[Integer, Pretype.PTyQuote]) : 
  (Pretype, Map[Integer, Pretype.PTyQuote]) =
{
  val (pattern, _, q) = Pretype.removeAny(pretype, quotes.size, quotes)
  (pattern, q)
}

private def preterm2HOP(typingContext : Preterm.TypingContext, preterm : Preterm, 
  quotes : Map[Integer, Preterm.PTmQuote]) : (HOPattern, Map[Integer, Preterm.PTmQuote]) = 
{
  import Preterm._
  preterm match {
    case PTmTyping(tm, ty) => preterm2HOP(typingContext, tm, quotes)
    case PTmName(name, ty) => 
      typingContext.lookupPolymorphic(name, 0).get match {
        case (name, _, _, isVar) =>
          (if (isVar) Var(name.name, ty) else Const(name, ty), quotes)
      }
    case PTmAbs(x, ty, body, _) =>
      val (newBody, newQuotes) = preterm2HOP(typingContext.addVar(x, ty), body, quotes)
      (Abs(x, ty, newBody), newQuotes)
    case PTmComb(f, g, higherorder, _) =>
      val (newF, newQuotes1) = preterm2HOP(typingContext, f, quotes)
      val (newG, newQuotes2) = preterm2HOP(typingContext, g, newQuotes1)
      val comb = 
        if (higherorder.get) Comb(newF, newG)
        else {
          import Pretype._
          val funapply_ty = PTyFun(PTyUniverse, PTyFun(PTyUniverse, PTyUniverse))
          Comb(Comb(Const(Kernel.funapply, funapply_ty), newF), newG)
        }
      (comb, newQuotes2)
    case q @ PTmQuote(_, ty) =>
      val id : Integer = quotes.size
      (MetaVar(id, ty), quotes + (id -> q))
    case tm : PTmTerm => (term2HOP(typingContext.targetContext, tm.tm), quotes)
    case _ => throw new RuntimeException("preterm2HOP: internal error")
  }
}

// Checks if a HOPattern (which resulted from preterm2HOP) is an actual HOPattern,
// i.e. beta-normalized and metavars only applied to distinct bound variables.
// Note that this function does not check other necessary properties which are guaranteed when resulting
// from preterm2HOP, like no unbound variables, etc.
def isHOPattern(pattern : HOPattern) : Boolean = {
  pattern match {
    case Abs(_, _, body) => isHOPattern(body)
    case c : Comb => 
      strip(c) match {
        case (_ : Abs, _ :: args) => false
        case (_ : MetaVar, args) =>
          var names : Set[IndexedName] = Set()
          for (arg <- args) {
            arg match {
              case Var(name, _) if !names.contains(name) =>
                names = names + name
              case _ => 
                return false
            }
          }
          true
        case (p, ps) => (p::ps).forall(isHOPattern _)
      }
    case _ => true
  }
}


def patternMatch(context : Context, hop : HOPattern, term : Term) : Either[(Map[Integer, Term], Map[Integer, Pretype]), Boolean] = {
  unify(hop, term2HOP(context, term)) match {
    case Left((subst, typeSubst)) => Left(subst.mapValues(hop2Term), typeSubst)
    case Right(invalid) => Right(invalid)
  }
}

def patternMatch(context : Context, hop : HOPattern, term_ : CTerm) : Either[(Map[Integer, CTerm], Map[Integer, Pretype]), Boolean] = {
  val term = context.lift(term_)
  patternMatch(context, hop, term.term) match {
    case Right(invalid) => Right(invalid)
    case Left((subst, typeSubst)) =>
      val csubst = subst.mapValues(t => context.certify(t))
      Left((csubst, typeSubst))
  }
}


def unify(u : HOPattern, v : HOPattern) : Either[(Map[Integer, HOPattern], Map[Integer, Pretype]), Boolean] = {
  val alg = new Unification()
  try {
    val (subst, typeSubst) = alg.unify(u, v)
    Left(subst, typeSubst)
  } catch {
    case alg.Fail => Right(false)
    case alg.InvalidPattern => Right(true)
    case alg.InvalidPatternType => Right(true)
  }
}

def instTypeVars(u : HOPattern, typeSubst : Integer => Option[Pretype]) : HOPattern = {
  u match {
    case Var(name, ty) => Var(name, Pretype.subst(typeSubst, ty))
    case MetaVar(name, ty) => MetaVar(name, Pretype.subst(typeSubst, ty))
    case Const(name, ty) => Const(name, Pretype.subst(typeSubst, ty))
    case Abs(x, ty, body) => Abs(x, Pretype.subst(typeSubst, ty), instTypeVars(body, typeSubst))
    case Comb(f, g) => Comb(instTypeVars(f, typeSubst), instTypeVars(g, typeSubst))
  }
}

private def strip(u : HOPattern) : (HOPattern, List[HOPattern]) = {
  strip(u, List())
}

private def strip(u : HOPattern, us : List[HOPattern]) : (HOPattern, List[HOPattern]) = {
  u match {
    case Comb(f, g) => strip(f, g::us)
    case _ => (u, us) 
  }
}

private class Unification {
  var highestMetaIndex : Integer = 0
  var highestVars : Map[String, Integer] = Map()
  var typeEquations : Set[(Pretype, Pretype)] = Set()

  type Substitution = List[(Integer, HOPattern)]

  case object Fail extends RuntimeException
  case object InvalidPattern extends RuntimeException
  case object InvalidPatternType extends RuntimeException

  private def register(metaVarIndex : Integer) {
    if (highestMetaIndex < metaVarIndex)
      highestMetaIndex = metaVarIndex
  }

  private def register(x : IndexedName) {
    val index : Integer = if (x.index.isDefined) x.index.get else 0
    highestVars.get(x.name) match {
      case Some(i) if i >= index => // do nothing
      case _ => highestVars = highestVars + (x.name -> index)
    }
  }

  private def register(u : HOPattern) {
    u match {
      case Var(x, _) => register(x)
      case MetaVar(index, _) => register(index)
      case Abs(x, ty, body) => register(x); register(body)
      case Comb(f, g) => register(f); register(g)
      case Const(_, _) => // do nothing
    }  
  }

  private def freshMetaVar : MetaVar = {
    highestMetaIndex = highestMetaIndex + 1
    MetaVar(highestMetaIndex, Pretype.PTyAny)
  }

  private def freshName(name : String) : IndexedName = {
    val indexedName = 
      highestVars.get(name) match {
        case None => IndexedName(name, None)
        case Some(i) => IndexedName(name, Some(i+1))
      }
    register(indexedName)
    indexedName
  }

  private def typeOf(u : HOPattern) : Pretype = {
    u match {
      case Var(_, ty) => ty
      case Const(_, ty) => ty
      case MetaVar(_, ty) => ty
      case Comb(f, g) => 
        (typeOf(f), typeOf(g)) match {
          case (Pretype.PTyFun(a, b), c) if a == c => b
          case _ => throw InvalidPatternType
        }
      case Abs(x, ty, body) => Pretype.PTyFun(ty, typeOf(body))
    }
  }

  private def addTypeEquation(u : Pretype, v : Pretype) {
    if (u != v && u != Pretype.PTyAny && v != Pretype.PTyAny) 
      typeEquations = typeEquations + (u -> v)
  }

  private def flatten(theta : Substitution, u : HOPattern) : HOPattern = {
    u match {
      case MetaVar(m, ty) =>
        lookup(m, theta) match {
          case None => u
          case Some(u) => flatten(theta, u)
        }
      case Abs(x, ty, body) => Abs(x, ty, flatten(theta, body))
      case Comb(f, g) => Comb(flatten(theta, f), flatten(theta, g))
      case _ => u
    }
  }

  private def asMap(subst : Substitution, typeSubst : Integer => Option[Pretype]) : Map[Integer, HOPattern] = {
    // to be implemented: convert lazy substitution into strict substitution
    var m : Map[Integer, HOPattern] = Map()
    for ((i, p) <- subst) {
      val q = flatten(subst, p)
      m = m + (i -> instTypeVars(q, typeSubst))
    }
    m
  }

  private def reduce(u : HOPattern, ts : List[HOPattern]) : HOPattern = {
    (u, ts) match {
      case (Abs(x, ty, body), t :: ts) =>
        reduce(substVar(body, x, t), ts)
      case (u, t :: ts) =>
        reduce(Comb(u, t), ts)
      case (u, List()) => u  
    }
  }

  private def devar(theta : Substitution, u : HOPattern) : HOPattern = {
    strip(u) match {
      case (f : MetaVar, ts) => 
        lookup(f.name, theta) match {
          case None => u
          case Some(t) => devar(theta, reduce(t, ts))
        }
      case _ => u
    }
  }

  // substitutes Var(x) by Var(y), where y must be fresh
  private def substVar(u : HOPattern, x : IndexedName, y : IndexedName) : HOPattern = {
    u match {
      case Var(v, ty) if v == x => Var(y, ty)
      case Abs(v, ty, body) =>
        if (v == x) u
        else Abs(v, ty, substVar(body, x, y))
      case Comb(f, g) =>
        Comb(substVar(f, x, y), substVar(g, x, y))
      case _ => u
    }
  }

  private def isFreeIn(x : IndexedName, u : HOPattern) : Boolean = {
    u match {
      case Var(v, _) => v == x
      case Abs(v, _, body) =>
        if (v == x) false
        else isFreeIn(x, body)
      case Comb(f, g) =>
        isFreeIn(x, f) || isFreeIn(x, g)
      case _ => false
    }
  }

  private def substVar(u : HOPattern, x : IndexedName, y : HOPattern) : HOPattern = {
    u match {
      case Var(v, _) if v == x => y
      case Abs(v, ty, body) => 
        if (v == x) u
        else if (!isFreeIn(v, y))
          Abs(v, ty, substVar(body, x, y))
        else {
          val w = freshName(v.name)
          Abs(w, ty, substVar(substVar(body, v, w), x, y))
        } 
      case Comb(f, g) => Comb(substVar(f, x, y), substVar(g, x, y))
      case _ => u
    }
  }

  private def isRigid(u : HOPattern) : Boolean = {
    u match {
      case _ : Var => true
      case _ : Const => true
      case _ => false
    }
  }

  private def forceHOP(xs : List[HOPattern]) : List[Var] = {
    var vars : List[Var] = List()
    var names : Set[IndexedName] = Set()
    for (x <- xs) {
      x match {
        case x : Var =>
          if (names.contains(x.name)) throw InvalidPattern 
          vars = x :: vars
          names = names + x.name
        case _ => throw InvalidPattern
      }
    }
    vars.reverse
  }

  private def filterEqualPlaces(_fs : List[Var], _gs : List[Var]) : List[Var] = {
    var fs = _fs
    var gs = _gs
    var hs : List[Var] = List()
    while (!fs.isEmpty) {
      val f = fs.head
      val g = gs.head
      if (f.name == g.name) hs = f :: hs
      fs = fs.tail
      gs = gs.tail
    }
    hs.reverse
  }

  private def varsetOf(fs : List[Var]) : Set[IndexedName] = {
    fs.map(_.name).toSet
  }

  private def lookupVar(f : IndexedName, xs : List[Var]) : Option[Var] = {
    for (x <- xs) {
      if (x.name == f) return Some(x)
    }
    None
  }

  private def lookupVars(indices : Set[IndexedName], xs : List[Var]) : List[Var] = {
    var ys : List[Var] = List()
    for (index <- indices) {
      lookupVar(index, xs) match {
        case Some(y) => y :: ys
        case None => // do nothing
      }
    }
    ys.reverse
  }

  private def lambda(xs : List[Var], h : HOPattern, hs : List[Var]) : HOPattern = {
    var t : HOPattern = h
    for (h <- hs) {
      t = Comb(t, h)
    }
    for (x <- xs.reverse) {
      t = Abs(x.name, x.ty, t)
    }
    t
  }

  private def flexflex1(theta : Substitution, f : MetaVar, fs : List[Var], gs : List[Var]) : Substitution =
  {
    if (fs.size != gs.size)
      throw Fail
    else {
      if (fs == gs) theta
      else {
        val hs = filterEqualPlaces(fs, gs)
        val h = freshMetaVar
        (f.name -> lambda(fs, h, hs)) :: theta
      }
    }
  }
  
  private def flexflex2(theta : Substitution, f : MetaVar, fs : List[Var],
    g : MetaVar, gs : List[Var]) : Substitution =
  {
    val xs = varsetOf(fs)
    val ys = varsetOf(gs)
    if (xs subsetOf ys) {
      (g.name -> lambda(gs, f, fs)) :: theta
    } else if (ys subsetOf xs) {
      (f.name -> lambda(fs, g, gs)) :: theta
    } else {
      val zs = (xs intersect ys)
      val h = freshMetaVar
      val hs = lookupVars(zs, fs)
      (f.name -> lambda(fs, h, hs)) :: (g.name -> lambda(gs, h, hs)) :: theta
    }
  }

  private def flexflex(theta : Substitution, f : MetaVar, fs : List[Var],
    g : MetaVar, gs : List[Var]) : Substitution =
  {
    addTypeEquation(f.ty, g.ty)
    if (f.name == g.name)
      flexflex1(theta, f, fs, gs)
    else
      flexflex2(theta, f, fs, g, gs)
  }

  private def lookup(f : Integer, theta : Substitution) : Option[HOPattern] = {
    for ((v, p) <- theta) {
      if (f == v) return Some(p)
    }
    return None
  }

  private def occurs(f : Integer, theta : Substitution,  u : HOPattern) : Boolean = {
    u match {
      case MetaVar(i, _) => 
        f == i || (
          lookup(i, theta) match {
            case None => false
            case Some(p) => occurs(f, theta, p)
          })
      case Comb(u, v) => occurs(f, theta, u) || occurs(f, theta, v)
      case Abs(_, _, body) => occurs(f, theta, body)
      case _ : Const => false
      case _ : Var => false
    }
  }

  private def proj(varnames : Set[IndexedName], theta : Substitution, t : HOPattern) : Substitution = {
    strip(devar(theta, t)) match {
      case (Abs(x, ty, body), List()) => proj(varnames + x, theta, body)
      case (_ : Const, ts) => proj(varnames, theta, ts)
      case (Var(v, _), ts) => 
        if (varnames.contains(v)) 
          proj(varnames, theta, ts) 
        else
          throw Fail
      case (f : MetaVar, ts) =>
        val xs = forceHOP(ts)
        val zs = varsetOf(xs) intersect varnames
        val hs = lookupVars(zs, xs)
        val h = freshMetaVar
        (f.name -> lambda(xs, h, hs)) :: theta
      case _ => 

        throw InvalidPattern
    }
  }

  private def proj(varnames : Set[IndexedName], _theta : Substitution, ts : List[HOPattern]) : Substitution = {
    var theta = _theta
    for (t <- ts) {
      theta = proj(varnames, theta, t)
    }
    theta
  }

  private def flexrigid(theta : Substitution, f : MetaVar, fs : List[Var],
    t : HOPattern) : Substitution =
  {
    if (occurs(f.name, theta, t)) throw Fail
    proj(varsetOf(fs), (f.name -> lambda(fs, t, List()))::theta, t)
  }

  private def rigidrigid(theta : Substitution, f : HOPattern, fs : List[HOPattern],
    g : HOPattern, gs : List[HOPattern]) : Substitution =
  {
    (f, g) match {
      case (Var(x, _), Var(y, _)) if x == y =>
        unify(theta, fs, gs)
      case (Const(x, x_ty), Const(y, y_ty)) if x == y =>
        addTypeEquation(x_ty, y_ty)
        unify(theta, fs, gs)
      case _ => throw Fail
    }
  }

  private def unify(theta : Substitution, u : HOPattern, v : HOPattern) : Substitution = {
    (devar(theta, u), devar(theta, v)) match {
      case (Abs(x, x_ty, x_body), Abs(y, y_ty, y_body)) if x == y =>
        unify(theta, x_body, y_body)
      case (Abs(x, x_ty, x_body), Abs(y, y_ty, y_body)) =>
        val z = freshName(x.name)
        unify(theta, substVar(x_body, x, z), substVar(y_body, y, z))
      case (Abs(x, ty, body), t) =>
        unify(theta, body, Comb(t, Var(x, ty)))
      case (t, Abs(x, ty, body)) =>
        unify(theta, Comb(t, Var(x, ty)), body)
      case (u, v) => 
        (strip(u), strip(v)) match {
          case ((f : MetaVar, fs), (g : MetaVar, gs)) => flexflex(theta, f, forceHOP(fs), g, forceHOP(gs))
          case ((f : MetaVar, fs), _) => flexrigid(theta, f, forceHOP(fs), v)
          case (_, (g : MetaVar, gs)) => flexrigid(theta, g, forceHOP(gs), u)
          case ((f, fs), (g, gs)) if isRigid(f) && isRigid(g) => rigidrigid(theta, f, fs, g, gs)
          case _ => throw InvalidPattern
        }
    }
  }

  private def unify(_theta : Substitution, _fs : List[HOPattern], _gs : List[HOPattern]) : Substitution = {
    var fs = _fs
    var gs = _gs
    if (fs.size != gs.size) throw Fail
    var theta = _theta
    while (!fs.isEmpty) {
      theta = unify(theta, fs.head, gs.head)
      fs = fs.tail
      gs = gs.tail
    }
    theta
  }

  def unify(u : HOPattern, v : HOPattern) : (Map[Integer, HOPattern], Map[Integer, Pretype]) = {
    register(u)
    register(v)
    addTypeEquation(typeOf(u), typeOf(v))
    val subst = unify(List(), u, v)
    val typeSubst = Pretype.solve(typeEquations)
    if (typeSubst == null) throw Fail
    (asMap(subst, i => typeSubst.get(i)), typeSubst)
  }

}


}