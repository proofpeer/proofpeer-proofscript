package proofpeer.proofscript.logic

sealed trait HOPattern
object HOPattern {

import Utils._

case class Const(name : Name, ty : Pretype) extends HOPattern
case class Var(name : IndexedName) extends HOPattern
case class MetaVar(name : Integer, ty : Pretype) extends HOPattern
case class Abs(x : IndexedName, ty : Pretype, body : HOPattern) extends HOPattern
case class Comb(f : HOPattern, g : HOPattern) extends HOPattern

// converts a term which is assumed to be valid in the context into a HOPattern
def term2HOP(context : Context, term : Term) : HOPattern = {
  term match {
    case c : Term.PolyConst => Const(c.name, Pretype.translate(context.typeOfTerm(c).get))
    case c : Term.Const => Const(c.name, Pretype.translate(context.typeOfTerm(c).get))
    case Term.Comb(f, g) => Comb(term2HOP(context, f), term2HOP(context, g))
    case Term.Abs(name, ty, body) => Abs(name, Pretype.translate(ty), term2HOP(context, body))
    case Term.Var(name) => Var(name)
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
    case Var(name) => Term.Var(name)
    case Abs(x, ty, body) => Term.Abs(x, Pretype.translate(ty), hop2Term(body))
    case Comb(f, g) => Term.Comb(hop2Term(f), hop2Term(g))
    case _ : MetaVar => failwith("cannot convert hop with meta variables to term")
  }
}

// takes a properly type inferred preterm (via Preterm.inferPolymorphicPreterm);
// all higherorder flags are supposed to be resolved;
// returns a HOPattern and a mapping from meta variable indices to corresponding quotations
def preterm2HOP(typingContext : Preterm.TypingContext, preterm : Preterm) 
  : (HOPattern, Map[Integer, Preterm.PTmQuote]) = 
{
  preterm2HOP(typingContext, preterm, Map())
}

private def preterm2HOP(typingContext : Preterm.TypingContext, preterm : Preterm, 
  quotes : Map[Integer, Preterm.PTmQuote]) : (HOPattern, Map[Integer, Preterm.PTmQuote]) = 
{
  import Preterm._
  preterm match {
    case PTmTyping(tm, _) => preterm2HOP(typingContext, tm, quotes)
    case PTmName(name, ty) => 
      typingContext.lookupPolymorphic(name, 0).get match {
        case (name, _, _, isVar) =>
          (if (isVar) Var(name.name) else Const(name, ty), quotes)
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
    case _ => throw new RuntimeException("preterm2HOP: internal error")
  }
}

def patternMatch(context : Context, hop : HOPattern, term : Term) : Option[Map[Integer, Term]] = {
  unify(hop, term2HOP(context, term)) match {
    case None => None
    case Some(subst) => Some(subst.mapValues(hop2Term))
  }
}

def unify(u : HOPattern, v : HOPattern) : Option[Map[Integer, HOPattern]] = {
  None
}

}