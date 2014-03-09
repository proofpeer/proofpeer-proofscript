package proofpeer.proofscript.logic

object Utils {

  def failwith[T](reason : String) : T = {
    throw new RuntimeException("Failure: " + reason)
  }
  
}

import Utils._

sealed case class IndexedName(val name : String, val index : Option[Int]) 
sealed case class Name(val namespace : Option[String], val name : IndexedName)

sealed abstract class Type
object Type {
  case object Universe extends Type
  case object Prop extends Type
  case class Fun(domain : Type, range : Type) extends Type
}

sealed abstract class Term 
object Term {
  case class Const(name : Name, ty : Type) extends Term 
  case class Comb(f : Term, x : Term) extends Term 
  case class Abs(name : IndexedName, ty : Type, body : Term) extends Term 
  case class Var(name : IndexedName) extends Term
}

sealed case class Theorem(ctx : Context, hyps : Set[Term], concl : Term)

sealed trait Context {
  
  // The parent context, which is only null for the very first context.
  def parent : Context
  
  // The name of the current namespace.
  def currentNamespace : String
  
  // The completed namespaces.
  def completedNamespaces : Map[String, Context]
  
  // Starts a new namespace.
  def startNamespace(namespace : String) : Context
  
  // Checks if the given constant has the given type. 
  def constHasType(const_name : Name, ty : Type) : Boolean
  
  // Introduces an assumption with a given name. 
  // The name must either have no namespace, or must be equal to the current namespace.
  // Note that the context of the theorem is different from this context.
  def assume(thm_name : Name, assumption : Term) : Theorem
  
  // Defines a new constant.
  def define(const_name : Name, thm_name : Name, tm : Term) : Theorem
  
  // Introduces a new unspecified constant.
  def introduce(const_name : Name, ty : Type) : Context
  
  def lookupTheorem(thm_name : Name) : Option[Theorem]
  
  def storeTheorem(thm_name : Name, thm : Theorem) : Context
  
  def lookupConstant(const_name : Name) : Option[(Type, Option[(Name, Theorem)])]
  
  // Converts a theorem into a theorem of this context. 
  def lift(thm : Theorem) : Theorem
  
}

object Context {
  val root_namespace = "root"
  def rootname(name : String) = Name(Some(root_namespace), IndexedName(name, None))
  
  val equals = rootname("equals")  
  val forall = rootname("forall")
  val exists = rootname("exists")
  val choose = rootname("choose")
}

abstract class ContextImpl(private val constants : Map[Name, Type]) extends Context {
  
  def constHasType(name : Name, ty : Type) : Boolean = {
    import Type._
    name match {
      case Context.equals =>
        ty match {
          case Fun(alpha, Fun(beta, Prop)) if alpha == beta => true
          case _ => false
        }
      case Context.forall | Context.exists =>
        ty match {
          case Fun(Fun(_, Prop), Prop) => true
          case _ => false
        }
      case Context.choose =>
        ty match {
          case Fun(Fun(alpha, Prop), beta) if alpha == beta => true
          case _ => false
        }
      case _ =>
        constants.get(name) == Some(ty)
    }
  }
  
}

object AssocList {
  
  type L[K,V] = List[(K,V)]
  
  def empty[K,V] : L[K,V] = List()
  
  def lookup[K,V](list : L[K,V], k : K) : Option[V] = {
    for ((key, value) <- list) {
      if (key == k) return Some(value)
    }
    None
  }
  
  def assoc[K,V](list : L[K,V], k : K, v : V) : L[K, V] = (k,v) :: list
  
}

object Kernel {
  
  import Term._
  import Type._
      
  def isValidTerm(c : Context, vars : AssocList.L[IndexedName, Type], term : Term) : Option[Type] = {
    term match {
      case Const(name, ty) =>
        if (c.constHasType(name, ty)) Some(ty) else None
      case Var(name) =>
        AssocList.lookup(vars, name)
      case Comb(f, x) => 
        (isValidTerm(c, vars, f), isValidTerm(c, vars, x)) match {
          case (Some(Fun(fdomain, frange)), Some(xty)) if fdomain == xty =>
            Some(frange)
          case _ => None
        }
      case Abs(name, ty, body) =>
        isValidTerm(c, AssocList.assoc(vars, name, ty), body) match {
          case Some(bodyty) => Some(Fun(ty, bodyty))
          case None => None            
        }
    }
  }
  
  
  
  
  
}






