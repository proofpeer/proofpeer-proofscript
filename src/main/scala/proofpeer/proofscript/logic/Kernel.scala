package proofpeer.proofscript.logic

object Utils {

  def failwith[T](reason : String) : T = {
    throw new RuntimeException("Failure: " + reason)
  }
  
  type Integer = BigInt
  
}

import Utils._

sealed case class IndexedName(val name : String, val index : Option[Integer]) 
sealed case class Name(val namespace : Option[String], val name : IndexedName)

sealed abstract class Type
object Type {
  case object Universe extends Type
  case object Prop extends Type
  case class Fun(domain : Type, range : Type) extends Type
}

sealed abstract class Term 
object Term {
  case class PolyConst(name : Name, alpha : Type) extends Term
  case class Const(name : Name) extends Term 
  case class Comb(f : Term, x : Term) extends Term 
  case class Abs(name : IndexedName, ty : Type, body : Term) extends Term 
  case class Var(name : IndexedName) extends Term
}

sealed trait Theorem {
  def context : Context
  def proposition : Term
}

trait Context {
  
  // The Kernel object that this Context was created by.
  def kernel : Kernel
  
  // The namespace of the context.
  def namespace : String
  
  // The namespaces that were used to create this (or its ancestor) context.
  def parentNamespaces : Set[String]
    
  // Returns the type of the constant. 
  // A None result means that either no such constant exists in this context, 
  // or that the constant is polymorphic.
  def typeOfConst(const_name : Name) : Option[Type] = 
    lookupConstant(const_name).map(_._1)
  
  // Returns the type of the term if the term is valid in this context.
  def typeOfTerm(term : Term) : Option[Type]
  
  // Introduces a new unspecified constant.
  // The name must either have no namespace, or must be equal to the current namespace.
  def introduce(const_name : Name, ty : Type) : Context

  // Introduces an assumption with a given name. 
  // The name must either have no namespace, or must be equal to the current namespace.
  // The new context can be obtained from the theorem.
  def assume(thm_name : Name, assumption : Term) : Theorem
  
  // Defines a new constant. 
  // The names must either have no namespace, or must be equal to the current namespace.
  def define(const_name : Name, thm_name : Name, tm : Term) : Theorem
   
  // Looks up the theorem with the given name.
  def lookupTheorem(thm_name : Name) : Option[Theorem]
  
  // Stores the theorem under the given name.
  // The name must either have no namespace, or must be equal to the current namespace.
  def storeTheorem(thm_name : Name, thm : Theorem) : Context
  
  // Looks up the type and (if existing) the theorem name of the definition of a constant.
  // A None result means that either no such constant exists in this context, 
  // or that the constant is polymorphic.
  def lookupConstant(const_name : Name) : Option[(Type, Option[Name])]
  
  // Converts a theorem into a theorem of this context (if possible). 
  def lift(thm : Theorem) : Theorem
  
}

trait Kernel {
  
  def completedNamespaces : Set[String]
  
  def contextOfNamespace(namespace : String) : Option[Context]
  
  def createNewNamespace(namespace : String, parents : Set[String]) : Context
  
  def completeNamespace(context : Context) : Context
  
}

object Kernel {
  val root_namespace = "root"
  def rootname(name : String) = Name(Some(root_namespace), IndexedName(name, None))
  
  val equals = rootname("equals")  
  val forall = rootname("forall")
  val exists = rootname("exists")
  val choose = rootname("choose")
  
  private class TheoremImpl(val context : Context, val proposition : Term) extends Theorem
  
  def createDefaultKernel() : Kernel = new KernelImpl((c : Context, p : Term) => new TheoremImpl(c, p))
}
