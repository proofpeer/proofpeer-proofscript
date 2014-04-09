package proofpeer.proofscript.logic

object Utils {

  def failwith[T](reason : String) : T = {
    throw new RuntimeException("Failure: " + reason)
  }
  
  type Integer = BigInt
  
  def str2Integer(s : String) : Integer = s.toInt  
  
}

import Utils._

sealed case class IndexedName(val name : String, val index : Option[Integer]) 
sealed case class Name(val namespace : Option[String], val name : IndexedName)

sealed abstract class Type
object Type {
  case object Universe extends Type
  case object Prop extends Type
  case class Fun(domain : Type, range : Type) extends Type
  case class TySet(set : Term) extends Type
  case class TyVar(n : Integer) extends Type
}

sealed abstract class Term 
object Term {
  case class Const(name : Name, ty : Type) extends Term 
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
    
  // Looks up the type of a constant.
  // A None result means that no such constant exists in this context. 
  def typeOfConst(const_name : Name) : Option[Type] 
  
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
  
  // Defines a new constant for which a given property holds. 
  // The property is given in the shape of an existential theorem.
  // The theorem may have leading all-quantifiers; in this case the constant will be skolemized. 
  // The names must either have no namespace, or must be equal to the current namespace.
  def choose(const_name : Name, thm_name : Name, thm : Theorem) : Theorem
   
  // Looks up the theorem with the given name.
  def lookupTheorem(thm_name : Name) : Option[Theorem]
  
  // Stores the theorem under the given name.
  // The name must either have no namespace, or must be equal to the current namespace.
  def storeTheorem(thm_name : Name, thm : Theorem) : Context
    
  // Converts a theorem into a theorem of this context (if possible). 
  def lift(thm : Theorem, preserve_structure : Boolean) : Theorem
  
  // Produces the theorem `a = a`
  def reflexive(a : Term) : Theorem
  
  // Produces the theorem `a = b`, where b results from a by a single beta reduction at the top
  def beta(a : Term) : Theorem 
  
  // Produces the theorem `a = b`, where b results from a by a single eta reduction at the top
  def eta(a : Term) : Theorem
  
  // Produces the theorem `a = c` from the theorems `a = b` and `b' = c`, where b and b' are alpha-equivalent
  def transitive(p : Theorem, q : Theorem) : Theorem
  
  // Produces the theorem `f a = g b` from the theorems `f = g` and `a = b`.
  def comb(p : Theorem, q : Theorem) : Theorem

  // Given a theorem `a` and either `a' = b` or `a' -> b`, produce the theorem `b` 
  def modusponens(p : Theorem, q : Theorem) : Theorem 
  
  // Given a theorem `forall x. a = b`, produces the theorem `(lambda x. a) = (lambda x. b)`
  def abs(p : Theorem) : Theorem
  
  // From theorems `a -> b` and `b' -> a'` produce theorem `a = b`
  def equiv(p : Theorem, q : Theorem) : Theorem
  
  // Instantiates the given all-quantified theorem. 
  def instantiate(p : Theorem, insts : List[Option[Term]]) : Theorem
  
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
  val implies = rootname("implies")
  
  private class TheoremImpl(val context : Context, val proposition : Term) extends Theorem
  
  def createDefaultKernel() : Kernel = new KernelImpl((c : Context, p : Term) => new TheoremImpl(c, p))
}
