package proofpeer.proofscript.logic

object Utils {

  def failwith[T](reason : String) : T = {
    throw new RuntimeException("Failure: " + reason)
  }
  
  type Integer = BigInt
  
  def str2Integer(s : String) : Integer = s.toInt  
  
}

import Utils._

sealed case class IndexedName(val name : String, val index : Option[Integer]) {
  override def toString : String = {
    if (index.isDefined) name + "_" + index.get else name
  }
}
sealed case class Name(val namespace : Option[Namespace], val name : IndexedName)

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

sealed trait ContextKind 
object ContextKind {
  case class Assume(assumption : Term) extends ContextKind
  case class Define(const_name : Name, ty : Type, tm : Term) extends ContextKind
  case class Choose(const_name : Name, ty : Type, property : Term) extends ContextKind
  case class Introduce(const_name : Name, ty : Type) extends ContextKind
  case class Created(namespace : Namespace, parentNamespaces : Set[Namespace], ancestorNamespaces : Set[Namespace]) extends ContextKind
  case object Complete extends ContextKind
}

trait Context {
  
  // The Kernel object that this Context was created by.
  def kernel : Kernel
  
  def kind : ContextKind

  // The namespace of the context.
  def namespace : Namespace
  
  // The namespaces that were used to create this (or its ancestor) context.
  def parentNamespaces : Set[Namespace]

  // The immediate parent context of this context.
  def parentContext : Option[Context]
    
  // Looks up the type of a constant.
  // A None result means that either no such constant exists in this context, 
  // or that the constant is polymorphic.
  def typeOfConst(const_name : Name) : Option[Type] 
  
  // Returns the type of the term if the term is valid in this context.
  def typeOfTerm(term : Term) : Option[Type]
  
  // Introduces a new unspecified constant.
  // The name must either have no namespace, or must be equal to the current namespace.
  def introduce(const_name : Name, ty : Type) : Context

  // Introduces an assumption with a given name. 
  // The name must either have no namespace, or must be equal to the current namespace.
  // The new context can be obtained from the theorem.
  def assume(assumption : Term) : Theorem
  
  // Defines a new constant. 
  // The name must either have no namespace, or it must be equal to the current namespace.
  def define(const_name : Name, tm : Term) : Theorem
  
  // Defines a new constant for which a given property holds. 
  // The property is given in the shape of an existential theorem.
  // The theorem may have leading all-quantifiers; in this case the constant will be skolemized. 
  // The name must either have no namespace, or it must be equal to the current namespace.
  def choose(const_name : Name, thm : Theorem) : Theorem
         
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

  // All constants of this context which are NOT constants of a parent namespace.
  def localConstants : Set[Name]
  
}

trait Kernel {
  
  def completedNamespaces : Set[Namespace]
  
  def contextOfNamespace(namespace : Namespace) : Option[Context]

  def parentsOfNamespace(namespace : Namespace) : Option[Set[Namespace]]

  def aliasesOfNamespace(namespace : Namespace) : Option[Aliases]
  
  def createNewNamespace(namespace : Namespace, parents : Set[Namespace], aliases : Aliases) : Context
  
  def completeNamespace(context : Context) : Context
  
}

object Kernel {
  val root_namespace = Namespace("\\root")
  def rootname(name : String) = Name(Some(root_namespace), IndexedName(name, None))
  
  def isPolymorphicName(name : Name) = {
    name == equals || name == forall || name == exists
  }

  // names which are essential to the kernel
  val equals = rootname("equals")  
  val forall = rootname("forall")
  val exists = rootname("exists")
  val implies = rootname("implies")
  
  // the other names in the root namespace
  val logical_and = rootname("and")
  val logical_or = rootname("or")
  val logical_not = rootname("not")
  val logical_true = rootname("true")
  val logical_false = rootname("false")
  val empty_set = rootname("empty")
  val set_difference = rootname("difference")
  val set_union = rootname("union")
  val set_intersection = rootname("intersection")
  val set_bigunion = rootname("Union")
  val set_bigintersection = rootname("Intersection")
  val set_power = rootname("power")
  val set_singleton = rootname("singleton")
  val set_separation = rootname("sep")
  val set_replacement = rootname("repl")
  val set_elementOf = rootname("elementof")
  val set_subsetOf = rootname("subsetof") 
  val fun = rootname("fun")
  val funapply = rootname("apply")
  val forallin = rootname("forallin")
  val existsin = rootname("existsin")
  val pair = rootname("pair")
    
  private class TheoremImpl(val context : Context, val proposition : Term) extends Theorem
  
  def createDefaultKernel() : Kernel = new KernelImpl((c : Context, p : Term) => new TheoremImpl(c, p))
}
