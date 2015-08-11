package proofpeer.proofscript.logic

import proofpeer.general.Serializer
import proofpeer.proofscript.serialization.UniquelyIdentifiable
import proofpeer.proofscript.serialization.UniquelyIdentifiableStore

object Utils {

  class KernelException(val reason : String) extends RuntimeException(reason) 

  def failwith[T](reason : String) : T = {
    throw new KernelException("Failure: " + reason)
  }
  
  type Integer = BigInt
  
  def str2Integer(s : String) : Integer = s.toInt  
  
}

import Utils._

sealed case class IndexedName(val name : String, val index : Option[Integer]) extends UniquelyIdentifiable {
  override def toString : String = {
    if (index.isDefined) name + "_" + index.get else name
  }
}

sealed case class Name(val namespace : Option[Namespace], val name : IndexedName) extends UniquelyIdentifiable {
  override def toString : String = {
    if (namespace.isDefined) namespace.get + "\\" + name
    else name.toString
  }
}

sealed abstract class Type extends UniquelyIdentifiable
object Type {
  case object Universe extends Type
  case object Prop extends Type
  case class Fun(domain : Type, range : Type) extends Type
}

sealed abstract class Term extends UniquelyIdentifiable
object Term {
  case class PolyConst(name : Name, alpha : Type) extends Term
  case class Const(name : Name) extends Term 
  case class Comb(f : Term, x : Term) extends Term 
  case class Abs(name : IndexedName, ty : Type, body : Term) extends Term 
  case class Var(name : IndexedName) extends Term
}

sealed trait CTerm extends UniquelyIdentifiable {
  def context : Context
  def term : Term
  def typeOf : Type
  def normalform : Term
}

sealed trait Theorem extends UniquelyIdentifiable {
  def context : Context
  def proposition : Term
  def prop : CTerm
}

sealed trait ContextKind extends UniquelyIdentifiable
object ContextKind {
  case class Assume(assumption : Term) extends ContextKind
  case class Define(const_name : Name, ty : Type, tm : Term) extends ContextKind
  case class Choose(const_name : Name, ty : Type, property : Term) extends ContextKind
  case class Introduce(const_name : Name, ty : Type) extends ContextKind
  case class Created(namespace : Namespace, parentNamespaces : Set[Namespace], ancestorNamespaces : Set[Namespace]) extends ContextKind
  case object Complete extends ContextKind
}

trait Context extends UniquelyIdentifiable {
  
  // The Kernel object that this Context was created by.
  def kernel : Kernel
  
  def kind : ContextKind

  // The namespace of the context.
  def namespace : Namespace
  
  // The namespaces that were used to create this (or its ancestor) context.
  def parentNamespaces : Set[Namespace]

  // The immediate parent context of this context.
  def parentContext : Option[Context]

  // Certifies that a term is valid in this context.
  def certify(term : Term) : CTerm
    
  // Looks up the type of a constant.
  // A None result means that either no such constant exists in this context, 
  // or that the constant is polymorphic.
  def typeOfConst(const_name : Name) : Option[Type] 
  
  // Returns the type of the term if the term is valid in this context.
  def typeOfTerm(term : Term) : Option[Type]
  
  // Introduces a new unspecified constant.
  // The name must either have no namespace, or must be equal to the current namespace.
  def introduce(const_name : Name, ty : Type) : Context

  // Introduces an assumption. 
  // The new context can be obtained from the theorem.
  def assume(assumption : CTerm) : Theorem

  def assume(assumption : Term) : Theorem = assume(certify(assumption))

  def hasAssumptions : Boolean
  
  // Defines a new constant. 
  // The name must either have no namespace, or it must be equal to the current namespace.
  def define(const_name : Name, tm : CTerm) : Theorem 

  def define(const_name : Name, tm : Term) : Theorem =
    define(const_name, certify(tm))
  
  // Defines a new constant for which a given property holds. 
  // The property is given in the shape of an existential theorem.
  // The theorem may have leading all-quantifiers; in this case the constant will be skolemized. 
  // The name must either have no namespace, or it must be equal to the current namespace.
  def choose(const_name : Name, thm : Theorem) : Theorem
         
  // Converts a theorem into a theorem of this context (if possible). 
  def lift(thm : Theorem, preserve_structure : Boolean) : Theorem

  def lift(thm : Theorem) : Theorem = lift(thm, false)

  def lift(term : CTerm, preserve_structure : Boolean) : CTerm

  def lift(term : CTerm) : CTerm = lift(term, false)

  // Same as lift(term, false), but if the term actually changes then the lift fails
  def autolift(term : CTerm) : Option[CTerm] 
  
  // Produces the theorem `a = a`
  def reflexive(a : CTerm) : Theorem 

  def normalize(a : CTerm) : Theorem

  // Assuming that thm and prop are alpha-equivalent, returns a theorem with prop as proposition
  def normalize(thm : Theorem, prop : CTerm) : Theorem 
  
  // Creates a new constant name which is fresh for this context and resembles the given name
  def mkFresh(name : IndexedName) : IndexedName 

  // If abs is structurally an abstraction, destructs it
  // and returns (context, x, body), where context contains the constant x 
  // which corresponds to the variable that abs is abstracting over.
  def destAbs(abs : CTerm) : Option[(Context, CTerm, CTerm)]
  
  def destComb(comb : CTerm) : Option[(CTerm, CTerm)]

  // Produces the theorem `a = c` from the theorems `a = b` and `b' = c`, where b and b' are alpha-beta-eta-equivalent
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
  def instantiate(p : Theorem, insts : List[Option[CTerm]]) : Theorem

  // All constants of this context which are NOT constants of a parent namespace.
  def localConstants : Set[Name]  

  // Yep. Exactly. Don't use this.
  def magic(term : Term) : Theorem
}

trait KernelSerializers {

  def IndexedNameSerializer : Serializer[IndexedName]

  def NamespaceSerializer : Serializer[Namespace]

  def NameSerializer : Serializer[Name]

  def AliasSerializer : Serializer[Alias]

  def AliasesSerializer : Serializer[Aliases]

  def TypeSerializer : Serializer[Type]

  def TermSerializer : Serializer[Term]

  def ContextKindSerializer : Serializer[ContextKind]

  def ContextSerializer : Serializer[Context]

  def CTermSerializer : Serializer[CTerm]

  def TheoremSerializer : Serializer[Theorem] 

}

trait Kernel {
  
  def completedNamespaces : Set[Namespace]
  
  def contextOfNamespace(namespace : Namespace) : Option[Context]

  def parentsOfNamespace(namespace : Namespace) : Option[Set[Namespace]]

  def aliasesOfNamespace(namespace : Namespace) : Option[Aliases]
  
  def createNewNamespace(namespace : Namespace, parents : Set[Namespace], aliases : Aliases) : Context
  
  def completeNamespace(context : Context) : Context

  /** This is a back door into the kernel for serialisation purposes. 
    * Only use this if you know what you are doing as this violates the encapsulation of the kernel and makes
    * the creation of arbitrary contexts and theorems possible !!!
    */
  def serializers(store : UniquelyIdentifiableStore) : KernelSerializers
  def restoreCompletedNamespace(parents : Set[Namespace], aliases : Aliases, context : Context)

}

object Kernel {
  val root_namespace = Namespace("\\root")
  def rootname(name : String) = Name(Some(root_namespace), IndexedName(name, None))
  
  def isPolymorphicName(name : Name) = {
    name == equals || name == forall || name == exists
  }

  def destPolymorphicType(name : Name, ty : Type) : Option[Type] = {
    import Type._
    (name, ty) match {
      case (Kernel.equals, Fun(alpha, Fun(beta, Prop))) if alpha == beta =>
        Some(alpha)
      case (Kernel.forall, Fun(Fun(alpha, Prop), Prop)) =>
        Some(alpha)
      case (Kernel.exists, Fun(Fun(alpha, Prop), Prop)) =>
        Some(alpha)
      case _ => None
    }
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
    
  private class TheoremImpl(val prop : CTerm) extends Theorem {
    def context = prop.context
    def proposition = prop.term
  }

  private class CTermImpl(val context : Context, val term : Term, val typeOf : Type) extends CTerm {
    lazy val normalform : Term = KernelUtils.alphaNormalform(KernelUtils.betaEtaNormalform(term))
    private lazy val rep = List(normalform, typeOf)
    override def hashCode : Int = rep.hashCode
    override def equals(other : Any) : Boolean = {
      val otherTerm = other.asInstanceOf[CTermImpl]
      rep.equals(otherTerm.rep)
    }
  }
  
  def createDefaultKernel() : Kernel = new KernelImpl(
    (c : Context, p : Term) => new TheoremImpl(new CTermImpl(c, p, Type.Prop)),
    (c : Context, t : Term, ty : Type) => new CTermImpl(c, t, ty))

}
