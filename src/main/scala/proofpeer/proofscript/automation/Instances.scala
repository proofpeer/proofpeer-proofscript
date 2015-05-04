package proofpeer.proofscript.automation

import proofpeer.proofscript.logic._
import scala.language.implicitConversions
import scalaz.{ Name => _, _}
import Scalaz._

object KernelInstances {
  implicit object TermIsEqual extends Equal[Term] {
    override def equal(l: Term, r: Term) = l == r
  }
  implicit object NamespaceIsOrdered extends Order[Namespace] {
    override def equal(l: Namespace, r: Namespace) = l == r
    override def order(l: Namespace, r: Namespace) =
      (l.isAbsolute ?|? r.isAbsolute) |+| (l.components ?|? r.components)
  }
  implicit object IndexedNameIsOrdered extends Order[IndexedName] {
    override def equal(l: IndexedName, r: IndexedName) = l == r
    override def order(l: IndexedName, r: IndexedName) = {
      (l.name ?|? r.name) |+| (l.index ?|? r.index)
    }
  }
  // TODO: Temporarily poor show implementation
  implicit object IndexedNameIsShow extends Show[IndexedName] {
    override def show(n: IndexedName) = n.name.shows ++ n.index.shows
  }
  implicit object NameIsOrdered extends Order[Name] {
    override def equal(l: Name, r: Name) = l == r
    override def order(l: Name, r: Name) =
      (l.namespace ?|? r.namespace) |+| (l.name ?|? r.name)
  }
  implicit object NameIsShow extends Show[Name] {
    override def show(n: Name) = n.name.show
  }

  def bracket(str: Cord) = Cord("(") ++ str ++ Cord(")")

  implicit object TypeIsShow extends Show[Type] {
    override def show(ty: Type) =
      ty match {
        case Type.Universe       => "𝒰"
        case Type.Prop           => "ℙ"
        case Type.Fun(dom,codom) => bracket(dom.show ++ Cord("→") ++ codom.show)
      }
  }
  // TODO: Temporarily poor Term implementation, not even covering all cases.
  implicit object TermIsShow extends Show[Term] {
    override def show(t: Term) =
      t match {
        case Term.Var(IndexedName(name, index)) =>
          name.show ++ index.show
        case Term.PolyConst(name,ty) =>
          name.show ++ Cord(":") ++ ty.show
        case Term.Const(name)        => name.shows
        case Term.Abs(name,ty,body)  =>
          name.show ++ Cord(":") ++ ty.show ++ Cord(" ↦ ") ++ body.show
        case Term.Comb(rator,rand)   =>
          bracket(rator.show) ++ Cord(" ") ++ bracket(rand.show)
        case _ =>
          throw new RuntimeException("TermIsShow is not implemented yet for term: " + t)
      }
  }
}
