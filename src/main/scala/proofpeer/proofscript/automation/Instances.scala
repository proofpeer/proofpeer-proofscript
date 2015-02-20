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
  implicit object IndexedNameIsOrdered
      extends Order[IndexedName]{
    override def equal(l: IndexedName, r: IndexedName) = l == r
    override def order(l: IndexedName, r: IndexedName) = {
      (l.name ?|? r.name) |+| (l.index ?|? r.index)
    }
  }
  implicit object NameIsOrdered extends Order[Name] {
    override def equal(l: Name, r: Name) = l == r
    override def order(l: Name, r: Name) =
      (l.namespace ?|? r.namespace) |+| (l.name ?|? r.name)
  }
}
