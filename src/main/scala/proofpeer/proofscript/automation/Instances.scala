package proofpeer.proofscript.automation

import proofpeer.proofscript.logic._
import scala.language.implicitConversions
import scalaz.{ Name => _, _}
import Scalaz._

object KernelInstances {
  implicit object TermIsEqual extends Equal[Term] {
    override def equal(l: Term, r: Term) = l == r
  }
  implicit object NameIsOrdered extends Order[Name] with Show[Name]{
    override def equal(l: Name, r: Name) = l == r
    override def order(l: Name, r: Name) = l ?|? r
    override def show(n: Name) = n.name.show
  }
  implicit object IndexedNameIsOrdered
      extends Order[IndexedName] with Show[IndexedName]{
    override def equal(l: IndexedName, r: IndexedName) = l == r
    override def order(l: IndexedName, r: IndexedName) = {
      (l.name ?|? r.name) |+| (l.index ?|? r.index)
    }
    override def show(n: IndexedName) = n.name
  }
}
