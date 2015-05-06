package proofpeer.proofscript.automation

import scalaz._
import Scalaz._

/** Provenance: simple class decorating a value with its origin. */
case class Prov[X,A] private (origin: X, get: A)

object Prov {
  implicit def ProvIsComonad[X] = new Comonad[({type λ[A] = Prov[X,A]})#λ] {
  override def copoint[A](x: Prov[X,A]) = x.get
  override def cobind[A,B](fa: Prov[X,A])(f: Prov[X,A] => B) =
    Prov(fa.origin,f(fa))
  override def map[A,B](fa: Prov[X,A])(f: A => B) =
    Prov(fa.origin,f(fa.get))
  }
  sealed abstract class ProvEqualInstance[X:Equal,A:Equal] extends Equal[Prov[X,A]] {
    override def equal(x: Prov[X,A], y: Prov[X,A]) =
      x.origin === y.origin && x.get === y.get
  }
  sealed abstract class ProvOrderInstance[X:Order,A:Order]
      extends ProvEqualInstance[X,A]
      with Order[Prov[X,A]] {
    override def order(x: Prov[X,A], y: Prov[X,A]) =
       (x.origin ?|? y.origin) |+| (x.get ?|? y.get)
    override def equal(x: Prov[X,A], y: Prov[X,A]) =
      super.equal(x,y)
  }
  implicit def ProvIsEqual[X:Equal,A:Equal] = new ProvEqualInstance[X,A] {}
  implicit def ProvIsOrder[X:Order,A:Order] = new ProvOrderInstance[X,A] {}
  implicit def ProvIsShow[X:Show,A:Show]    = new Show[Prov[X,A]] {
    override def show(x: Prov[X,A]) = {
      Cord("Prov(") ++ x.origin.show ++ Cord(",") ++ x.get.show ++ Cord(")")
    }
  }
  def originate[X](x: X) = Prov(x,x)
}
