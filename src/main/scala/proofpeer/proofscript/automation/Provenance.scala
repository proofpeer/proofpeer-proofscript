package proofpeer.proofscript.metis

import scalaz._
import Scalaz._

/** Simple class decorating a value with its origin. */
case class Prov[X,A](origin: X, get: A)

object Provenence {
  implicit def ProvIsComonad[X] = new Comonad[({type λ[A] = Prov[X,A]})#λ] {
  override def copoint[A](x: Prov[X,A]) = x.get
  override def cobind[A,B](fa: Prov[X,A])(f: Prov[X,A] => B) =
    Prov(fa.origin,f(fa))
  override def map[A,B](fa: Prov[X,A])(f: A => B) =
    Prov(fa.origin,f(fa.get))
  }
  implicit def ProvIsEqual[X:Equal,A:Equal] = new Equal[Prov[X,A]] {
    override def equal(x: Prov[X,A], y: Prov[X,A]) = x == y
  }
  implicit def ProvIsShow[X:Show,A:Show] = new Show[Prov[X,A]] {
    override def show(x: Prov[X,A]) = {
      Cord("Prov(") ++ x.origin.show ++ Cord(",") ++ x.get.show ++ Cord(")")
    }
  }
}
