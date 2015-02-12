package proofpeer.proofscript.logic

import KernelUtils._
import scala.language.higherKinds
import scala.language.implicitConversions
import scalaz._
import Scalaz._
import Kleisli._
import EqualsInstances._

/** Conversions are Kleisli arrows Term => Thy[E,Theorem]. The intended semantics of
    conversions is given by its `thenMonoid`. */
trait Conversions[F[_,_],E] extends Theory[F,E] {
  // Sticking to really boring errors for conversions for now.
  def stringError: String => E

  type Conv = Kleisli[ThyE,Term,Thm]
  case class RichConv(k: Conv) {
    def apply(tm: Term): ThyE[Thm] = k.run(tm)

    def destEquals(tm: Term): ThyE[(Term,Term,Type)] = dest_equals(tm) match {
      case Some((lhs,rhs,ty)) => (lhs,rhs,ty).point[ThyE]
      case None               =>
        ThyIsMonadError.raiseError(stringError(tm + " is not an equality"))
    }
    def andThenC(conv: RichConv): RichConv = kleisli[ThyE,Term,Thm](tm =>
      for (
        thm1            <- this(tm);
        eql             <- destEquals(thm1.proposition);
        (lhs,rhs,ty)    =  eql;
        thm2            <- conv(rhs);
        eql_            <- destEquals(thm2.proposition);
        (lhs_,rhs_,ty_) =  eql_;
        err <- if (lhs_ == rhs_) ().point[ThyE]
               else ThyIsMonadError.raiseError[Unit](stringError(
                      "andThen: " + lhs_ + " != " + rhs));
        thm <- transitive(thm1,thm2)
      )
      yield thm
    )
  }

  implicit def kleisliIsRichConv(k: Kleisli[ThyE, Term, Thm]): RichConv =
    RichConv(k)

  object thenMonoid extends Monoid[Conv] {
    def zero = kleisli[ThyE,Term,Thm](tm => reflexive(tm))
    def append(x: Conv, y: => Conv) = (x andThenC y).k

    def ConvLaws {
      def thenZero[A](x: Conv, y: Conv, tm: Term)(implicit ev: IsEmpty[ThyE]):
          Boolean =
        ev.isEmpty((x andThenC zero)(tm))
      // TODO: Could add distributivity laws over the monoid (<+>) for the
      // Kleisli arrows.
    }
  }
}
