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
// trait Conversions[F[_,_]] extends Theory[F] {
//   // Nothing fancy for conversion exceptions. I might even demote this to Unit.
//   def FSisME: MonadError[F,String]
//   type ThyS[A] = Thy[String,A]
//   implicit def ev = ThyIsMonadError(FSisME)

//   type Conv = Kleisli[ThyS,Term,Thm]
//   case class RichConv(k: Conv) {
//     def apply(tm: Term): ThyS[Thm] = k.run(tm)

//     def destEquals(tm: Term) = dest_equals(tm) match {
//       case Some((lhs,rhs,ty)) => (lhs,rhs,ty).point[ThyS]
//       case None               =>
//         ev.raiseError(tm + " is not an equality")
//     }
//     def andThenC(conv: RichConv): RichConv = kleisli[ThyS,Term,Thm](tm =>
//       for (
//         thm1            <- this(tm);
//         eql             <- destEquals(thm1.proposition);
//         (lhs,rhs,ty)    =  eql;
//         thm2            <- conv(rhs);
//         eql_            <- destEquals(thm2.proposition);
//         (lhs_,rhs_,ty_) =  eql_;
//         err <- if (lhs_ == rhs_) ().point[ThyS]
//               else ev.raiseError[Unit]("andThen: " + lhs_ + " != " + rhs);
//         thm <- bindF(transitive(thm1,thm2)) { fx  }
//       )
//       yield thm
//     )
//   }

//   implicit def kleisliIsRichConv(k: Kleisli[ThyS, Term, Thm]): RichConv =
//     RichConv(k)

// }
//   object thenMonoid extends Monoid[Conv] {
//     def zero = kleisli[ThyS,Term,Thm](tm => reflexive(tm))
//     def append(x: Conv, y: => Conv) = (x andThenC y).run

//     def ConvLaws {
//       def thenZero[A](x: Conv, y: Conv, tm: Term)(implicit ev: IsEmpty[ThyS]):
//           Boolean =
//         ev.isEmpty((x andThenC zero)(tm))
//       // TODO: Could add distributivity laws over the monoid (<+>) for the
//       // Kleisli arrows.
//     }
//   }
// }
