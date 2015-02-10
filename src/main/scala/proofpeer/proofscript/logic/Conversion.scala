package proofpeer.proofscript.logic

import KernelUtils._
import scala.language.higherKinds
import scala.language.implicitConversions
import scalaz._
import Scalaz._
import Kleisli._
import EqualsInstances._

/** Conversions are Kleisli arrows Term => M[String,Theorem], sending a
    term x to some F[E,Theorem], consisting of theorems in the given context of
    the form x = .... Errors of type E may be thrown.
  */
sealed class Conversions[F[_,_]](implicit
  errEv:  MonadError[F,String],
  plusEv: MonadPlus[({ type λ[A] = F[String,A]})#λ]) extends Conversions_[F] {
  override def theErrEv  = errEv
  override def thePlusEv = plusEv
}

trait Conversions_[F[_,_]] {
  case class M[E,A] private[Conversions_] (k: K[E,Context,A]) {
    def apply(ctx: Context) = k.run(ctx)
  }

  protected def theErrEv[E]:  MonadError[F,E]
  implicit protected def thePlusEv[E]: MonadPlus[({ type λ[A] = F[E,A]})#λ]

  private type K[E,C,A] = Kleisli[({type λ[A] = F[E,A]})#λ,C,A]

  implicit def mInstances[E] = new MIsError[E]

  private def kleisli_ [E,A](f: Context => F[E,A]) =
    Kleisli[({ type λ[A] = F[E,A] })#λ,Context,A](f)

  // Boiler plate makes me sad
  trait MIsMonadPlus[E] extends MonadPlus[({type λ[A] = M[E,A]})#λ] {
    private type FE[A] = F[E,A]
    private type KE[A] = Kleisli[FE,Context,A]
    private implicit val ev: MonadPlus[KE] = Kleisli.kleisliMonadPlus
    override def point[A](a: => A) = M(a.point[KE](implicitly(ev)))
    override def bind[A,B](fa: M[E,A])(f: A => M[E,B]) =
      M(fa.k >>= (x => f(x).k))
    override def plus[A](x: M[E,A], y: => M[E,A]) = M(x.k <+> y.k)
    override def empty[A] = M(mempty[KE,A](implicitly(ev)))
  }
  class MIsError[E] extends MIsMonadPlus[E] with MonadError[M,E] {
    private type FE[A]  = F[E,A]
    override def raiseError[A](e: E) =
      M(theErrEv.raiseError[A](e).liftKleisli[Context])
    override def handleError[A](fa: M[E,A])(handler: E => M[E,A]) =
      M(kleisli_ { ctx =>
        theErrEv.handleError(fa.k.run(ctx))(e => handler(e).k.run(ctx))
      })
  }

  // Hide the context reader.
  private def ask_[E]: M[E,Context] =
    M(kleisli_(ctx => thePlusEv.point(ctx)))

  private def scope_[E,A](ctx: Context, fa: M[E,A]) =
    M(kleisli_(_ => fa.k.run(ctx)))

  def liftF[E,A](x: F[E,A]): M[E,A] = M(kleisli_ { _ => x })

  /** Typical to just throw string-based errors. */
  type MS[A] = M[String,A]

  /** Nicer type-synonym */
  type Conv = Kleisli[MS,Term,Theorem]

  case class RichConv(run: Conv) {
    def apply(tm: Term): M[String,Theorem] = run.run(tm)

    def andThenC(conv: RichConv): RichConv = kleisli[MS,Term,Theorem](tm =>
      for (
        thm1                  <- this(tm);
        Some((lhs,rhs,ty))    <- dest_equals(thm1.proposition).point[MS];
        thm2                  <- conv(rhs);
        Some((lhs_,rhs_,ty_)) <- dest_equals(thm2.proposition).point[MS];
        err <- if (lhs_ == rhs_) ().point[MS]
        else mInstances[String].raiseError[Unit](
                "andThen: " + lhs_ + " != " + rhs);
        ctx                   <- ask_[String]
      )
      yield ctx.transitive(thm1,thm2)
    )
  }

  implicit def kleisliIsRichConv(k: Kleisli[MS, Term, Theorem]): RichConv
  = RichConv(k)

  object thenMonoid extends Monoid[Conv] {
    def zero = kleisli[MS,Term,Theorem](tm => ask_[String].map(_.reflexive(tm)))
    def append(x: Conv, y: => Conv) = (x andThenC y).run

    def ConvLaws {
      def thenZero[A](x: Conv, y: Conv, tm: Term)(implicit ev: IsEmpty[MS]):
          Boolean =
        ev.isEmpty((x andThenC zero)(tm))
      // TODO: Could add distributivity laws over the monoid (<+>) for the
      // Kleisli arrows.
    }
  }

  def combConv(ratorConv: Conv, randConv: Conv): Conv = kleisli[MS,Term,Theorem] { 
      case Term.Comb(rator, rand) =>
      ask_[String] >>= { ctx =>
        (ratorConv(rator) |@| randConv(rand)) { ctx.comb(_,_) } }
      case _ => mInstances[String].raiseError[Theorem]("not a combination");
    }

  def absConv(conv: Conv): Conv = kleisli[MS,Term,Theorem] {
    case Term.Abs(name, ty, body) =>
      for (
        ctx    <- ask_[String];
        bodCtx =  ctx.introduce(Name(None,name),ty);
        thm    <- conv(body) map { thm => bodCtx.abs(ctx.lift(thm)) })
      yield thm
    case _ => mInstances[String].raiseError[Theorem]("not an abstraction");
  }
}
