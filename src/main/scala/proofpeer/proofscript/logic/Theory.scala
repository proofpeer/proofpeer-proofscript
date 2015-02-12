package proofpeer.proofscript.logic

import KernelUtils._
import scala.language.higherKinds
import scala.language.implicitConversions
import scalaz._
import Scalaz._
import Kleisli._
import EqualsInstances._
import Utils.KernelException

/** `Theory` exposes inference rules without reference to contexts. The core type is
  * `Theory.Thy`, whose interface is at least that of a MonadError capable of
  *  throwing KernelException, plus versions of the kernel rules.
  *
  * @tparam `F` An instance of both [[scalaz.MonadError] for KernelException and
  * (when partially applied to KernelException) [[scalaz.Monad]].
  */
trait Theory[F[_,_]] {
  def kernel: Kernel
  def FKisME: MonadError[F,KernelException]
  implicit def FKisM: Monad[({ type λ[A] = F[KernelException,A]})#λ]

  // Wrap theorems to limit access to contexts.
  class Thm private[Theory](private[Theory] val get: Theorem) {
    val proposition = get.proposition
  }

  private def kleisli_ [E,A](f: Context => F[E,A]) =
    Kleisli[({ type λ[A] = F[E,A] })#λ,Context,A](f)

  // Context is automatically threaded through computations (using Kleisli arrows
  // of F). We hide the arrows to keep them out of reach of client code and those
  // extending Theory. The intention here is that all uses of Context.lift will
  // go through.
  sealed class Thy[E,A] private[Theory] (
    private[Theory] val k: Kleisli[({type λ[A] = F[E,A]})#λ,Context,A]) {
    def apply(ctx: Context): F[E,A] = k.run(ctx)
  }

  implicit def ThyIsMonad[E](implicit ev: Monad[({type λ[A] = F[E,A]})#λ]) =
    new ThyIsMonad[E] {
      override def FEisM = ev
    }
  implicit def ThyIsMonadPlus[E](implicit ev: MonadPlus[({type λ[A] = F[E,A]})#λ]) =
    new ThyIsMonadPlus[E] {
      override def FEisMP = ev
    }
  implicit def ThyIsMonadError[E](implicit ev: MonadError[F,E]) =
    new ThyIsMonadError[E] with ThyIsMonad[E] {
      override def FEisME = ev
      override def FEisM  = ev 
    }

  // Boiler plate makes me sad
  trait ThyIsMonad[E] extends Monad[({type λ[A] = Thy[E,A]})#λ] {
    implicit def FEisM: Monad[({ type λ[A] = F[E,A]})#λ]

    private type FE[A] = F[E,A]
    private type KE[A] = Kleisli[FE,Context,A]
    private implicit val ev: Monad[KE] = Kleisli.kleisliMonadReader
    import ev.monadSyntax._
    override def point[A](a: => A) = new Thy(ev.point(a))
    override def bind[A,B](fa: Thy[E,A])(f: A => Thy[E,B]) =
      new Thy(fa.k >>= (f(_).k))

    def liftF[E,A](x: F[E,A]): Thy[E,A] = new Thy(kleisli_ { _ => x })

    def bindF[A,B](x: Thy[E,A])(f: F[E,A] => Thy[E,B]): Thy[E,B] =
      new Thy(kleisli_ { ctx => f(x.k.run(ctx)).k.run(ctx) })

    def mapError[E2,A](x: Thy[E,A])(f: F[E,A] => F[E2,A]): Thy[E2,A] =
        new Thy(kleisli_{ ctx: Context => f(x.k.run(ctx)) })
  }
  trait ThyIsMonadPlus[E]
      extends ThyIsMonad[E] with MonadPlus[({type λ[A] = Thy[E,A]})#λ] {
    def FEisMP: MonadPlus[({ type λ[A] = F[E,A]})#λ]

    override def FEisM = FEisMP
    private type FE[A] = F[E,A]
    private type KE[A] = Kleisli[FE,Context,A]
    private implicit val ev: MonadPlus[KE] =
      Kleisli.kleisliMonadPlus[FE,Context](FEisMP)
    override def empty[A] = new Thy(ev.empty)
    override def plus[A](x: Thy[E,A], y: => Thy[E,A]) = new Thy(ev.plus(x.k,y.k))
  }
  trait ThyIsMonadError[E] extends MonadError[Thy,E] {
    def FEisME: MonadError[F,E]

    private implicit def FEisM: Monad[({ type λ[A] = F[E,A]})#λ] = FEisME
    private type FE[A]  = F[E,A]
    override def raiseError[A](e: E) =
      new Thy(FEisME.raiseError[A](e).liftKleisli[Context])
    override def handleError[A](fa: Thy[E,A])(handler: E => Thy[E,A]) =
      new Thy(kleisli_ { ctx =>
        FEisME.handleError(fa.k.run(ctx))(e => handler(e).k.run(ctx))
      })

    /** Run this `Theory` in the supplied [[proofpeer.proofscript.logic.Namespace]].
      */
    def run[Fold[_]:Foldable](mthm: Thy[E,Thm])(
      namespace: Namespace, parents: Fold[Namespace]): F[E,Theorem] = {
      val parentSet = parents.foldLeft[Set[Namespace]](Set()) { _ + _ }
      val ctx = kernel.createNewNamespace(
        namespace,
        parentSet,
        new Aliases(namespace, List()))
      mthm(ctx).map{_.get}
    }
   }

  type ThyK[A] = Thy[KernelException,A]
  implicit object ThyKInstances extends ThyKIsMonad with ThyKIsMonadError

  trait ThyKIsMonad extends ThyIsMonad[KernelException] {
    override def FEisM = FKisM
  }
  trait ThyKIsMonadError extends ThyKIsMonad with ThyIsMonadError[KernelException] {
    override def FEisME = FKisME
  }
  trait ThyKIsMonadPlus extends ThyIsMonadPlus[KernelException]

  // Context access.
  private def ask_ : Thy[KernelException,Context] =
    new Thy(kleisli_(ctx => FKisM.point(ctx)))

  private def scope_[A](ctx: Context)(fa: Thy[KernelException,A]) =
    new Thy(kleisli_(_ => fa.k.run(ctx)))

  // Put KernelExceptions into MonadError. Could skip this when specialising
  // MonadError on this exception type.
  private def except[A](x: => A): Thy[KernelException,A] =
    try x.point[ThyK]
    catch {
      case exc: Utils.KernelException =>
        ThyKInstances.raiseError[A](exc)
    }

  def typeOfConst[E](constName: Name): Thy[KernelException,Option[Type]] =
    ask_.map(_.typeOfConst(constName))

  def typeOfTerm(term: Term): Thy[KernelException,Type] =
    ask_ >>= { _.typeOfTerm(term) match {
      case Some(ty) => ty.point[ThyK]
      case None     => ThyKInstances.raiseError[Type](
        new KernelException("term not valid"))
    }}

  // NB: The following functions should not throw any exceptions concerning invalid
  // contexts.
  def introducing(constName: Name, ty: Type)(mthm: Thy[KernelException,Thm]):
      Thy[KernelException,Thm] =
    for (
      ctx    <- ask_;
      newCtx =  ctx.introduce(constName,ty);
      thm    <- scope_[Thm](newCtx)(mthm)
    )
    yield new Thm(ctx.lift(thm.get))

  def assuming(tm: Term)(mthm: Thy[KernelException,Thm]): Thy[KernelException,Thm] =
    for (
      ctx  <- ask_;
      asm  <- except(ctx.assume(tm));
      thm  <- scope_[Thm](asm.context)(mthm)
    )
    yield new Thm(ctx.lift(thm.get))

  def defining(name: IndexedName, tm: Term)(mthm: Thy[KernelException,Theorem]):
      Thy[KernelException,Thm] =
    for (
      ctx  <- ask_;
      defn <- except(ctx.define(Name(None,name), tm));
      thm  <- scope_[Theorem](defn.context)(mthm)
    )
    yield new Thm(ctx.lift(thm))

  def choosing(name: IndexedName, tm: Term)(mthm: Thy[KernelException,Thm]):
      Thy[KernelException,Thm] =
    for (
      ctx  <- ask_;
      defn <- except(ctx.define(Name(None,name), tm));
      thm  <- scope_[Thm](defn.context)(mthm)
    )
    yield new Thm(ctx.lift(thm.get))

  private def askThm(f: Context => Theorem): Thy[KernelException,Thm] =
    ask_ map { ctx => new Thm(f(ctx)) }
  private def askThmExcept(f: Context => Theorem): Thy[KernelException,Thm] =
    ask_ >>= { ctx => except(f(ctx)) map { thm => new Thm(thm) } }

  def reflexive(x: Term): Thy[KernelException,Thm] = askThm(_.reflexive(x))
  def beta(tm: Term): Thy[KernelException,Thm] = askThmExcept(_.beta(tm))
  def eta(tm: Term): Thy[KernelException,Thm] = askThmExcept(_.eta(tm))
  def normalize(tm: Term): Thy[KernelException,Thm] = askThm(_.normalize(tm))
  def mkFresh(name: IndexedName) = ask_ map (_.mkFresh(name))
  def transitive(xy: Thm, yz: Thm): Thy[KernelException,Thm] =
    askThmExcept(_.transitive(xy.get,yz.get))
  def comb(fg: Thm, xy: Thm): Thy[KernelException,Thm] =
    askThmExcept(_.comb(fg.get,xy.get))
  def modusponens(p: Thm, qr: Thm) = askThmExcept(_.modusponens(p.get,qr.get))
  def abs(eq: Thm) = askThmExcept(_.abs(eq.get))
  def equiv(l: Thm, r: Thm) = askThmExcept(_.equiv(l.get,r.get))
  def instantiate(thm: Thm, insts: List[Option[Term]]) =
    askThmExcept(_.instantiate(thm.get, insts))
}
