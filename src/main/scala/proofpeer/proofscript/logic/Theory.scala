package proofpeer.proofscript.logic

import KernelUtils._
import scala.language.higherKinds
import scala.language.implicitConversions
import scalaz._
import Scalaz._
import Kleisli._
import EqualsInstances._

/** `Theory` exposes inference rules without reference to contexts. The core type is
  * `Theory.M`, whose interface is that of MonadError and MonadPlus, plus versions of
  * the kernel rules.
  *
  * @tparam `F` An instance of both [[scalaz.MonadError] and (when partially applied)
  * [[scalaz.MonadPlus]]
  */
trait Theory[F[_,_]] {
  def kernel: Kernel

  // Wrap theorems to limit access to contexts.
  class Thm private[Theory](private[Theory] val get: Theorem)

  /** Run this `Theory` in the supplied [[proofpeer.proofscript.logic.Namespace]]. */
  def run[E,Fold[_]:Foldable](mthm: M[E,Thm])(
    namespace: Namespace, parents: Fold[Namespace]): F[E,Theorem] = {
    val parentSet = parents.foldLeft[Set[Namespace]](Set()) { _ + _ }
    val ctx = kernel.createNewNamespace(
      namespace,
      parentSet,
      new Aliases(namespace, List()))
    mthm(ctx).map{_.get}
  }

  protected def theErrEv[E]:  MonadError[F,E]
  implicit protected def thePlusEv[E]: MonadPlus[({ type λ[A] = F[E,A]})#λ]

  private type K[E,C,A] = Kleisli[({type λ[A] = F[E,A]})#λ,C,A]
  private def kleisli_ [E,A](f: Context => F[E,A]) =
    Kleisli[({ type λ[A] = F[E,A] })#λ,Context,A](f)

  // Context is automatically threaded through computations (using Kleisli arrows
  // of F). We hide the arrows to keep them out of reach of client code and those
  // extending Theory. The intention here is that all uses of Context.lift will
  // go through.
  sealed class M[E,A] private[Theory] (private[Theory] val k: K[E,Context,A]) {
    def apply(ctx: Context): F[E,A] = k.run(ctx)
  }
  type MS[A] = M[String,A]

  sealed class MInstances[E] extends MIsMonadPlus[E] with MIsMonadError[E]
  implicit def mInstances[E] = new MInstances[E]

  // Boiler plate makes me sad
  trait MIsMonadPlus[E] extends MonadPlus[({type λ[A] = M[E,A]})#λ] {
    private type FE[A] = F[E,A]
    private type KE[A] = Kleisli[FE,Context,A]
    private implicit val ev: MonadPlus[KE] = Kleisli.kleisliMonadPlus
    override def point[A](a: => A) = new M(a.point[KE](implicitly(ev)))
    override def bind[A,B](fa: M[E,A])(f: A => M[E,B]) =
      new M(fa.k >>= (x => f(x).k))
    override def plus[A](x: M[E,A], y: => M[E,A]) = new M(x.k <+> y.k)
    override def empty[A] = new M(mempty[KE,A](implicitly(ev)))
  }
  trait MIsMonadError[E] extends MonadError[M,E] {
    private type FE[A]  = F[E,A]
    override def raiseError[A](e: E) =
      new M(theErrEv.raiseError[A](e).liftKleisli[Context])
    override def handleError[A](fa: M[E,A])(handler: E => M[E,A]) =
      new M(kleisli_ { ctx =>
        theErrEv.handleError(fa.k.run(ctx))(e => handler(e).k.run(ctx))
      })
  }

  // Context access.
  private def ask_[E]: M[E,Context] =
    new M(kleisli_(ctx => thePlusEv.point(ctx)))

  private def scope_[E,A](ctx: Context)(fa: M[E,A]) =
    new M(kleisli_(_ => fa.k.run(ctx)))

  def liftF[E,A](x: F[E,A]): M[E,A] = new M(kleisli_ { _ => x })

  // Catch all KernelExceptions.
  private def except[A](x: => A): M[String,A] =
    try x.point[MS]
    catch {
      case exc: Utils.KernelException =>
        mInstances[String].raiseError[A](exc.reason)
    }

  def typeOfConst[E](constName: Name): M[E,Option[Type]] =
    ask_[E].map(_.typeOfConst(constName))

  def typeOfTerm(term: Term): M[String,Type] =
    ask_[String] >>= { _.typeOfTerm(term) match {
      case Some(ty) => ty.point[MS]
      case None     => mInstances[String].raiseError[Type]("term not valid")
    }}

  // NB: The following functions should not throw any exceptions concerning invalid
  def introducing(constName: Name, ty: Type)(mthm: M[String,Thm]): M[String,Thm] =
    for (
      ctx    <- ask_[String];
      newCtx =  ctx.introduce(constName,ty);
      thm    <- scope_[String,Thm](newCtx)(mthm)
    )
    yield new Thm(ctx.lift(thm.get))

  def assuming(tm: Term)(mthm: M[String,Thm]): M[String,Thm] =
    for (
      ctx  <- ask_[String];
      asm  <- except(ctx.assume(tm));
      thm  <- scope_[String,Thm](asm.context)(mthm)
    )
    yield new Thm(ctx.lift(thm.get))

  def defining(name: IndexedName, tm: Term)(mthm: M[String,Theorem]): M[String,Thm] =
    for (
      ctx  <- ask_[String];
      defn <- except(ctx.define(Name(None,name), tm));
      thm  <- scope_[String,Theorem](defn.context)(mthm)
    )
    yield new Thm(ctx.lift(thm))

  def choosing(name: IndexedName, tm: Term)(mthm: M[String,Thm]): M[String,Thm] =
    for (
      ctx  <- ask_[String];
      defn <- except(ctx.define(Name(None,name), tm));
      thm  <- scope_[String,Thm](defn.context)(mthm)
    )
    yield new Thm(ctx.lift(thm.get))

  private def askThm[E](f: Context => Theorem): M[E,Thm] =
    ask_[E] map { ctx => new Thm(f(ctx)) }
  private def askThmExcept[E](f: Context => Theorem): M[String,Thm] =
    ask_[String] >>= { ctx => except(f(ctx)) map { thm => new Thm(thm) } }

  def reflexive[E](x: Term): M[E,Thm] = askThm[E](_.reflexive(x))
  def beta(tm: Term): M[String,Thm] = askThmExcept(_.beta(tm))
  def eta(tm: Term): M[String,Thm] = askThmExcept(_.eta(tm))
  def normalize[E](tm: Term): M[E,Thm] = askThm[E](_.normalize(tm))
  def mkFresh[E](name: IndexedName) = ask_[E] map (_.mkFresh(name))
  def transitive(xy: Thm, yz: Thm): M[String,Thm] =
    askThmExcept(_.transitive(xy.get,yz.get))
  def comb(fg: Thm, xy: Thm): M[String,Thm] = askThmExcept(_.comb(fg.get,xy.get))
  def modusponens(p: Thm, qr: Thm) = askThmExcept(_.modusponens(p.get,qr.get))
  def abs(eq: Thm) = askThmExcept(_.abs(eq.get))
  def equiv(l: Thm, r: Thm) = askThmExcept(_.equiv(l.get,r.get))
  def instantiate(thm: Thm, insts: List[Option[Term]]) =
    askThmExcept(_.instantiate(thm.get, insts))
}
