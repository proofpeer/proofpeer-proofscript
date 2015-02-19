package proofpeer.proofscript.metis

import proofpeer.proofscript.logic._
import KernelUtils._
import scala.language.higherKinds
import scala.language.implicitConversions
import scalaz.{ Name => _, _ }
import Scalaz._
import Kleisli._
import KernelInstances._
import Utils.KernelException

/** `Theory` exposes inference rules without reference to contexts. The core type is
  * `Theory.Thy`, whose interface is at least that of a MonadError, plus versions of
  *  the kernel rules.
  *
  * @tparam `F` An instance of both [[scalaz.MonadError] for KernelException and
  * (when partially applied to KernelException) [[scalaz.Monad]].
  * @tparam `E` The error type.
  */
trait Theory[F[_,_],E] {
  def kernel: Kernel
  def FEisME: MonadError[F,E]
  def kernelError(e: KernelException): E

  type FE[A]  = F[E,A]
  implicit def FEisM: Monad[FE] = FEisME

  // Wrap theorems to limit access to contexts.
  class Thm private[Theory](private[Theory] val get: Theorem) {
    val proposition = get.proposition
  }

  private def kleisli_ [A](f: (Context) => F[E,A]) =
    Kleisli[({ type λ[A] = F[E,A] })#λ,Context,A](f)

  // Context is automatically threaded through computations (using Kleisli arrows
  // of F). We hide the arrows to keep them out of reach of client code and those
  // extending Theory. The intention here is that all uses of Context.lift will
  // go through.
  sealed class Thy[E,A] private[Theory] (
    private[Theory] val k: Kleisli[({type λ[A] = F[E,A]})#λ,Context,A]) {
    def apply(ctx: Context): F[E,A] = k.run(ctx)
  }
  type ThyE[A] = Thy[E,A]

  implicit object ThyIsMonad extends ThyIsMonad
  object ThyIsMonadError extends ThyIsMonadError with ThyIsMonad

  implicit def ThyIsMonadPlus(implicit ev: MonadPlus[({type λ[A] = F[E,A]})#λ]) =
    new ThyIsMonadPlus {
      override def FEisMP = ev
    }

  // Boiler plate makes me sad
  trait ThyIsMonad extends Monad[({type λ[A] = Thy[E,A]})#λ] {
    private type KE[A] = Kleisli[FE,Context,A]
    private implicit val ev: Monad[KE] = Kleisli.kleisliMonadReader
    import ev.monadSyntax._
    override def point[A](a: => A) = new Thy(ev.point(a))
    override def bind[A,B](fa: Thy[E,A])(f: A => Thy[E,B]) =
      new Thy(fa.k >>= (f(_).k))

    def liftF[A](x: F[E,A]): Thy[E,A] = new Thy(kleisli_ { _ => x })

    def bindF[A,B](x: Thy[E,A])(f: F[E,A] => Thy[E,B]): Thy[E,B] =
      new Thy(kleisli_ { ctx => f(x.k.run(ctx)).k.run(ctx) })
  }
  trait ThyIsMonadPlus
      extends ThyIsMonad with MonadPlus[({type λ[A] = Thy[E,A]})#λ] {
    def FEisMP: MonadPlus[({ type λ[A] = F[E,A]})#λ]

    private type KE[A] = Kleisli[FE,Context,A]
    private implicit val ev: MonadPlus[KE] =
      Kleisli.kleisliMonadPlus[FE,Context](FEisMP)
    override def empty[A] = new Thy(ev.empty)
    override def plus[A](x: Thy[E,A], y: => Thy[E,A]) = new Thy(ev.plus(x.k,y.k))
  }
  trait ThyIsMonadError extends MonadError[Thy,E] {
    override def raiseError[A](e: E) =
      new Thy(FEisME.raiseError[A](e).liftKleisli[Context])
    override def handleError[A](fa: Thy[E,A])(handler: E => Thy[E,A]) =
      new Thy(kleisli_ { ctx =>
        FEisME.handleError(fa.k.run(ctx))(e => handler(e).k.run(ctx))
      })
   }

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

  // Context access.
  private def ask_ : Thy[E,Context] =
    new Thy(kleisli_(ctx => FEisM.point(ctx)))

  private def scope_[A](ctx: Context)(fa: Thy[E,A]) =
    new Thy(kleisli_(_ => fa.k.run(ctx)))

  // Put KernelExceptions into MonadError. Could skip this when specialising
  // MonadError on this exception type.
  def except[A](x: => A): Thy[E,A] =
    try {
      val theX = x
      theX.point[ThyE]
    }
    catch {
      case exc: Utils.KernelException =>
        ThyIsMonadError.raiseError[A](kernelError(exc))
    }

  def typeOfConst(constName: Name): Thy[E,Option[Type]] =
    ask_.map(_.typeOfConst(constName))

  def typeOfTerm(term: Term): Thy[E,Type] =
    ask_ >>= { _.typeOfTerm(term) match {
      case Some(ty) => ty.point[ThyE]
      case None     => ThyIsMonadError.raiseError[Type](
        kernelError(new KernelException("term not valid")))
    }}

  // NB: The following functions should not throw any exceptions concerning invalid
  // contexts.
  def lift(thm: Thm): Thy[E,Thm] = ask_ map { ctx =>
    new Thm(ctx.lift(thm.get,true)) }

  def introducing(name: IndexedName, ty: Type)(mthm: Term.Const => Thy[E,Thm]):
      Thy[E,Thm] =
    for (
      ctx    <- ask_;
      n       = Name(None,name);
      newCtx  = ctx.introduce(n,ty);
      thm    <- scope_[Thm](newCtx)(mthm(Term.Const(n)) >>= (lift(_))) >>= (lift(_))
    )
    yield thm

  def assuming(tm: Term)(mthm: Thm => Thy[E,Thm]): Thy[E,Thm] =
    for (
      ctx <- ask_;
      asm <- except(ctx.assume(tm));
      thm <- scope_[Thm](asm.context)(mthm(new Thm(asm))) >>= (lift(_))
    )
    yield thm

  def defining(name: IndexedName, tm: Term)(mthm: Term.Const => Thy[E,Thm]):
      Thy[E,Thm] =
    for (
      ctx  <- ask_;
      n     = Name(None,name);
      defn <- except(ctx.define(Name(None,name), tm));
      thm  <- scope_[Thm](defn.context)(mthm(Term.Const(n))) >>= (lift(_))
    )
    yield thm

  def choosing(name: IndexedName, tm: Term)(mthm: Thy[E,Thm]): Thy[E,Thm] =
    for (
      ctx  <- ask_;
      defn <- except(ctx.define(Name(None,name), tm));
      thm  <- scope_[Thm](defn.context)(mthm) >>= (lift(_))
    )
    yield thm


  def destAbs[A](tm: Term)(f: (Term,Term) => Thy[E,A]) = ask_ map { ctx =>
    ctx.destAbs(tm) match {
      case None => ThyIsMonadError.raiseError[Type](
        kernelError(new KernelException("Not an abstraction.")))
      case Some((newCtx,x,bod)) =>
        scope_[A](newCtx)(f(x,bod))
    }
  }

  private def askThm(f: Context => Theorem): Thy[E,Thm] =
    ask_ map { ctx => new Thm(f(ctx)) }
  private def askThmExceptM(f: Context => Thy[E,Theorem]): Thy[E,Thm] =
    ask_ >>= { ctx => except(f(ctx)).join map { thm => new Thm(thm) } }
  private def askThmExcept(f: Context => Theorem): Thy[E,Thm] =
    askThmExceptM { ctx => f(ctx).point[ThyE] }

  /** The following rules do not lift theorems. If this is necessary,
      lift must be used manually.
    */
  // TODO: Should probably provide versions which do lifting automatically.
  def reflexive(x: Term): Thy[E,Thm] = askThm(_.reflexive(x))
  def beta(tm: Term): Thy[E,Thm] = askThmExcept(_.beta(tm))
  def eta(tm: Term): Thy[E,Thm] = askThmExcept(_.eta(tm))
  def normalize(tm: Term): Thy[E,Thm] = askThm(_.normalize(tm))
  def mkFresh(name: IndexedName) = ask_ map (_.mkFresh(name))
  def transitive(xy: Thm, yz: Thm): Thy[E,Thm] =
    askThmExcept(_.transitive(xy.get,yz.get))
  def comb(fg: Thm, xy: Thm): Thy[E,Thm] =
    askThmExcept(_.comb(fg.get,xy.get))
  def modusponens(p: Thm, qr: Thm) = askThmExcept(_.modusponens(p.get,qr.get))
  def abs(eq: Thm) = askThmExcept(_.abs(eq.get))
  def equiv(l: Thm, r: Thm) = askThmExcept(_.equiv(l.get,r.get))
  def instantiate(thm: Thm, insts: List[Option[Term]]) =
    askThmExcept(_.instantiate(thm.get, insts))

  val emptyRes = new NamespaceResolution((_ => Set()), (_ => Set[IndexedName]()))

  def parse(str: String): Thy[E,Term] = {
    for (
      ctx     <- ask_;
      aliases = new Aliases(ctx.namespace, List());
      tm      <- except(Syntax.parseTerm(aliases,emptyRes,ctx,str)))
    yield tm
  }
}
