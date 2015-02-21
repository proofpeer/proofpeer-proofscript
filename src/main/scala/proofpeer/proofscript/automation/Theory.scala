package proofpeer.proofscript.automation

import scala.language.higherKinds
import scala.language.implicitConversions
import scalaz.{ Name => _, _ }
import Scalaz._
import Kleisli._
import KernelInstances._
import proofpeer.proofscript.logic._
import KernelUtils._
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

  // Context is automatically threaded through computations (using Kleisli arrows
  // of F). We hide the arrows to keep them out of reach of client code and those
  // extending Theory. The intention here is that all uses of Context.lift will
  // go through.
  private type K[E,A]   = Kleisli[({type λ[A] = F[E,A]})#λ,Context,A]
  private type KE[A]    = Kleisli[FE,Context,A]
  private implicit def KEisM: Monad[KE] = Kleisli.kleisliMonadReader
  private type ContT[A] = ContsT[Identity,KE,Thm,A]
  sealed class Thy[E,A] private[Theory] (
    private[Theory] val k: ContsT[Identity,({type λ[A] = K[E,A]})#λ,Thm,A])

  type ThyE[A] = Thy[E,A]

  implicit object ThyIsMonad extends ThyIsMonad
  object ThyIsMonadError extends ThyIsMonadError with ThyIsMonad

  implicit def ThyIsMonadPlus(implicit ev: PlusEmpty[({type λ[A] = F[E,A]})#λ]) =
    new ThyIsMonadPlus {
      override def FEisPE = ev
    }

  // Boiler plate makes me sad
  trait ThyIsMonad extends Monad[({type λ[A] = Thy[E,A]})#λ] {
    private implicit val ev: Monad[ContT] = ContsT.ContsTMonad
    private implicit def KEisM: Monad[KE] = Kleisli.kleisliMonadReader
    import ev.monadSyntax._
    override def point[A](a: => A) = new Thy(ev.point(a))
    override def bind[A,B](fa: Thy[E,A])(f: A => Thy[E,B]) =
      new Thy(fa.k >>= (f(_).k))

    def liftF[A](x: F[E,A]): Thy[E,A] = {
      val k = Kleisli.kleisliU { ctx: Context => x }
      val c: ContT[A] = IndexedContsT.liftM[Identity,KE,Thm,A](k)(
        implicitly[Comonad[Identity]],implicitly(KEisM))
      new Thy(c)
    }

    def bindF[A,B](thyA: Thy[E,A])(f: F[E,A] => Thy[E,B]): Thy[E,B] =
      new Thy(IndexedContsT.apply[Identity,KE,Thm,Thm,B] { k =>
        Kleisli[FE,Context,Thm] { ctx: Context =>
          def arrow(x:A): Kleisli[FE,Context,Thm] =
            Kleisli[FE,Context,Thm] {
              ctx: Context => f(FEisME.point(x)).k.run(k).run(ctx)
            }
          def idArrow: Identity[A => Kleisli[FE,Context,Thm]] = Value(arrow)
          thyA.k.run(idArrow).run(ctx)
        }
      })
  }

  trait ThyIsMonadPlus
      extends ThyIsMonad with MonadPlus[({type λ[A] = Thy[E,A]})#λ] {
    def FEisPE: PlusEmpty[({ type λ[A] = F[E,A]})#λ]

    private type KE[A] = Kleisli[FE,Context,A]
    private implicit val ev: PlusEmpty[KE] =
      Kleisli.kleisliPlusEmpty[FE,Context](FEisPE)
    override def empty[A] =
      new Thy(IndexedContsT.apply[Identity,KE,Thm,Thm,A] { _ => ev.empty })
    override def plus[A](x: Thy[E,A], y: => Thy[E,A]) =
      new Thy(IndexedContsT.apply[Identity,KE,Thm,Thm,A] {
        k => ev.plus(x.k.run(k),y.k.run(k))
      })
  }

  trait ThyIsMonadError extends MonadError[Thy,E] {
    override def raiseError[A](e: E) =
      new Thy(IndexedContsT.apply[Identity,KE,Thm,Thm,A]{ k =>
        Kleisli[FE,Context,Thm] (_ => FEisME.raiseError[Thm](e) )
      })
    override def handleError[A](fa: Thy[E,A])(handler: E => Thy[E,A]) =
      new Thy(IndexedContsT.apply[Identity,KE,Thm,Thm,A]{ k =>
        Kleisli[FE,Context,Thm] { ctx =>
          FEisME.handleError(fa.k.run(k).run(ctx)){ e =>
            handler(e).k.run(k).run(ctx)
          }
        }
      })
  }

  // Wrap theorems to limit access to contexts.
  class Thm private[Theory](private[Theory] val get: Theorem) {
    def proposition: Thy[E,Term] =
      lift(this).map(_.proposition)
  }

  // Context access.
  private def ask_ : Thy[E,Context] =
    new Thy(IndexedContsT.apply[Identity,KE,Thm,Thm,Context]{ k =>
      Kleisli[FE,Context,Thm] { ctx => k.value(ctx).run(ctx) }
    })

  // Set context.
  private def inContext(ctx: Context): Thy[E,Unit] = {
    new Thy(IndexedContsT.apply[Identity,KE,Thm,Thm,Unit]{ k =>
      Kleisli[FE,Context,Thm] { _ => k.value(()).run(ctx) }
    })
  }

  /** Run theory in a local context. */
  def block[A](fa: Thy[E,Thm]): Thy[E,Thm] =
    new Thy(IndexedContsT.apply[Identity,KE,Thm,Thm,Thm]{ k =>
      Kleisli[FE,Context,Thm] { ctx =>
        def arrow(thm:Thm): Kleisli[FE,Context,Thm] =
          Kleisli[FE,Context,Thm] { innerCtx =>
            val icthm = innerCtx.lift(thm.get,true)
            val cthm  = ctx.lift(icthm,true)
            k.value(new Thm(cthm)).run(ctx) }
        def idArrow: Identity[Thm => Kleisli[FE,Context,Thm]] = Value(arrow)
        fa.k.run(idArrow).run(ctx)
      }})

  // Raise an exception as a KernelException.
  private def except[A](x: => A): Thy[E,A] =
    try {
      val theX = x
      theX.point[ThyE]
    }
    catch {
      case exc: Utils.KernelException =>
        ThyIsMonadError.raiseError[A](kernelError(exc))
    }

  /** Run this `Theory` in the supplied [[proofpeer.proofscript.logic.Context]].
    */
  def run(mthm: Thy[E,Thm])(ctx: Context) =
    block(mthm).k.run_.run(ctx).map{_.get}

  def typeOfConst(constName: Name): Thy[E,Option[Type]] =
    ask_.map(_.typeOfConst(constName))

  def typeOfTerm(term: Term): Thy[E,Type] =
    ask_ >>= { _.typeOfTerm(term) match {
      case Some(ty) => ty.point[ThyE]
      case None     => ThyIsMonadError.raiseError[Type](
        kernelError(new KernelException("term not valid")))
    }}

  def introduce(name: IndexedName, ty: Type): Thy[E,Term] =
    for (
      ctx    <- ask_;
      n      =  Name(None,name);
      newCtx =  ctx.introduce(n,ty);
      _      <- inContext(newCtx))
    yield Term.Const(n)

  def assume(tm: Term): Thy[E,Thm] =
    for (
      ctx <- ask_;
      asm <- except(ctx.assume(tm));
      _   <- inContext(asm.context))
    yield new Thm(asm)

  def defining(name: IndexedName, tm: Term): Thy[E,(Term.Const,Thm)] =
    for (
      ctx  <- ask_;
      n    =  Name(None,name);
      defn <- except(ctx.define(Name(None,name), tm));
      _    <- inContext(defn.context))
    yield (Term.Const(n),new Thm(defn))

  def choosing(name: IndexedName, tm: Term)(mthm: Thy[E,Thm]): Thy[E,Thm] =
    for (
      ctx  <- ask_;
      defn <- except(ctx.define(Name(None,name), tm));
      _    <- inContext(defn.context))
    yield new Thm(defn)

  def destAbs[A](tm: Term): Thy[E,(Term,Term)] = ask_ >>= { ctx =>
    ctx.destAbs(tm) match {
      case None => ThyIsMonadError.raiseError[(Term,Term)](
        kernelError(new KernelException("Not an abstraction.")))
      case Some((newCtx,x,bod)) =>
        inContext(newCtx) map (_ => (x,bod))
    }
  }

  private def askThm(f: Context => Theorem): Thy[E,Thm] =
    ask_ map { ctx => new Thm(f(ctx)) }
  private def askThmExceptM(f: Context => Thy[E,Theorem]): Thy[E,Thm] =
    ask_ >>= { ctx => except(f(ctx)).join map { thm => new Thm(thm) } }
  private def askThmExcept(f: Context => Theorem): Thy[E,Thm] =
    askThmExceptM { ctx => f(ctx).point[ThyE] }

  private def lift(thm: Thm): Thy[E,Theorem] = ask_ map { ctx =>
    ctx.lift(thm.get,true) }

  def reflexive(x: Term): Thy[E,Thm] = askThm(_.reflexive(x))
  def beta(tm: Term): Thy[E,Thm] = askThmExcept(_.beta(tm))
  def eta(tm: Term): Thy[E,Thm] = askThmExcept(_.eta(tm))
  def normalize(tm: Term): Thy[E,Thm] = askThm(_.normalize(tm))
  def mkFresh(name: IndexedName) = ask_ map (_.mkFresh(name))
  def transitive(xy: Thm, yz: Thm): Thy[E,Thm] =
    for (xy_ <- lift(xy);yz_ <- lift(yz);xz_ <- askThmExcept(_.transitive(xy_,yz_)))
    yield xz_
  def comb(fg: Thm, xy: Thm): Thy[E,Thm] =
    for (fg_ <- lift(fg); xy_ <- lift(xy); fxgy_ <- askThmExcept(_.comb(fg_,xy_)))
    yield fxgy_
  def modusponens(p: Thm, qr: Thm) =
    for (p_ <- lift(p); qr_ <- lift(qr); r_ <- askThmExcept(_.modusponens(p_,qr_)))
    yield r_
  def abs(eq: Thm) =
    for (eq_ <- lift(eq); abs_ <- askThmExcept(_.abs(eq_)))
    yield abs_
  def equiv(l: Thm, r: Thm) =
    for (l_ <- lift(l); r_ <- lift(r); eq_ <- askThmExcept(_.equiv(l_,r_)))
    yield eq_
  def instantiate(thm: Thm, insts: List[Option[Term]]) =
    for (thm_ <- lift(thm); inst_ <- askThmExcept(_.instantiate(thm_, insts)))
    yield inst_

  def parse(str: String): Thy[E,Term] = {
    for (
      ctx     <- ask_;
      aliases = new Aliases(ctx.namespace, List());
      tm      <- except(Syntax.parseTerm(aliases,emptyRes,ctx,str)))
    yield tm
  }
}
