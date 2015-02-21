package proofpeer.proofscript.automation

import proofpeer.proofscript.logic._
import proofpeer.proofscript.naiveinterpreter._
import KernelUtils._
import Utils.KernelException
import scala.language.higherKinds
import scala.language.implicitConversions
import scalaz. { Name => _, _ }
import Scalaz._
import Kleisli._
import KernelInstances._

/** Conversions are Kleisli arrows Term => Thy[E,Theorem]. The intended semantics of
    conversions is given by its `thenMonoid`. */
trait Conversions[F[_,_],E] extends Theory[F,E] {
  // Sticking to really boring errors for conversions for now.
  def stringError(str: String): E
  def raiseString[A](str: String): Thy[E,A] =
    ThyIsMonadError.raiseError(stringError(str))
  def printTerm(tm: Term) = {
    Syntax.printTerm(Preterm.unknownResolution,tm)
  }

  def destEquals(tm: Term): ThyE[(Term,Term,Type)] = dest_equals(tm) match {
    case Some((lhs,rhs,ty)) => (lhs,rhs,ty).point[ThyE]
    case None               => raiseString(printTerm(tm) + " is not an equality")
  }

  case class Conv(k: Kleisli[ThyE,Term,Thm]) {
    def apply(tm: Term): ThyE[Thm] = k.run(tm)

    def andThenC(conv: Conv): Conv = kleisli[ThyE,Term,Thm](tm =>
      for (
        thm1            <- this(tm);
        eql             <- thm1.proposition >>= (destEquals(_));
        (lhs,rhs,ty)    =  eql;
        thm2            <- conv(rhs);
        eql_            <- thm2.proposition >>= (destEquals(_));
        (lhs_,rhs_,ty_) =  eql_;
        err <- if (lhs_ == rhs_) ().point[ThyE]
        else raiseString("andThen: " +
          printTerm(lhs_) + " != " + printTerm(rhs));
        thm <- transitive(thm1,thm2)
      )
      yield thm
    )
  }
  implicit def kleisliIsConv(k: Kleisli[ThyE, Term, Thm]): Conv = Conv(k)

  def absConv(conv: Conv): Conv = kleisli[ThyE,Term,Thm] {
    case tm@Term.Abs(x,ty,bod) =>
      (block(introduce(x,ty) >> (conv(bod)))) >>= (abs(_))
    case _ => raiseString("Not an abstraction")
  }

  def rewrConv(eq: Thm): ThyE[Conv] =
    for (
      eql     <- eq.proposition >>= (destEquals(_));
      (l,r,ty) = eql)
    yield kleisli[ThyE,Term,Thm] { tm =>
      if (tm === l) eq.point[ThyE]
      else raiseString(printTerm(tm) + " does not match " + printTerm(l))
    }

  object thenMonoid extends Monoid[Conv] {
    def zero = kleisli[ThyE,Term,Thm](tm => reflexive(tm))
    def append(x: Conv, y: => Conv) = (x andThenC y).k

    def ConvLaws {
      def thenZero[A](x: Conv, y: Conv, tm: Term)(implicit ev: IsEmpty[ThyE]):
          Boolean =
        ev.isEmpty((x andThenC zero)(tm))
      def zeroThen[A](x: Conv, y: Conv, tm: Term)(implicit ev: IsEmpty[ThyE]):
          Boolean =
        ev.isEmpty((zero andThenC x)(tm))
      // TODO: More laws? Associativity? Distributivity over <+> ?
    }
  }
}

object Test extends Conversions[({type λ[E,A] = EitherT[Id,E,A]})#λ,String] {
  def kernelError(e: KernelException): String =
    e.reason + e.getStackTrace().foldLeft("\n"){_ + "\n" + _}
  def stringError(e: String): String = e

  val kernel = {
    val handler = new ConsoleInterpreterNotificationHandler(print _)
    val dir = "/afs/inf.ed.ac.uk/user/p/pscott7/proofpeer/proofpeer-proofscript/" +
        "scripts/"
    val compileDir = new java.io.File(dir,"build")
    val theoryDirs = List(dir)
    val theoryFile = new java.io.File(dir,"root.thy")
    val source = scala.io.Source.fromFile(theoryFile)
    val (ee, allTheories) =
      LocalExecutionEnvironment.create(compileDir,theoryDirs,handler.loadedTheory _)
    val rootThys = allTheories.filter(_ == Namespace.root)
    val interpreter = new Interpreter(ee)

    handler.initialize(ee, rootThys)
    interpreter.compileTheories(rootThys,handler)
    ee.kernel
  }

  val ns = Namespace(true,Vector("foo"))
  val foo =
    Test.kernel.createNewNamespace(
      ns,
      Set(Kernel.root_namespace),
      new Aliases(ns, List()))

  def FEisME = EitherT.eitherTMonadError[Id,String]
  import Term._
  import Type._

  val x   = IndexedName("x",None)
  val y   = IndexedName("y",None)
  val p   = IndexedName("P",None)
  val q   = IndexedName("Q",None)
  val vx  = Var(x)
  val vy  = Var(y)
  val abs = Abs(x,Universe,vx)

  val theory = for (
    _  <- introduce(x,Universe);
    _  <- introduce(y,Universe);
    eq <- parse("x = y") >>= (assume(_));
    zx <- parse("z ↦ x");
    zy <- rewrConv(eq) >>= { absConv(_)(zx) })
  yield zy

  def myterm(str: String) = for (
    x   <- introduce(x,Universe);
    y   <- introduce(y,Universe);
    p   <- introduce(p,Fun(Universe,Prop));
    q   <- introduce(q,Fun(Universe,Fun(Universe,Prop)));
    asm <- parse(str) >>= (assume(_)))
  yield asm

  def bar = for (
    _  <- introduce(x,Universe);
    eq <- block (for (
      _  <- introduce(y,Universe);
      eq <- parse("x = y") >>= (assume(_)))
      yield eq);
    tm <- eq.proposition;
    () =  System.out.println(printTerm(tm)))
  yield eq

  val thm = run(theory)(foo)
}
