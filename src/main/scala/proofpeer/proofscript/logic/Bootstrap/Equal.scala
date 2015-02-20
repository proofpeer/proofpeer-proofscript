// package proofpeer.proofscript.logic.bootstrap

// import scala.language.higherKinds
// import scala.language.implicitConversions
// import scalaz._
// import Scalaz._
// import Kleisli._
// import proofpeer.proofscript.logic.Kernel
// import proofpeer.proofscript.logic.Kernel._
// import proofpeer.proofscript.logic.KernelUtils._
// import proofpeer.proofscript.logic.Name
// import proofpeer.proofscript.logic.Term
// import proofpeer.proofscript.logic.Theory
// import proofpeer.proofscript.logic.Conversions
// import proofpeer.proofscript.logic.EqualsInstances._

// trait Equal[F[_,_]] extends Conversions[F] {
//   def combConv(ratorConv: Conv, randConv: Conv): Conv = kleisli[ThyS,Term,Thm] { 
//       case Term.Comb(rator, rand) =>
//         ((ratorConv(rator) |@| randConv(rand)) { comb(_,_) }).join
//       case _ => mInstances[String].raiseError[Thm]("not a combination");
//     }

//   def absConv(conv: Conv): Conv = kleisli[ThyS,Term,Thm] {
//     case Term.Abs(name, ty, body) =>
//       (introducing(Name(None,name), ty) { conv(body) }) >>= { abs(_) }
//     case _ => mInstances[String].raiseError[Thm]("not an abstraction");
//   }
// }

// object Test {
//   abstract sealed class Error[E,A]
//   case class Failed[E,A](exc: E) extends Error[E,A]
//   case class Result[E,A](x: A)   extends Error[E,A]

//   trait errorIsMonadPlus[E] extends MonadPlus[({type λ[A] = Error[E,A]})#λ] {
//     def mzero[A] = Failed[E,A](
//   }

//   sealed abstract class Test extends Conversions[Error] {
// //    def errEv[E] = object MonadError[({type λ[E,A] = EitherT[Id,E,A]})#λ,E] {

//     }
// //      EitherT.eitherTMonadError[Id,E]
// //    def blah[E] = errEv[List[E]]
// // //    def theErrEv[E] = errEv[List[E]]
// //     override def thePlusEv[E]: MonadPlus[({type λ[A] = EitherT[Id,List[E],A]})#λ] =
// //       EitherT.eitherTMonadPlus[Id,List[E]]
//   }
// }
