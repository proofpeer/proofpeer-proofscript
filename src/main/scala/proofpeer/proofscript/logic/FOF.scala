package proofpeer.proofscript.logic

import KernelUtils._
import KernelInstances._
import proofpeer.metis.{ Term => MTerm, Fun => MFun, Var => MVar, Subst,
  Literal, Pred => MPred, Clause }
import proofpeer.metis.TermInstances._
import scala.language.higherKinds
import scalaz._
import Scalaz._

sealed abstract class FOF[V,F,P,+U,+B]
case class Pred[V,F,P,U,B](p: P, args: List[MTerm[V,F]])    extends FOF[V,F,P,U,B]
case class And[V,F,P,U,B](
  p: FOF[V,F,P,U,B], q: FOF[V,F,P,U,B])                     extends FOF[V,F,P,U,B]
case class Or[V,F,P,U,B](
  p: FOF[V,F,P,U,B], q: FOF[V,F,P,U,B])                     extends FOF[V,F,P,U,B]
case class Unary[V,F,P,U,B](u: U, p: FOF[V,F,P,U,B])        extends FOF[V,F,P,U,B]
case class Bnding[V,F,P,U,B](b: B, v: V, p: FOF[V,F,P,U,B]) extends FOF[V,F,P,U,B]

object FOF {
  sealed abstract class Binder
  case class All()    extends Binder
  case class Exists() extends Binder

  sealed case class Neg()

  def unapply(term: Term): Option[FOF[IndexedName,Name,Name,Neg,Binder]] = {
    term match {
      case Term.PolyConst(c,_) => Some(Pred(c,List()))
      case Term.Const(c)       => Some(Pred(c,List()))
      case Term.Var(v)         => Some(Pred(Name(None,v),List()))
      case Term.Comb(Term.Const(uop),p) if uop == Kernel.logical_not =>
        unapply(p).map (Unary(Neg(),_))
      case Term.Comb(Term.Comb(Term.Const(binop),p),q) =>
        val binopcons =
          (p: FOF[IndexedName,Name,Name,Neg,Binder]
            ,q: FOF[IndexedName,Name,Name,Neg,Binder]) => {
            if (binop === Kernel.logical_and)     Some(And(p,q))
            else if (binop === Kernel.logical_or) Some(Or(p,q))
            else if (binop === Kernel.implies)    Some(Or(Unary(Neg(),p),q))
            else if (binop === Kernel.equals)
              Some(Or(And(p,q),And(Unary(Neg(),p),Unary(Neg(),q))))
            else None
          }
            ((unapply(p) |@| unapply(q)) { binopcons(_,_) }).join orElse {
              (TermFunctions.unapply(p) |@| TermFunctions.unapply(q)) { case (l,r) =>
                Pred(binop,List(l,r)) }
            }
      case Term.Comb(Term.PolyConst(binder,_),Term.Abs(v,_,bod)) =>
        if (binder === Kernel.forall) {
          unapply(bod) map { Bnding(All(),v,_) }
        }
        else if (binder === Kernel.exists) {
          unapply(bod) map { Bnding(Exists(),v,_) }
        }
        else None
      case Term.Comb(rator,rand) =>
        ((unapply(rator) |@| TermFunctions.unapply(rand)) { (_,_) match {
          case (Pred(p,args),arg) => Some(Pred(p,args :+ arg))
          case _                  => None
        }}).join
      case Term.Abs(_,_,_) => None
    }
  }

  def pentamap[V,F,P,Un,B,V_,F_,P_,Un_,B_](fof: FOF[V,F,P,Un,B])(
    f: V => V_, g: F => F_, h: P => P_, i: Un => Un_, j: B => B_):
      FOF[V_,F_,P_,Un_,B_] = {
    fof match {
      case Pred(p,args)  => Pred(h(p),args.map(_.bimap(f,g)))
      case And(p,q)      => And(pentamap(p)(f,g,h,i,j),pentamap(q)(f,g,h,i,j))
      case Or(p,q)       => Or(pentamap(p)(f,g,h,i,j),pentamap(q)(f,g,h,i,j))
      case Unary(u,p)    => Unary(i(u),pentamap(p)(f,g,h,i,j))
      case Bnding(b,v,p) => Bnding(j(b),f(v),pentamap(p)(f,g,h,i,j))
    }
  }

  object Instances {
    implicit def FOFIsFunctor[F,P,Un,B]: Functor[({type λ[V] = FOF[V,F,P,Un,B]})#λ] =
    new Functor[({type λ[V] = FOF[V,F,P,Un,B]})#λ] {
      override def map[U,V](fof: FOF[U,F,P,Un,B])(f: U => V): FOF[V,F,P,Un,B] = {
        fof match {
          case Pred(p,args)    => Pred(p,args.map(_.map(f)))
          case And(p,q)        => And(map(p)(f),map(q)(f))
          case Or(p,q)         => Or(map(p)(f),map(q)(f))
          case Unary(u,p)      => Unary(u,map(p)(f))
          case Bnding(bnd,v,p) => Bnding(bnd,f(v),map(p)(f))
        }
      }
    }

    implicit def NegIsShow = new Show[Neg] {
      override def show(neg: Neg) = Cord("~")
    }
  }

  def toNNF[V,F,P](fof: FOF[V,F,P,Neg,Binder]):
      FOF[V,F,(Option[Neg],P),Nothing,Binder] = {
    fof match {
      case Pred(p,args)           => Pred((None,p),args)
      case And(p,q)               => And(toNNF(p),toNNF(q))
      case Or(p,q)                => Or(toNNF(p),toNNF(q))
      case Unary(Neg(),p)         => notnnf(p)
      case Bnding(All(),v,bod)    => Bnding(All(),v,toNNF(bod))
      case Bnding(Exists(),v,bod) => Bnding(Exists(),v,toNNF(bod))
    }
  }

  private def notnnf[V,F,P](fof: FOF[V,F,P,Neg,Binder]):
      FOF[V,F,(Option[Neg],P),Nothing,Binder] = {
    fof match {
      case Pred(p,args)           => Pred((Some(Neg()),p),args)
      case And(p,q)               => Or(notnnf(p),notnnf(q))
      case Or(p,q)                => And(notnnf(p),notnnf(q))
      case Unary(Neg(),p)         => toNNF(p)
      case Bnding(All(),v,bod)    => Bnding(Exists(),v,notnnf(bod))
      case Bnding(Exists(),v,bod) => Bnding(All(),v,notnnf(bod))
    }
  }
}

object Matrix {
  type Matrix[V,F,P] = FOF[V,F,P,Nothing,Nothing]

  import FOF.{Binder,All,Exists,Neg}

  def frees[V,F,P](fof: Matrix[V,F,P]): Set[V] =
    preds(fof).flatMap { case Pred(p,args) => args.foldMap(_.frees) }

  def preds[V,F,P](fof: Matrix[V,F,P]): Set[Pred[V,F,P,Nothing,Nothing]] = {
    fof match {
      case p@Pred(_,_)      => Set(p)
      case And(p,q)         => preds(p) |+| preds(q)
      case Or(p,q)          => preds(p) |+| preds(q)
      case Unary(void,_)    => void
      case Bnding(void,_,_) => void
    }
  }

  private type QPS[A]     = State[Int,A]
  private type WT[M[_],A] = WriterT[M,List[(Binder,Int)],A]
  private type QPM[A]     = WT[QPS,A]

  private def substFresh[V:Equal,F,U,P,B](v: V \/ Int,fof: FOF[V \/ Int,F,U,P,B]):
      QPM[(Int,FOF[V \/ Int,F,U,P,B])] = {
    def subst(n: Int, fof: FOF[V \/ Int,F,U,P,B]): FOF[V \/ Int,F,U,P,B] = {
      fof match {
        case Pred(p,args)         => Pred(p,args.map(_.map { v_ =>
          if (v_ === v)
            n.right
          else v_
        }))
        case And(p,q)             => And(subst(n,p),subst(n,q))
        case Or(p,q)              => Or(subst(n,p),subst(n,q))
        case Unary(u,p)           => Unary(u,subst(n,p))
        case Bnding(bnd,bndv,bod) if bndv === v => Bnding(bnd,bndv,bod)
        case Bnding(bnd,bndv,bod) => Bnding(bnd,bndv,subst(n,bod))
      }
    }
    for (
      n <- get[Int].liftM[WT];
      _ <- modify[Int](_+1).liftM[WT])
    yield (n,subst(n, fof))
  }

  private def get_ : QPM[Int] = get[Int].liftM[WT]
  def quantPull[V:Equal,F,P,U](fof: FOF[V,F,(Option[Neg],P),Nothing,Binder]):
      (List[(Binder,Int)],Matrix[V \/ Int,F,(Option[Neg],P)]) = {
    def qp(fof: FOF[V \/ Int,F,(Option[Neg],P),Nothing,Binder]):
        QPM[Matrix[V \/ Int,F,(Option[Neg],P)]] = {
      fof match {
        case And(p,q)      => (qp(p) |@| qp(q)) {And(_,_)}
        case Or(p,q)       => (qp(p) |@| qp(q)) {Or(_,_)}
        case Unary(void,_) => void
        case Bnding(b,v,p) => substFresh(v,p) >>= {
          nfof : (Int,FOF[V \/ Int,F,(Option[Neg],P),Nothing,Binder]) => nfof match {
          case (n,fof) =>
              qp(fof) >>= { case qfof =>
                qfof.point[QPM] :++> (List((b,n)))
              }
          }
        }
        case Pred(p,args) =>
          val fof_ :Matrix[V \/ Int,F,(Option[Neg],P)] = Pred(p,args)
          fof_.point[QPM]
      }
    }
    import FOF.Instances.FOFIsFunctor
    qp(FOFIsFunctor.map(fof)(_.left)).run.eval(0).bimap({_.reverse},{x => x})
  }

  def skolemize[V:Order,F,P](
    binders: List[(Binder,V)],
    fof:     Matrix[V,V,P]): Matrix[V,V,P] = {

    def setToMap[A:Order](xs: Set[A]): A ==>> Unit = {
      xs.foldLeft(==>>.empty[A,Unit]) {
        case (m,x) => m + (x → Unit)
      }
    }

    val vsets = for (
      pred <- preds(fof);
      Pred(_,args) = pred)
    yield setToMap(args.foldMap(_.frees))

    def groupSet(varSets: V ==>> Set[V], vs: V ==>> Unit) = {
      // NB: (∅, |+|) in Monoid[Set] is (empty,union)
      val union  = vs.bifoldMap(v => varSets.lookup(v).get)(_ => ∅[Set[V]])
      val update = vs.map { _ => union }
      varSets |+| update
    }

    val initSets = setToMap(vsets.foldMap(_.keySet)).mapWithKey {
      case (v,()) => Set(v) }

    val groups = vsets.foldLeft(initSets)(groupSet)

    val (_,θ) = binders.foldLeft((List[V](),(==>>.empty[V,MTerm[V,V]]))) {
      case ((deps,θ),(All(),v))    => (deps :+ v,θ)
      case ((deps,θ),(Exists(),v)) =>
        val neededDeps = for (
          u <- deps;
          if groups.lookup(v).get.contains(u))
        yield MVar[V,V](u)
        (deps, θ + (v → MFun(v,neededDeps)))
    }

    def applySubst(fof: Matrix[V,V,P]): Matrix[V,V,P] =
      fof match {
        case Pred(p,args)     => Pred(p,args.map(_.subst(Subst(θ))))
        case And(p,q)         => And(applySubst(p),applySubst(q))
        case Or(p,q)          => Or(applySubst(p),applySubst(q))
        case Unary(void,_)    => void
        case Bnding(void,_,_) => void
      }

    applySubst(fof)
  }

  def showNNFMatrix[V:Show,F:Show,P:Show](fof: Matrix[V,F,(Option[Neg],P)]): Cord = {
    fof match {
      case Pred((neg,p),args) => (neg match {
        case Some(FOF.Neg())    => Cord("~")
        case None           => ∅[Cord]
      }) ++ p.show ++ Cord("(") ++ Cord.mkCord(",",args.map(_.show):_*) ++ Cord(")")
      case And(p,q)         => showNNFMatrix(p) ++ " ∧ " ++ showNNFMatrix(q)
      case Or(p,q)          => showNNFMatrix(p) ++ " ∨ " ++ showNNFMatrix(q)
      case Unary(void,_)    => void
      case Bnding(void,_,_) => void
    }
  }

  def showQuants[V:Show](quants: List[(FOF.Binder,V)]) =
    Cord.mkCord(" ",quants.map {
      case (All(),v)    => Cord("∀") ++ v.show
      case (Exists(),v) => Cord("∃") ++ v.show
    }:_*)
}

object TermFunctions {
  def unapply(term: Term): Option[MTerm[IndexedName,Name]] = {
    term match {
      case Term.PolyConst(c,_)   => Some(MFun(c,List()))
      case Term.Const(c)         => Some(MFun(c,List()))
      case Term.Comb(rator,rand) => (unapply(rator),unapply(rand)) match {
        case (Some(MFun(f,args)),Some(arg)) => Some(MFun(f,args :+ arg))
        case _                              => None
      }
      case Term.Var(v)           => Some(MVar(v))
      case _                     => None
    }
  }
}

object CNF {
  import Matrix.Matrix
  import FOF.Neg
  def cnf_[V,F,P](fof: Matrix[V,F,(Option[Neg],P)]): Set[Set[Literal[V,F,P]]] = {
    fof match {
      case Pred((None,p),args)        => Set(Set(Literal(true,MPred(p,args))))
      case Pred((Some(Neg()),p),args) => Set(Set(Literal(false,MPred(p,args))))
      case And(p,q)                   => cnf_(p) |+| cnf_(q)
      case Or(p,q)                    =>
        for (ps <- cnf_(p); qs <- cnf_(q)) yield ps |+| qs
    }
  }
  def cnf[V,F,P](fof: Matrix[V,F,(Option[Neg],P)]): Set[Clause[V,F,P]] =
    cnf_(fof).map(Clause(_))
}
