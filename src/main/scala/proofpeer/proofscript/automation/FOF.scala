package proofpeer.proofscript.automation

import proofpeer.proofscript.logic._
import KernelUtils._
import KernelInstances._
import proofpeer.metis.{ Term => MTerm, Fun => MFun, Var => MVar, Subst,
  Literal, Pred => MPred, Clause }
import proofpeer.metis.TermInstances._
import scala.language.higherKinds
import scalaz.{ Name => _ , _}
import Scalaz._
import Prov._

/** First order term.
  * @tparam V Type of variables
  * @tparam F Type of functors
  * @tparam P Type of predicate-functors
  * @tparam U Type of unary connectives (either Neg or Nothing)
  * @tparam B Type of binders (either Binder or Nothing)
  */
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
  case object All    extends Binder
  case object Exists extends Binder

  sealed case class Neg()

  /** Freshened variables are integers tracking their original. */
  type Fresh[V] = Prov[V,Int]

  /** Naive conversion from first-order Proofpeer terms:
        p → q   becomes   ~p ∨ q
        p ↔ q   becomes   (p ∧ q) ∨ (~p ∧ q)
    */
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
          unapply(bod) map { Bnding(All,v,_) }
        }
        else if (binder === Kernel.exists) {
          unapply(bod) map { Bnding(Exists,v,_) }
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

  /** FOF terms are functors in their (syntactic) functors. */
  def trimap[V,F,P,V_,F_,P_,U,B](fof: FOF[V,F,P,U,B])(
    f: V => V_, g: F => F_, h: P => P_): FOF[V_,F_,P_,U,B] = {
    fof match {
      case Pred(p,args)  => Pred(h(p),args.map(_.bimap(f,g)))
      case And(p,q)      => And(trimap(p)(f,g,h),trimap(q)(f,g,h))
      case Or(p,q)       => Or(trimap(p)(f,g,h),trimap(q)(f,g,h))
      case Unary(u,p)    => Unary(u,trimap(p)(f,g,h))
      case Bnding(b,v,p) => Bnding(b,f(v),trimap(p)(f,g,h))
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

  def toNNF[V,F,P,U](fof: FOF[V,F,P,Neg,Binder]):
      FOF[V,F,(Option[Neg],P),U,Binder] = {
    fof match {
      case Pred(p,args)         => Pred((None,p),args)
      case And(p,q)             => And(toNNF(p),toNNF(q))
      case Or(p,q)              => Or(toNNF(p),toNNF(q))
      case Unary(Neg(),p)       => notnnf(p)
      case Bnding(All,v,bod)    => Bnding(All,v,toNNF(bod))
      case Bnding(Exists,v,bod) => Bnding(Exists,v,toNNF(bod))
    }
  }

  private def notnnf[V,F,P,U](fof: FOF[V,F,P,Neg,Binder]):
      FOF[V,F,(Option[Neg],P),U,Binder] = {
    fof match {
      case Pred(p,args)         => Pred((Some(Neg()),p),args)
      case And(p,q)             => Or(notnnf(p),notnnf(q))
      case Or(p,q)              => And(notnnf(p),notnnf(q))
      case Unary(Neg(),p)       => toNNF(p)
      case Bnding(All,v,bod)    => Bnding(Exists,v,notnnf(bod))
      case Bnding(Exists,v,bod) => Bnding(All,v,notnnf(bod))
    }
  }
}

object Matrix {
  /** A matrix has no unary operators nor any binders. */
  type Matrix[V,F,P] = FOF[V,F,P,Nothing,Nothing]

  import FOF.{Binder,All,Exists,Neg}

  /** All variables in a matrix. */
  def frees[V,F,P](fof: Matrix[V,F,P]): Set[V] =
    preds(fof).flatMap { case Pred(p,args) => args.foldMap(_.frees) }

  /** All predicates in a matrix. */
  def preds[V,F,P](fof: Matrix[V,F,P]): Set[Pred[V,F,P,Nothing,Nothing]] = {
    fof match {
      case p@Pred(_,_)      => Set(p)
      case And(p,q)         => preds(p) |+| preds(q)
      case Or(p,q)          => preds(p) |+| preds(q)
      case Unary(void,_)    => void
      case Bnding(void,_,_) => void
    }
  }

  import FOF.Fresh
  /** Given a formula in NNF form (no unary operator), extract all binders,
      freshening variables as necessary.
    */
  def quantPull[V:Order,F,U,P](fof: FOF[V,F,P,Nothing,Binder]):
      (List[(Binder,Fresh[V])],
        Matrix[V \/ Fresh[V],F,P],
        FOF[V \/ Fresh[V],F,P,Nothing,Binder]) = {
    type QPS[A]     = State[(Int,V ==>> Fresh[V]),A]
    type WT[M[_],A] = WriterT[M,List[(Binder,Fresh[V])],A]
    type QPM[A]     = WT[QPS,A]
    type FOFIn  = FOF[V,F,P,Nothing,Binder]
    type FOFOut = FOF[V \/ Fresh[V],F,P,Nothing,Binder]
    type Mat_   = Matrix[V \/ Fresh[V],F,P]

    def getSubst : QPM[(V ==>> Fresh[V])] =
      get[(Int,V ==>> Fresh[V])].map(_._2).liftM[WT]

    def bindFresh(v: V): QPM[Fresh[V]] = {
      for (
        nθ    <- get[(Int,V ==>> Fresh[V])].liftM[WT];
        (n,θ) =  nθ;
        fresh =  originate(v).map(_ => n);
        _  <- put((n+1, θ + (v → Prov.originate(v).map {_ => n}))).liftM[WT])
      yield fresh
    }

    def qp(fof: FOFIn): QPM[(Mat_,FOFOut)] = {
      fof match {
        // Ugh. This is just biapplicative
        case And(p,q)      => for (
          qpp <- qp(p);
          qpq <- qp(q);
          (pmatrix,pfof) = qpp;
          (qmatrix,qfof) = qpq)
        yield (And(pmatrix,qmatrix),And(pfof,qfof))
        case Or(p,q)       => for (
          qpp <- qp(p);
          qpq <- qp(q);
          (pmatrix,pfof) = qpp;
          (qmatrix,qfof) = qpq)
        yield (Or(pmatrix,qmatrix),Or(pfof,qfof))
        case Unary(void,_) => void
        case Bnding(b,v,p) => bindFresh(v) >>= {
          v:Fresh[V] => qp(p) >>= { case (qfof,nfof) =>
            (qfof,nfof).point[QPM] :++> (List((b,v)))
          }
        }
        case pred@Pred(p,args) =>
          getSubst map { θ =>
            val newargs = args.map(_.map(v =>
              θ.lookup(v).map(_.right).getOrElse(v.left)))
            (Pred(p,newargs),Pred(p,newargs))
          }
      }
    }
    val (bnds,(matrix,nfof)) = qp(fof).run.eval((0,==>>.empty))
    (bnds,matrix,nfof)
  }

  /** Given a binding list and its matrix, skolemise to a matrix which is implicitly
      universally quantified. */
  def skolemize[V:Order,F,P](
    binders: List[(Binder,V)],
    fof:     Matrix[V,F,P]): Matrix[V,V \/ F,P] = {

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

    val (_,θ) = binders.foldLeft((List[V](),(==>>.empty[V,MTerm[V,V \/ F]]))) {
      case ((deps,θ),(All,v))    => (deps :+ v,θ)
      case ((deps,θ),(Exists,v)) =>
        val neededDeps = for (
          u <- deps;
          if groups.lookup(v).get.contains(u))
        yield MVar[V,V \/ F](u)
        (deps, θ + (v → MFun(v.left,neededDeps)))
    }
    def applySubst(fof: Matrix[V,F,P]): Matrix[V,V \/ F,P] =
      fof match {
        case Pred(p,args)     => Pred(p,args.map { _.bimap(
          { v => θ.lookup(v).getOrElse(MVar[V,V \/ F](v)) },
          {_.right[V]}).
            join
        })
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
      case (All,v)    => Cord("∀") ++ v.show
      case (Exists,v) => Cord("∃") ++ v.show
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
      case Unary(void,_)              => void
      case Bnding(void,_,_)           => void
    }
  }

  /** Convert an implicitly universally quantified matrix into CNF form. */
  def cnf[V,F,P](fof: Matrix[V,F,(Option[Neg],P)]): Set[Clause[V,F,P]] =
    cnf_(fof).map(Clause(_))
}

object METIS {
  import FOF._

  def TermToCNF[V:Order,F:Order](fof: FOF[V,F,F,Neg,Binder]):
      Set[Clause[V \/ Fresh[V], (V \/ Fresh[V]) \/ F, (V \/ Fresh[V]) \/ F]] = {
    val nnf = FOF.toNNF(fof)
    val (quants,matrix,_) = Matrix.quantPull(nnf)
    val quants_ = quants.map { case (b,v) => (b,v.right[V]) }
    val univMatrix = Matrix.skolemize(quants_,matrix)
    // Identify functors with predicates.
    // TODO: Check that there are no overloading issues here. Typing should
    // guarantee otherwise, right?
    val univMatrix_ =
      FOF.trimap(univMatrix)(
        {v => v},
        {f => f},
        {case (neg,p) => (neg,p.right[V \/ Fresh[V]])})
    CNF.cnf(univMatrix_)
  }
}
