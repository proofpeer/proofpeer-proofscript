package proofpeer.proofscript.automation

import proofpeer.proofscript.logic._
import scala.language.implicitConversions
import scalaz.{ Name => _, _}
import Scalaz._

object KernelInstances {
  implicit object TermIsEqual extends Equal[Term] {
    override def equal(l: Term, r: Term) = l == r
  }
  implicit object NamespaceIsOrdered extends Order[Namespace] {
    override def equal(l: Namespace, r: Namespace) = l == r
    override def order(l: Namespace, r: Namespace) =
      (l.isAbsolute ?|? r.isAbsolute) |+| (l.components ?|? r.components)
  }
  implicit object IndexedNameIsOrdered extends Order[IndexedName] {
    override def equal(l: IndexedName, r: IndexedName) = l == r
    override def order(l: IndexedName, r: IndexedName) = {
      (l.name ?|? r.name) |+| (l.index ?|? r.index)
    }
  }
  implicit object NameIsOrdered extends Order[Name] {
    override def equal(l: Name, r: Name) = l == r
    override def order(l: Name, r: Name) =
      (l.namespace ?|? r.namespace) |+| (l.name ?|? r.name)
  }
  // TODO: Temporarily poor show implementation
  implicit object IndexedNameIsShow extends Show[IndexedName] {
    override def show(n: IndexedName) = n.name.shows ++ n.index.shows
  }
  implicit object NameIsShow extends Show[Name] {
    override def show(n: Name) = n.name.show
  }

  def bracket(str: Cord) = Cord("(") ++ str ++ Cord(")")

  implicit object TypeIsOrdered extends Order[Type] {
    override def equal(l: Type, r: Type) = l == r
    override def order(l: Type, r: Type) =
      (l,r) match {
        case (Type.Universe, Type.Universe)                 => Ordering.EQ
        case (Type.Universe, _)                             => Ordering.LT
        case (_, Type.Universe)                             => Ordering.GT
        case (Type.Prop, Type.Prop)                         => Ordering.EQ
        case (Type.Prop, _)                                 => Ordering.LT
        case (_, Type.Prop)                                 => Ordering.GT
        case (Type.Fun(ldom,lcodom), Type.Fun(rdom,rcodom)) =>
          (ldom ?|? rdom) |+| (lcodom ?|? rcodom)
        case (Type.Fun(_,_),_)                              => Ordering.LT
        case (_, Type.Fun(_,_))                             => Ordering.GT
      }
  }

  implicit object TermIsOrdered extends Order[Term] {
    override def equal(l: Term, r: Term) = l == r
    override def order(l: Term, r: Term): Ordering = {
      import Term._
      (l,r) match {
        case (PolyConst(m,ty1), PolyConst(n,ty2))   =>
          (m ?|? n) |+| (ty1 ?|? ty2)
        case (PolyConst(_,_), _)                    => Ordering.LT
        case (_, PolyConst(_,_))                    => Ordering.GT
        case (Const(n1),Const(n2))                  => n1 ?|? n2
        case (Const(_),_)                           => Ordering.LT
        case (_,Const(_))                           => Ordering.GT
        case (Comb(f1,x1), Comb(f2,x2))             => (f1 ?|? f2) |+| (x1 ?|? x2)
        case (Comb(_,_), _)                         => Ordering.LT
        case (_,Comb(_,_))                          => Ordering.GT
        case (Abs(n1,ty1,body1), Abs(n2,ty2,body2)) =>
          (n1 ?|? n2) |+| (ty1 ?|? ty2) |+| (body1 ?|? body2)
        case (Abs(_,_,_), _)                        => Ordering.LT
        case (_, Abs(_,_,_))                        => Ordering.GT
        case (Var(n1), Var(n2))                     => n1 ?|? n2
        case (Var(_), _)                            => Ordering.LT
        case (_, Var(_))                            => Ordering.GT
      }
    }
  }

  implicit object TypeIsShow extends Show[Type] {
    override def show(ty: Type) =
      ty match {
        case Type.Universe       => "𝒰"
        case Type.Prop           => "ℙ"
        case Type.Fun(dom,codom) => bracket(dom.show ++ Cord("→") ++ codom.show)
      }
  }

  implicit object TermIsShow extends Show[Term] {
    override def show(t: Term) =
      t match {
        case Term.Var(IndexedName(name, index)) =>
          name.show ++ index.show
        case Term.PolyConst(name,ty) =>
          name.show ++ Cord(":") ++ ty.show
        case Term.Const(name)        => name.shows
        case Term.Abs(name,ty,body)  =>
          name.show ++ Cord(":") ++ ty.show ++ Cord(" ↦ ") ++ body.show
        case Term.Comb(rator,rand)   =>
          bracket(rator.show) ++ Cord(" ") ++ bracket(rand.show)
      }
  }
}
