package proofpeer.proofscript.automation

import proofpeer.proofscript.logic.{Kernel => _,_}
import KernelInstances._
import proofpeer.metis.{Term => MTerm, _}
import TermInstances._
import scalaz.{Name => _, _}
import Scalaz._

object Automation {
  type V = IndexedName \/ FOF.Fresh[IndexedName]
  type F = V \/ Name
  type P = Name
  type PPClause = Clause[V, F, F]

  def prove(context : Context, proposition : Term, thms : Vector[Theorem]) :
      Option[Theorem] = {

    val negatedConjecture = FOF.unapply(proposition).map(Unary(FOF.Neg(),_))
    val premises = thms.map(_.proposition).traverse(FOF.unapply(_))

    val clauses =
      (negatedConjecture |@| premises) {_ +: _} map (_.flatMap(METIS.TermToCNF(_)))

    clauses >>= { cls =>

      // All Fresh variables indices
      val freshes: Set[Int] =
        cls.foldMap { cl =>
          for ( \/-(Prov(_,f)) <- cl.frees )
          yield f }

      val nextFresh: Int = freshes.max + 1

      implicit val ordFun = KnuthBendix.precedenceOrder[V,F]
      implicit val kbo = KnuthBendix.kbo[V,F]
      val kernel = new Kernel[V,F,F]
      val factor = new Factor[V,F,F]
      val litOrd = new MetisLiteralOrdering(kbo)
      val fin = FinOrd(8)
      val vals = Valuations[V](fin)
      val ithmF  = new IThmFactory[V,F,F,Int,kernel.type](
        kernel,
        nextFresh,
        { case (n,v) =>
          (n+1, (v match {
            case -\/(v)    => Prov.originate(v).map(_ => n)
            case \/-(free) => free.map(_ => n)
          }).right)
        },
        litOrd,
        factor)
      val interpretation = Interpretation[V,F,F](1000,vals)
      val sys = new Resolution(0,cls.toList,ithmF,interpretation)

      val allThms = sys.distance_nextThms.takeWhile(_.isDefined).flatten
      val limitThms = allThms.take(2000)
      limitThms.lastOption.filter { _._2.isContradiction }.map { _ =>
        context.magic(proposition)
      }
    }
  }
}
