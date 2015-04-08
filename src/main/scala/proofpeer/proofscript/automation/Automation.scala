package proofpeer.proofscript.automation

import proofpeer.proofscript.logic.{Kernel => K,_}
import proofpeer.proofscript.naiveinterpreter.{ Success => _, _}
import KernelInstances._
import proofpeer.metis.{Term => MetisTerm, Pred => MetisPred, _}
import TermInstances._
import ClauseInstances._
import scalaz.{Name => _, _}
import Scalaz._
import scalaz.std.math._

object Automation {
  type Err      = (String,StateValue)
  type Valid[A] = ValidationNel[Err,A]
  type MTerm    = MetisTerm[BigInt,Term]
  type MPred    = MetisPred[BigInt,Term,Term]
  type MAtom    = Atom[BigInt,Term,Term]
  type MLiteral = Literal[BigInt,Term,Term]
  type MClause  = Clause[BigInt,Term,Term]
  def mkTuple(v: StateValue*) = TupleValue(v.toVector,true)

  val funType = Type.Fun(Type.Universe,Type.Fun(Type.Universe,Type.Prop))

  def proofscriptOfTerm(tm: MTerm): StateValue =
    tm match {
      case Var(v)      => IntValue(v)
      case Fun(f,args) =>
        mkTuple(TermValue(f) +: args.toSeq.map (proofscriptOfTerm(_)):_*)
    }

  def proofscriptOfAtom(atm: Atom[BigInt,Term,Term]): StateValue =
    atm match {
      case Eql(x,y) =>
        val px = proofscriptOfTerm(x)
        val py = proofscriptOfTerm(y)
        mkTuple(TermValue(Term.PolyConst(K.equals,funType)),px,py)
      case MetisPred(p,args) =>
        mkTuple(TermValue(p) +: args.toSeq.map(proofscriptOfTerm(_)):_*)
    }

  def proofscriptOfLiteral(lit: Literal[BigInt,Term,Term]): StateValue =
    mkTuple(BoolValue(lit.isPositive),proofscriptOfAtom(lit.atom))

  def proofscriptOfClause(cl: Clause[BigInt,Term,Term]): StateValue =
    SetValue(cl.lits.map { proofscriptOfLiteral(_) })

  def proofscriptOfSubst(θ: Subst[BigInt,MTerm]): StateValue =
    MapValue(θ.θ.toAscList.map {
      case (n,tm) => (IntValue(n),proofscriptOfTerm(tm)) }.toMap,true)

  def termOfProofscript(tm: StateValue): Valid[MTerm] = {
    tm match {
      case TupleValue(elts,_) =>
        elts.toList match {
          case TermValue(f) :: args =>
            args.traverse { termOfProofscript(_) }.map { Fun(f,_) }
          case _ => ("Not a term",tm).failureNel[MTerm]
        }
      case IntValue(v) => Var(v).successNel[Err]
      case _ => ("Not a term",tm).failureNel[MTerm]
    }
  }

  def atomOfProofscript(tm: StateValue): Valid[MAtom] = {
    tm match {
      case TupleValue(elts,_) =>
        elts.toList match {
          case List(TermValue(Term.PolyConst(eq,ty)),x,y) if eq == K.equals =>
            (termOfProofscript(x) |@| termOfProofscript(y)) { Eql(_,_) }
          case (TermValue(p) :: args) =>
            args.traverse { termOfProofscript(_) }.map { MetisPred(p,_) }
          case _ => ("Not an atom",tm).failureNel[MAtom]
        }
      case _ => ("Not an atom",tm).failureNel[MAtom]
    }
  }

  def litOfProofscript(tm: StateValue): Valid[MLiteral] = {
    tm match {
      case TupleValue(elts,_) =>
        elts.toList match {
          case List(BoolValue(isPositive),lit) =>
            atomOfProofscript(lit).map { Literal(isPositive,_) }
        }
      case _ => ("Not a literal",tm).failureNel[MLiteral]
    }
  }

  def clauseOfProofscript(tm: StateValue): Valid[Clause[BigInt,Term,Term]] = {
    tm match {
      case SetValue(lits) =>
        lits.toList.traverse(litOfProofscript(_)).map {
          lits: List[Literal[BigInt,Term,Term]] => Clause(lits.toSet)
        }
      case _ => ("Not a clause",tm).failureNel[MClause]
    }
  }

  def clausesOfProofscript(tm: StateValue): Valid[List[MClause]] = {
    tm match {
      case TupleValue(cls,_) =>
        cls.toList.traverse(clauseOfProofscript(_))
      case _ => ("Not a clause",tm).failureNel[List[MClause]]
    }
  }

  def prove(ctx: Context, tm: Term, thms: Vector[Theorem]): Option[Theorem] = None

  def throughMetis(proofscriptClauses: StateValue) : StateValue = {

    System.out.println("Going through METIS");

    clausesOfProofscript(proofscriptClauses) match {
      case Failure(errs) =>
        mkTuple(
          StateValue.mkStringValue("Error") ::
            errs.list.map {
              case (err,tm) =>
                mkTuple(
                  StateValue.mkStringValue(err),
                  tm)
            }:_*)
      case Success(cls) =>
        System.out.println("Interpreted clauses")

        // Need Order instance for Term
        implicit val termIsOrder = new Order[Term] {
          def order(x: Term, y: Term): Ordering =
            // crap
            x.toString ?|? y.toString
        }

        val nextFree = cls.foldLeft(BigInt(0)) { case (n,cl) =>
          n.max((cl.frees + BigInt(0)).max)
        } + 1

        implicit val ordFun = KnuthBendix.precedenceOrder[BigInt,Term]
        implicit val kbo = KnuthBendix.kbo[BigInt,Term]
        val kernel = new Kernel[BigInt,Term,Term]
        val factor = new Factor[BigInt,Term,Term]
        val litOrd = new MetisLiteralOrdering(kbo)
        val fin = FinOrd(8)
        val vals = Valuations[BigInt](fin)
        val ithmF  = new IThmFactory[BigInt,Term,Term,BigInt,kernel.type](
          kernel,
          nextFree,
          { case (m,_) => (m+1,m) },
          litOrd,
          factor)

        val interpretation = Interpretation[BigInt,Term,Term](1000,vals)
        val sys = new Resolution(0,cls.toList,ithmF,interpretation)

        def proofscriptOfCertificate(cert: sys.ithmF.kernel.Thm): StateValue = {
          cert.rule match {
            case kernel.Axiom() =>
              mkTuple(
                StateValue.mkStringValue("axiom"),
                proofscriptOfClause(cert.clause))
            case kernel.Assume() =>
              val atom = cert.clause.lits.filter(_.isPositive).toList match {
                case List(lit) => lit.atom
                // Otherwise Bug
              }
              mkTuple(StateValue.mkStringValue("assume"),proofscriptOfAtom(atom))
            case kernel.Refl() =>
              StateValue.mkStringValue("refl")
            case kernel.Equality(cursor,term) =>
              mkTuple(
                Vector(
                  StateValue.mkStringValue("equality"),
                  proofscriptOfLiteral(cursor.top)) ++
                  cursor.path.toSeq.map(n => IntValue(BigInt(n))): _*)
            case kernel.RemoveSym(thm) =>
              mkTuple(
                StateValue.mkStringValue("removeSym"),
                proofscriptOfCertificate(thm))
            case kernel.Irreflexive(thm) =>
              mkTuple(
                StateValue.mkStringValue("irreflexive"),
                proofscriptOfCertificate(thm))
            case kernel.InfSubst(θ,thm) =>
              mkTuple(
                proofscriptOfSubst(θ),
                proofscriptOfCertificate(thm))
            case kernel.Resolve(atm,pos,neg) =>
              mkTuple(
                StateValue.mkStringValue("resolve"),
                proofscriptOfAtom(atm),
                proofscriptOfCertificate(pos),
                proofscriptOfCertificate(neg))
          }
        }
        import KernelInstances._
        val allThms = sys.distance_nextThms.takeWhile(_.isDefined).flatten
        allThms.find(_._2.isContradiction).map {
          case (_,thm) => proofscriptOfCertificate(thm.thm)
        }.getOrElse(NilValue)
    }
  }
}
