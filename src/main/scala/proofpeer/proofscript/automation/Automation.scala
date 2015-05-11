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

// C-terms forgetting their context
class CTermF(val cterm: CTerm) {
  override def equals(rhs: Any) =
    rhs match {
      case rhs: CTermF => cterm.term == rhs.cterm.term
      case _           => false
    }
  override def hashCode = cterm.term.hashCode
}


object Automation {
  type Err      = (String,StateValue)
  type Valid[A] = ValidationNel[Err,A]
  type MTerm    = MetisTerm[BigInt,CTermF]
  type MPred    = MetisPred[BigInt,CTermF,CTermF]
  type MAtom    = Atom[BigInt,CTermF,CTermF]
  type MLiteral = Literal[BigInt,CTermF,CTermF]
  type MClause  = Clause[BigInt,CTermF,CTermF]
  def mkTuple(v: StateValue*) = TupleValue(v.toVector,true)

  val funType = Type.Fun(Type.Universe,Type.Fun(Type.Universe,Type.Prop))

  def proofscriptOfTerm(tm: MTerm): StateValue =
    tm match {
      case Var(v)      => IntValue(v)
      case Fun(f,args) =>
        mkTuple(TermValue(f.cterm) +: args.toSeq.map (proofscriptOfTerm(_)):_*)
    }

  def proofscriptOfAtom(eq: CTerm, atm: MAtom): StateValue =
    atm match {
      case Eql(x,y) =>
        val px = proofscriptOfTerm(x)
        val py = proofscriptOfTerm(y)
        mkTuple(TermValue(eq),px,py)
      case MetisPred(p,args) =>
        mkTuple(TermValue(p.cterm) +: args.toSeq.map(proofscriptOfTerm(_)):_*)
    }

  def proofscriptOfLiteral(eq: CTerm, lit: MLiteral): StateValue =
    mkTuple(BoolValue(lit.isPositive),proofscriptOfAtom(eq,lit.atom))

  def proofscriptOfClause(eq: CTerm, cl: MClause): StateValue =
    SetValue(cl.lits.map { proofscriptOfLiteral(eq,_) })

  def proofscriptOfSubst(θ: Subst[BigInt,MTerm]): StateValue =
    MapValue(θ.θ.toAscList.map {
      case (n,tm) => (IntValue(n),proofscriptOfTerm(tm)) }.toMap,true)

  def termOfProofscript(tm: StateValue): Valid[MTerm] = {
    tm match {
      case TupleValue(elts,_) =>
        elts.toList match {
          case TermValue(f) :: args =>
            args.traverse { termOfProofscript(_) }.map { Fun(new CTermF(f),_) }
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
          case List(TermValue(eq),x,y) if (eq.term match {
            case Term.PolyConst(eq,_) if eq == K.equals => true
            case _                                      => false
          }) =>
            (termOfProofscript(x) |@| termOfProofscript(y)) { Eql(_,_) }
          case (TermValue(p) :: args) =>
            args.traverse { termOfProofscript(_) }.map { MetisPred(new CTermF(p),_) }
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

  def clauseOfProofscript(tm: StateValue): Valid[MClause] = {
    tm match {
      case SetValue(lits) =>
        lits.toList.traverse(litOfProofscript(_)).map {
          lits: List[MLiteral] => Clause(lits.toSet)
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

  import KernelInstances._

  // TODO: Need proper order instance for terms
  implicit val cTermIsOrder = new Order[CTermF] {
    override def order(x: CTermF, y: CTermF): Ordering =
      // crap? probably not. These strings should be unique in context.
      x.cterm.term.toString ?|? y.cterm.term.toString
  }
  implicit val cTermIsShow = new Show[CTermF] {
    override def show(ct: CTermF) =
      ct.cterm.term.show
  }

  def TPTPOfClause(cl: MClause, n: Int) =
    Cord("fof(") ++ n.show ++ Cord(", unknown, ") ++ Debug.TPTPOfClause(cl) ++
  Cord(").")

  def TPTPOfClauses(cls: List[MClause]) =
    Cord.mkCord("\n",cls.zipWithIndex.map {
      case (cl,i) => TPTPOfClause(cl, i)
    }:_*)

  def prove(ctx: Context, tm: CTerm, thms: Vector[Theorem]): Option[Theorem] = None

  def throughMetis(ctxProofscriptClauses: StateValue): StateValue = {

    System.out.println("Going through METIS");

    val eqcls = ctxProofscriptClauses match {
      case TupleValue(Vector(ctx:ContextValue, psClauses:StateValue),_) =>
        clausesOfProofscript(psClauses).map { cls =>
          (ctx.value.certify(Term.PolyConst(K.equals,Type.Universe)),cls)
        }
      case _ =>
        ("Expecting a pair of context and clauses",ctxProofscriptClauses).
          failureNel[(CTerm,List[MClause])]
    }

    eqcls match {
      case Failure(errs) =>
        mkTuple(
          (StateValue.mkStringValue("Error") +:
            errs.list.toVector.map {
              case (err,tm) =>
                mkTuple(
                  StateValue.mkStringValue(err),
                  tm)
            }):_*)
      case Success((eq,cls)) =>
        System.out.println("Interpreted clauses")
        import java.io._
        var (pw: PrintWriter) = null
        try {
          val file = File.createTempFile("Problem",".p")
          pw = new PrintWriter(file)
          pw.write(TPTPOfClauses(cls).toString)
          System.out.println("Written: " ++ file.toString)
        }
        catch {
          case exception:IOException =>
            System.out.println("Couldn't write clause file")
        }
        finally {
          pw.close()
        }

        val nextFree = cls.foldLeft(BigInt(0)) { case (n,cl) =>
          n.max((cl.frees + BigInt(0)).max)
        } + 1

        implicit val ordFun = KnuthBendix.precedenceOrder[BigInt,CTermF]
        implicit val kbo = KnuthBendix.kbo[BigInt,CTermF]
        val kernel = new Kernel[BigInt,CTermF,CTermF]
        val factor = new Factor[BigInt,CTermF,CTermF]
        val litOrd = new MetisLiteralOrdering(kbo)
        val fin = FinOrd(8)
        val vals = Valuations[BigInt](fin)
        val ithmF  = new IThmFactory[BigInt,CTermF,CTermF,BigInt,kernel.type](
          kernel,
          nextFree,
          { case (m,_) => (m+1,m) },
          litOrd,
          factor)

        val interpretation = Interpretation[BigInt,CTermF,CTermF](1000,vals)
        val sys = new Resolution(0,cls.toList,ithmF,interpretation)

        def proofscriptOfCertificate(cert: sys.ithmF.kernel.Thm): StateValue = {
          cert.rule match {
            case kernel.Axiom() =>
              mkTuple(
                StateValue.mkStringValue("axiom"),
                proofscriptOfClause(eq,cert.clause))
            case kernel.Assume() =>
              val atom = cert.clause.lits.filter(_.isPositive).toList match {
                case List(lit) => lit.atom
                case _         => throw new Exception("METIS Bug!")
              }
              mkTuple(StateValue.mkStringValue("assume"),proofscriptOfAtom(eq,atom))
            case kernel.Refl() =>
              cert.clause.lits.toList match {
                case List(Literal(true,Eql(x,y))) if x == y =>
                  mkTuple(StateValue.mkStringValue("refl"),proofscriptOfTerm(x))
                case _ => throw new Exception("METIS Bug!")
              }
            case kernel.Equality(cursor,term) =>
              mkTuple(
                StateValue.mkStringValue("equality"),
                proofscriptOfTerm(term),
                proofscriptOfLiteral(eq,cursor.top),
                mkTuple(cursor.path.toSeq.map(n => IntValue(BigInt(n))): _*))
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
                proofscriptOfAtom(eq,atm),
                proofscriptOfCertificate(pos),
                proofscriptOfCertificate(neg))
          }
        }
        import KernelInstances._
        val allThms = sys.distance_nextThms.takeWhile(_.isDefined).flatten
        allThms.find(_._2.isContradiction).map {
          case (_,thm) =>
            System.out.println("METIS: theorem verified")
            proofscriptOfCertificate(thm.thm)
        }.getOrElse {
          System.out.println("METIS: unprovable")
          NilValue
        }
    }
  }
}
