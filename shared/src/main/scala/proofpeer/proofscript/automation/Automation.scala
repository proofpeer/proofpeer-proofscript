package proofpeer.proofscript.automation

import proofpeer.proofscript.logic.{Kernel => K,_}
import proofpeer.proofscript.naiveinterpreter.{ Success => _, _}
import KernelInstances._
import proofpeer.metis.{Term => MetisTerm, Pred => MetisPred, _}
import proofpeer.metis.util.Identified
import TermInstances.{TermIsShow => PSTermIsShow, _}
import LiteralInstances._
import ClauseInstances._
import scalaz.{Name => _, _}
import Scalaz._
import scalaz.std.math._

object Automation {
  type MTerm    = MetisTerm[BigInt,Term]
  type MPred    = MetisPred[BigInt,Term,Term]
  type MAtom    = Atom[BigInt,Term,Term]
  type MLiteral = Literal[BigInt,Term,Term]
  type MClause  = Clause[BigInt,Term,Term]
  type MTermIdx    = MetisTerm[(BigInt,Int),Term]
  type MPredIdx    = MetisPred[(BigInt,Int),Term,Term]
  type MAtomIdx    = Atom[(BigInt,Int),Term,Term]
  type MLiteralIdx = Literal[(BigInt,Int),Term,Term]
  type MClauseIdx  = Clause[(BigInt,Int),Term,Term]

  def mkTuple(v: StateValue*) = TupleValue(v.toVector,true)

  val funType = Type.Fun(Type.Universe,Type.Fun(Type.Universe,Type.Prop))

  def proofscriptOfIndexedVar(v: (BigInt,Int)): StateValue = {
    val (vn,vid) = v
    if (vid == 0)
      IntValue(vn)
    else
      SetValue(Set(mkTuple(IntValue(vn),IntValue(vid))))
  }

  def proofscriptOfTerm(fromTerm: Term => CTerm, tm: MTermIdx): StateValue =
    tm match {
      case Var(v) => proofscriptOfIndexedVar(v)
      case Fun(f,args) =>
        mkTuple(
          TermValue(
            fromTerm(f)) +: args.toSeq.map (proofscriptOfTerm(fromTerm, _)):_*)
    }

  def proofscriptOfAtom(fromTerm: Term => CTerm, eq: CTerm, atm: MAtomIdx):
      StateValue =
    atm match {
      case Eql(x,y) =>
        val px = proofscriptOfTerm(fromTerm,x)
        val py = proofscriptOfTerm(fromTerm,y)
        mkTuple(TermValue(eq),px,py)
      case MetisPred(p,args) =>
        mkTuple(
          TermValue(
            fromTerm(p)) +: args.toSeq.map(proofscriptOfTerm(fromTerm, _)):_*)
    }

  def proofscriptOfLiteral(fromTerm: Term => CTerm, eq: CTerm, lit: MLiteralIdx):
      StateValue =
    mkTuple(BoolValue(lit.isPositive),proofscriptOfAtom(fromTerm,eq,lit.atom))

  def proofscriptOfClause(fromTerm: Term => CTerm, eq: CTerm, cl: MClauseIdx):
      StateValue = {
    SetValue(cl.lits.foldLeft(Set[StateValue]()) { case (s,x) =>
      s + proofscriptOfLiteral(fromTerm,eq,x)
    })
  }

  type Err      = (String,StateValue)
  type Valid[A] = ValidationNel[Err,A]
  def termOfProofscript(tm: StateValue): Valid[MTerm] = {
    tm match {
      case TupleValue(elts,_) =>
        elts.toList match {
          case TermValue(f) :: args =>
            args.traverse { termOfProofscript(_) }.map {
              Fun(f.term,_)
            }
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
            args.traverse { termOfProofscript(_) }.map {
              MetisPred(p.term,_)
            }
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
          lits: List[MLiteral] => Clause(ISet.fromList(lits))
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

  // TODO: Use TPTPPrinter provided by Debug.
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

    val ctxeqcls = ctxProofscriptClauses match {
      case TupleValue(Vector(ctx:ContextValue, psClauses:StateValue),_) =>
        clausesOfProofscript(psClauses).map { cls =>
          (ctx.value,ctx.value.certify(Term.PolyConst(K.equals,Type.Universe)),cls)
        }
      case _ =>
        ("Expecting a pair of context and clauses",ctxProofscriptClauses).
          failureNel[(Context,CTerm,List[MClause])]
    }

    val icl = new IdentClause[BigInt,Term,Term]
    val termPrinter = Debug.showPrinter[BigInt,Term,Term]

    ctxeqcls match {
      case Failure(errs) =>
        mkTuple(
          (StateValue.mkStringValue("Error") +:
            errs.list.toVector.map {
              case (err,tm) =>
                mkTuple(
                  StateValue.mkStringValue(err),
                  tm)
            }):_*)
      case Success((ctx,eq,cls)) =>
        System.out.println("Interpreted clauses")
        import java.io._
        val file   = File.createTempFile("Problem",".p")
        val idfile = File.createTempFile("IdProblem",".p")
        val pw  = new PrintWriter(file)
        val pw2 = new PrintWriter(idfile)
        try {
          pw.write(TPTPOfClauses(cls).toString)
          val idcls = cls.map(icl.toIdentClause(_))
          icl.identClausePrinter(termPrinter)
          idcls.foreach {
            idcl => pw2.write(
              (Cord("fof(") |+|
                Debug.TPTPOfClause(idcl)
                |+| ").\n").toString)
          }
          System.out.println("Written: " ++ file.toString)
          System.out.println("Written: " ++ idfile.toString)
        }
        catch {
          case exception:IOException =>
            System.out.println("Couldn't write clause file")
        }
        finally {
          pw.close()
          pw2.close()
        }

        def proofscriptOfCertificate(cert: icl.ResolutionBasis.ithmF.kernel.Thm):
            StateValue = {
          val kernel = icl.ResolutionBasis.ithmF.kernel
          val fromTerm = (tm: Term) => ctx.certify(tm)
          def fromIdClause(cl: Clause[(icl.Id,Int),icl.Id,icl.Id]): MClauseIdx =
            Clause.trimap(cl)(
              { case (id,idx) => (icl.getVarById(id),idx) },
              icl.getFunById(_),
              icl.getPredById(_))
          def fromIdLiteral(lit: Literal[(icl.Id,Int),icl.Id,icl.Id]): MLiteralIdx =
            Literal.trimap(lit)(
              { case (id,idx) => (icl.getVarById(id),idx) },
              icl.getFunById(_),
              icl.getPredById(_))
          def fromIdAtom(atm: Atom[(icl.Id,Int),icl.Id,icl.Id]): MAtomIdx =
            Atom.trimap(atm)(
              { case (id,idx) => (icl.getVarById(id),idx) },
              icl.getFunById(_),
              icl.getPredById(_))
          def fromIdTerm(tm: MetisTerm[(icl.Id,Int),icl.Id]): MTermIdx =
            tm.bimap(
              { case (id,idx) => (icl.getVarById(id),idx) },
              icl.getFunById(_))
          cert.rule match {
            case kernel.Axiom() =>
              mkTuple(
                StateValue.mkStringValue("axiom"),
                proofscriptOfClause(fromTerm,eq,fromIdClause(cert.clause)))
            case kernel.Assume() =>
              val atom = cert.clause.lits.filter(_.isPositive).toList match {
                case List(lit) => lit.atom
                case _         => throw new Exception("METIS Bug!")
              }
              mkTuple(
                StateValue.mkStringValue("assume"),
                proofscriptOfAtom(fromTerm,eq,fromIdAtom(atom)))
            case kernel.Refl() =>
              cert.clause.lits.toList match {
                case List(Literal(true,Eql(x,y))) if x == y =>
                  mkTuple(
                    StateValue.mkStringValue("refl"),
                    proofscriptOfTerm(fromTerm,fromIdTerm(x)))
                case _ => throw new Exception("METIS Bug!")
              }
            case kernel.Equality(cursor,term) =>
              mkTuple(
                StateValue.mkStringValue("equality"),
                proofscriptOfTerm(fromTerm,fromIdTerm(term)),
                proofscriptOfLiteral(fromTerm,eq,fromIdLiteral(cursor.top)),
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
                MapValue(θ.θ.toAscList.map {
                  case ((vn,vid),tm) =>
                    (if (vid == 0) IntValue(vn) else
                      (SetValue(Set(mkTuple(IntValue(vn),IntValue(vid))))),
                      proofscriptOfTerm(fromTerm,fromIdTerm(tm)))
                }.toMap,true),
                proofscriptOfCertificate(thm))
            case kernel.Resolve(atm,pos,neg) =>
              mkTuple(
                StateValue.mkStringValue("resolve"),
                proofscriptOfAtom(fromTerm,eq,fromIdAtom(atm)),
                proofscriptOfCertificate(pos),
                proofscriptOfCertificate(neg))
          }
        }
        import KernelInstances._
        val res = icl.resolution(cls.toList, null)
        val allThms = res.distance_nextThms.takeWhile(_.isDefined).flatten
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
