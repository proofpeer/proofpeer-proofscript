package proofpeer.proofscript.naiveinterpreter

import java.io.File
import proofpeer.proofscript.frontend._
import proofpeer.proofscript.logic._
import proofpeer.proofscript.serialization.{Storage, UniquelyIdentifiableStore}
import proofpeer.indent._

class Rooting(executionEnvironment : ExecutionEnvironment) {

  import ExecutionEnvironment._

  val parser = new ProofScriptParser()

  private def theoryIsRooted(namespace : Namespace) : Boolean = {
    executionEnvironment.lookupTheory(namespace) match {
      case Some(_ : RootedTheory) => true
      case _ => false
    }
  }

  private type TheoryHeader = (Namespace, Option[String], Set[Namespace], Aliases)
  private type TheoryHeaderError = (SourcePosition, String)

  private def interpretTheoryHeader(namespace : Namespace, thy : ParseTree.Block) : Either[TheoryHeader, TheoryHeaderError] = {
    if (thy.statements.isEmpty) {
      Right((null, "missing theory header"))
    } else {
      val (ns, parents, aliases) = 
        thy.statements.head match {
          case ParseTree.STTheory(declaredNamespace, _aliases, parents) =>
            var ns : Namespace = null
            val spos = thy.statements.head.sourcePosition
            if (declaredNamespace.isAbsolute || declaredNamespace.components.size != 1) {
              return Right((spos, "theory name cannot be '" + declaredNamespace + "' but should be just '" + namespace.lastComponent + "'"))
            } else {
              val declared = declaredNamespace.relativeTo(namespace.parent.get)
              if (declared != namespace) {
                return Right((spos, "declared namespace '" + declared + "' does not match expected namespace '" + namespace + "'"))
              }
              ns = declared
            }
            val aliases = new Aliases(ns.parent.get, _aliases.map(a => Alias(a._1.name, a._2)))
            val ps = parents.map (aliases.resolve(_))
            (ns, ps.toSet, aliases)
          case _ =>
            return Right((null, "missing theory header"))
        }
      val tail = thy.statements.tail
      import ParseTree._
      if (tail.isEmpty) Left((ns, None, parents, aliases))
      else tail.head match {
        case STVal(_, Block(Vector(STExpr(StringLiteral(codepoints))))) =>
          val version = proofpeer.general.StringUtils.fromCodePoints(codepoints)
          Left((ns, Some(version), parents, aliases)) 
        case _ => Left((ns, None, parents, aliases))
      }
    }
  }

  private def parseTheoryHeader(thy : Theory) : Either[TheoryHeader, TheoryHeaderError] = {
    class AcceptHeader(parseProofscriptVersion : Boolean) {
      var state = 0
      def accept(line : String) : Boolean = {
        val isIndented = (line == "" || line.startsWith(" "))
        state match {
          case 0 =>
            if (line.startsWith("theory")) {
              state = 1
              true
            } else false
          case 1 =>
            if (isIndented) true
            else if (line.startsWith("extends")) {
              state = 2
              true
            } else if (parseProofscriptVersion && line.startsWith("val ProofScriptVersion = ")) {
              state = 3
              true
            } else false
          case 2 =>
            if (isIndented) true
            else if (!parseProofscriptVersion) false
            else if (line.startsWith("val ProofScriptVersion = ")) {
              state = 3
              true
            } else false
          case _ => false
        }
      }
    }
    val isRoot = thy.namespace == Namespace("\\root")
    val document = Document.fromString(thy.content, None, (new AcceptHeader(isRoot)).accept _)
    val header = document.getText(0, document.size)
    import ProofScriptParser._
    parser.parseFromSource(thy.source, header) match {
      case SuccessfulParse(block) =>
        interpretTheoryHeader(thy.namespace, block)
      case AmbiguousParse(pos) =>
        Right((pos, "ambiguous theory header"))
      case FailedParse(pos) =>
        Right((pos, "invalid theory header"))
    }
  }

  def rootTheories(theories : Set[Namespace]) { 
    var waitingQueue : Set[Namespace] = theories.filter(n => !theoryIsRooted(n))
    for (ns <- theories) {
      println("rooting theory '" + ns + "'")
      executionEnvironment.lookupTheory(ns) match {
        case None =>
          throw new RuntimeException("theory '" + ns + "' not found")
        case Some(thy : RootedTheory) =>
          println("theory is already rooted")
        case Some(thy) =>
          val header = parseTheoryHeader(thy)
          println(header)          
      }
      println("-------------------------------------------------")
    }
  }

}