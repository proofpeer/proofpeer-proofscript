package proofpeer.proofscript.naiveinterpreter

import proofpeer.proofscript.frontend._
import proofpeer.proofscript.logic._
import proofpeer.indent._
import proofpeer.general.algorithms.TopologicalSort

class Interpreter(executionEnvironment : ExecutionEnvironment) {

  import ExecutionEnvironment._

  private val parser = new ProofScriptParser()

  def theoryIsRooted(namespace : Namespace) : Boolean = {
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

  private def addFault(namespace : Namespace, pos : SourcePosition, error : String) {
    val p =
      if (pos == null) 
        new SourcePosition { val source = executionEnvironment.lookupTheory(namespace).get.source; val span = None }
      else
        pos
    executionEnvironment.addFaults(namespace, Vector(Fault(pos, error)))
  }

  private def addFault(namespace : Namespace, error : String) {
    addFault(namespace, null, error)
  }

  private def computeRootingParticipants(theories : Set[Namespace]) : Map[Namespace, (TheoryHeader, Set[Namespace])] = {
    var rootingCandidates = theories.toList
    var processedCandidates = Set[Namespace]()
    var rootingParticipants : Map[Namespace, (TheoryHeader, Set[Namespace])] = Map()
    while (!rootingCandidates.isEmpty) {
      val ns = rootingCandidates.head
      rootingCandidates = rootingCandidates.tail
      processedCandidates = processedCandidates + ns
      executionEnvironment.lookupTheory(ns) match {
        case None => throw new RuntimeException("theory '" + ns + "' not found")
        case Some(thy : RootedTheory) =>
        case Some(thy) if !thy.isFaulty =>
          parseTheoryHeader(thy) match {
            case Left(header) =>
              val participatingParents = header._3.filter(ns => !theoryIsRooted(ns))
              var predecessors = participatingParents
              for (parent <- participatingParents) {
                if (!processedCandidates.contains(parent)) {
                  if (!executionEnvironment.lookupTheory(parent).isDefined) {
                    addFault(ns, "parent theory " + parent + " does not exist")
                    predecessors = predecessors - parent
                  } else
                    rootingCandidates = parent :: rootingCandidates
                }
              }
              rootingParticipants = rootingParticipants + (ns -> (header, predecessors))
            case Right((pos, error)) =>
              addFault(ns, pos, error)
          }
        case _ =>
      }
    }
    rootingParticipants
  }

  def rootTheories(theories : Set[Namespace]) { 
    val rootingParticipants = computeRootingParticipants(theories)
    val rootingGraph = rootingParticipants.mapValues(_._2)
    val (sorted, unsorted) = TopologicalSort.compute(rootingGraph)
    val sortedSet = sorted.toSet
    for ((namespace, parents) <- unsorted) {
      val cyclicParents = parents -- sortedSet
      if (cyclicParents.size == 1)
        addFault(namespace, null, "cyclic dependency on parent theory " + cyclicParents.head)
      else 
        addFault(namespace, null, "cyclic dependency involving (one of) these parent theories: " + (cyclicParents.mkString(", ")))
    }
    for (namespace <- sorted) {
      val (_, version, parents, _) = rootingParticipants(namespace)._1
      if (namespace == Namespace.root) {
        if (!parents.isEmpty) addFault(namespace, "theory \\root cannot have any parent theories")
        else if (version.isEmpty) addFault(namespace, "theory \\root has no ProofScript version defined")
        else executionEnvironment.finishedRooting(namespace, parents, version)
      } else {
        if (parents.isEmpty) addFault(namespace, "the theory doesn't extend any parent theories")
        else {
          val faultyParents = parents.filter(ns => !theoryIsRooted(ns))
          if (!faultyParents.isEmpty) addFault(namespace, "cannot compile these parent theories: " + (faultyParents.mkString(", ")))
          else executionEnvironment.finishedRooting(namespace, parents, None)
        }
      }
    }
  }

}