package proofpeer.proofscript.naiveinterpreter

import proofpeer.proofscript.frontend._
import proofpeer.proofscript.logic._
import proofpeer.indent._
import proofpeer.general.algorithms.TopologicalSort
import proofpeer.proofscript.serialization._
import proofpeer.general.Bytes
import proofpeer.proofscript.ProofScriptManager

trait InterpreterNotificationHandler {
  def startCompiling(theory : Namespace)
  def finishedCompiling(theory : Namespace, success : Boolean)
  def skippedFaultyTheory(theory : Namespace)
  def skippedTheoryWithFaultyParents(theory : Namespace)
}

object NoInterpreterNotificationHandler extends InterpreterNotificationHandler {
  def startCompiling(theory : Namespace) {}
  def finishedCompiling(theory : Namespace, success : Boolean)  {} 
  def skippedFaultyTheory(theory : Namespace) {}
  def skippedTheoryWithFaultyParents(theory : Namespace) {}
}

class Interpreter(executionEnvironment : ExecutionEnvironment) {

  import ExecutionEnvironment._

  private val parser = new ProofScriptParser()  
  private val kernel = executionEnvironment.kernel

  def theoryIsRooted(namespace : Namespace) : Boolean = {
    executionEnvironment.lookupTheory(namespace) match {
      case Some(_ : RootedTheory) => true
      case _ => false
    }
  }

  def theoryIsCompiled(namespace : Namespace) : Boolean = {
    executionEnvironment.lookupTheory(namespace) match {
      case Some(_ : CompiledTheory) => true
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
            } else if (parseProofscriptVersion && line.startsWith("val versionOfProofScript = ")) {
              state = 3
              true
            } else false
          case 2 =>
            if (isIndented) true
            else if (!parseProofscriptVersion) false
            else if (line.startsWith("val versionOfProofScript = ")) {
              state = 3
              true
            } else false
          case _ => false
        }
      }
    }
    val isRoot = thy.namespace == Namespace("\\root")
    val document = Document.fromString(thy.content, Some(2), (new AcceptHeader(isRoot)).accept _)
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

  private def unknownPosition(namespace : Namespace) : SourcePosition = {
    new SourcePosition { val source = executionEnvironment.lookupTheory(namespace).get.source; val span = None }    
  }

  private def addFault(namespace : Namespace, pos : SourcePosition, error : String) {
    val p =
      if (pos == null) 
        unknownPosition(namespace)
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

  private def rootTheories(theories : Set[Namespace]) { 
    val rootingParticipants = computeRootingParticipants(theories)
    val rootingGraph = rootingParticipants.mapValues(_._2)
    val (sorted, unsorted) = TopologicalSort.compute(rootingGraph)
    val sortedSet = sorted.toSet
    for ((namespace, parents) <- unsorted) {
      val cyclicParents = parents -- sortedSet
      if (cyclicParents.size == 1)
        addFault(namespace, null, "invalid (possibly cyclic) dependency on parent theory " + cyclicParents.head)
      else 
        addFault(namespace, null, "invalid (possibly cyclic) dependency involving (one of) these parent theories: " + (cyclicParents.mkString(", ")))
    }
    for (namespace <- sorted) {
      val (_, version, parents, aliases) = rootingParticipants(namespace)._1
      if (namespace == Namespace.root) {
        if (!parents.isEmpty) addFault(namespace, "theory \\root cannot have any parent theories")
        else if (version.isEmpty) addFault(namespace, "theory \\root has no ProofScript version defined")
        else if (version.get != ProofScriptManager.currentVersion)
          addFault(namespace, "unsupported ProofScript version: " + version.get + ", expected version is: " + ProofScriptManager.currentVersion)
        else executionEnvironment.finishedRooting(namespace, parents, aliases, version)
      } else {
        if (parents.isEmpty) addFault(namespace, "the theory doesn't extend any parent theories")
        else {
          val faultyParents = parents.filter(ns => !theoryIsRooted(ns))
          if (!faultyParents.isEmpty) addFault(namespace, "cannot compile these parent theories: " + (faultyParents.mkString(", ")))
          else executionEnvironment.finishedRooting(namespace, parents, aliases, None)
        }
      }
    }
  }

  private def parentsOfNamespace(namespace : Namespace) : Set[Namespace] =
    kernel.parentsOfNamespace(namespace) match {
      case None => Utils.failwith("no such namespace: " + namespace)
      case Some(namespaces) => namespaces
    }

  private def logicLocalNames(namespace : Namespace) : Set[IndexedName] =
    kernel.contextOfNamespace(namespace) match {
      case None => Utils.failwith("no completed context for namespace: "+namespace)
      case Some(context) => 
        var locals : Set[IndexedName] = Set()
        for (name <- context.localConstants) {
          if (name.namespace.isDefined) locals = locals + name.name
        }
        locals
    }

  private def completedStates(namespace : Namespace) : Option[State] = {
    executionEnvironment.lookupTheory(namespace) match {
      case Some(theory : CompiledTheory) => Some(theory.state)
      case _ => None 
    }
  }

  private def programLocalNames(namespace : Namespace) : Set[String] = {
    completedStates(namespace).get.env.nonlinear.keySet
  }

  private val logicNamespaceResolution = new NamespaceResolution[IndexedName](parentsOfNamespace _, logicLocalNames _)
  private val programNamespaceResolution = new NamespaceResolution[String](parentsOfNamespace _, programLocalNames _)

  private def rootState : State = {
    val environment : Map[String, StateValue] = 
      NativeFunctions.environment.mapValues(f => NativeFunctionValue(f))
    val context = kernel.createNewNamespace(Kernel.root_namespace, Set(), 
      new Aliases(Kernel.root_namespace.parent.get, List()))
    new State(context, State.Env(environment, Map()), Collect.Zero, false)
  }  

  private def makeState(namespace : Namespace, parentNamespaces : Set[Namespace], aliases : Aliases) : State = {
    for (p <- parentNamespaces) {
      if (!completedStates(p).isDefined) throw new RuntimeException("makeState: parent " + p + " has not been compiled yet")
    }
    val context = kernel.createNewNamespace(namespace, parentNamespaces, aliases)
    new State(context, State.Env(Map(), Map()), Collect.Zero, false)
  } 

  private final val MAX_TRACE_LENGTH = 1000

  private def parseTheory(thy : RootedTheory) : Option[ParseTree.Block] = {
    import ProofScriptParser._
    parser.parseFromSource(thy.source, thy.content) match {
      case SuccessfulParse(block) =>
        Some(block)
      case AmbiguousParse(pos) =>
        addFault(thy.namespace, pos, "parsing ambiguity detected")
        None
      case FailedParse(pos) =>
        addFault(thy.namespace, pos, "parsing failed")
        None
    }
  }

  private def evalTheory(thy: RootedTheory) : Boolean = {
    val output = new DefaultOutputCapture()
    def dumpOutput() {
      executionEnvironment.storeOutput(thy.compileKey, output.export())
    }
    val evaluator = new Eval(completedStates _, kernel, programNamespaceResolution, logicNamespaceResolution, thy.aliases, thy.namespace, output)
    val state : State = 
      if (thy.namespace == Kernel.root_namespace) 
        rootState
      else 
        makeState(thy.namespace, thy.parents, thy.aliases) 
    val parsetree = 
      parseTheory(thy) match {
        case None => return false
        case Some(block) => block
      }
    val result : Either[Result[State], String] = 
      try {
        Left(evaluator.eval(state, ParseTree.Block(parsetree.statements.tail)))
      } catch {
        case x : StackOverflowError =>
          Right("cannot evaluate theory because the stack overflowed")
        case x : OutOfMemoryError =>
          Right("cannot evaluate theory because memory ran out")
        case x : Exception =>
          x.printStackTrace()
          Right("cannot evaluate theory because an exception occurred: " + x.getMessage())
      }
    result match {
      case Left(Failed(trace, error)) =>
        dumpOutput()
        var positions = trace.reverse
        if (positions.size > MAX_TRACE_LENGTH) positions = positions.take(MAX_TRACE_LENGTH)
        val pos : SourcePosition = 
          if (positions.isEmpty) unknownPosition(thy.namespace) else positions.head._1
        val fault = Fault(pos, error, positions.toVector)
        executionEnvironment.addFaults(thy.namespace, Vector(fault))
        false
      case Left(Success(state, _)) => 
        dumpOutput()
        if (state.context.hasAssumptions && state.context.namespace != Kernel.root_namespace) {
          addFault(thy.namespace, "theory fails because it introduces axioms (which only the root theory can do)")
          false
        } else {
          val completed = kernel.completeNamespace(state.context)
          val completedState = new State(completed, state.env.freeze, Collect.Zero, false)
          executionEnvironment.finishedCompiling(thy.namespace, completedState) 
          true 
        }
      case Right(error) =>
        dumpOutput()
        addFault(thy.namespace, error)
        false
    }
  }  

  /** Returns true if the theory has been compiled successfully, otherwise false. */
  private def compileTheory(theory : Namespace, handler : InterpreterNotificationHandler) : Boolean = {
    executionEnvironment.lookupTheory(theory) match {
      case Some(theory : Theory) if theory.isFaulty => 
        handler.skippedFaultyTheory(theory.namespace)
        false
      case Some(theory : CompiledTheory) => 
        true
      case Some(rootedTheory : RootedTheory) =>
        for (parent <- rootedTheory.parents) {
          if (!compileTheory(parent, handler)) {
            addFault(rootedTheory.namespace, "parent theory does not compile: " + parent)
            handler.skippedTheoryWithFaultyParents(rootedTheory.namespace)
            return false
          }
        }
        handler.startCompiling(rootedTheory.namespace)
        val success = evalTheory(rootedTheory)
        handler.finishedCompiling(rootedTheory.namespace, success)
        success
      case _ => throw new RuntimeException("cannot compile non-existing or non-rooted theory '" + theory + "'")
    }
  }

  private class SuppressDuplicateNotifications(handler : InterpreterNotificationHandler) extends InterpreterNotificationHandler {
    private var alreadyVisited : Set[Namespace] = Set()
    def startCompiling(theory : Namespace) {
      handler.startCompiling(theory)
    }
    def finishedCompiling(theory : Namespace, success : Boolean)  {
      handler.finishedCompiling(theory, success)
      alreadyVisited = alreadyVisited + theory
    } 
    def skippedFaultyTheory(theory : Namespace) {
      if (!alreadyVisited.contains(theory)) {
        alreadyVisited = alreadyVisited + theory
        handler.skippedFaultyTheory(theory)
      }      
    }
    def skippedTheoryWithFaultyParents(theory : Namespace) {
      if (!alreadyVisited.contains(theory)) {
        alreadyVisited = alreadyVisited + theory
        handler.skippedTheoryWithFaultyParents(theory)
      }      
    }
  }

  def compileTheories(theories : Set[Namespace], handler : InterpreterNotificationHandler = NoInterpreterNotificationHandler) {
    val h = new SuppressDuplicateNotifications(handler)
    rootTheories(theories)
    for (theory <- theories) compileTheory(theory, h)
  }

}
