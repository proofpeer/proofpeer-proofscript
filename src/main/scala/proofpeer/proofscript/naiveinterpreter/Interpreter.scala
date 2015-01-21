package proofpeer.proofscript.naiveinterpreter

import proofpeer.proofscript.frontend._
import proofpeer.proofscript.logic._
import proofpeer.indent._
import proofpeer.general.algorithms.TopologicalSort
import proofpeer.proofscript.serialization._
import proofpeer.general.Bytes

class Interpreter(executionEnvironment : ExecutionEnvironment) {

  import ExecutionEnvironment._

  private val parser = new ProofScriptParser()
  private val kernel = Kernel.createDefaultKernel()
  private val states = States.empty

  private def bytecodeOfTheory(namespace : String) : Option[Bytes] = {
    executionEnvironment.lookupTheory(Namespace(namespace)) match {
      case Some(theory : CompiledTheory) => Some(theory.compiledBytes)
      case _ => None
    }
  }

  private val store = new MultiStore(true, bytecodeOfTheory _)
  private val stateSerializer = new CustomizableStateSerializer(store, kernel.serializers(store))

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
      val (_, version, parents, aliases) = rootingParticipants(namespace)._1
      if (namespace == Namespace.root) {
        if (!parents.isEmpty) addFault(namespace, "theory \\root cannot have any parent theories")
        else if (version.isEmpty) addFault(namespace, "theory \\root has no ProofScript version defined")
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

  private def loadTheory(theory : CompiledTheory) {
    if (states.lookup(theory.namespace).isEmpty) {
      for (parent <- theory.parents) 
        loadTheory(executionEnvironment.lookupTheory(parent).get.asInstanceOf[CompiledTheory])
      val stateId = store.firstIdOf(theory.namespace)
      val state = stateSerializer.deserialize(stateId).asInstanceOf[State]
      states.register(theory.namespace, state)
      kernel.completeNamespace(state.context)
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

  private def programLocalNames(namespace : Namespace) : Set[String] = {
    states.lookup(namespace) match {
      case None => throw new RuntimeException("internal error: localNames of "+namespace)
      case Some(state) => state.env.freeze.nonlinear.keySet
    }
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

  private def makeState(states : States, namespace : Namespace, parentNamespaces : Set[Namespace], aliases : Aliases) : State = {
    for (p <- parentNamespaces) {
      if (!states.lookup(p).isDefined) throw new RuntimeException("makeState: parent " + p + " has not been compiled yet")
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
    val evaluator = new Eval(states, kernel, programNamespaceResolution, logicNamespaceResolution, thy.aliases, thy.namespace, DefaultOutput)
    val state : State = 
      if (thy.namespace == Kernel.root_namespace) 
        rootState
      else 
        makeState(states, thy.namespace, thy.parents, thy.aliases) 
    val parsetree = 
      parseTheory(thy) match {
        case None => return false
        case Some(block) => block
      }
    evaluator.evalBlock(state, ParseTree.Block(parsetree.statements.tail)) match {
      case Failed(trace, error) =>
        var positions = trace.reverse
        if (positions.size > MAX_TRACE_LENGTH) positions = positions.take(MAX_TRACE_LENGTH)
        val pos : SourcePosition = 
          if (positions.isEmpty) unknownPosition(thy.namespace) else positions.head._1
        val fault = Fault(pos, error, positions.toVector)
        executionEnvironment.addFaults(thy.namespace, Vector(fault))
        false
      case Success(state, _) => 
        if (state.context.hasAssumptions && state.context.namespace != Kernel.root_namespace) {
          addFault(thy.namespace, "theory fails because it introduces axioms (which only the root theory can do)")
          false
        } else {
          val completed = kernel.completeNamespace(state.context)
          val completedState = new State(completed, state.env.freeze, Collect.Zero, false)
          store.setCurrentNamespace(thy.namespace)
          stateSerializer.serialize(completedState)
          val bytecode = store.toBytes(thy.namespace).get
          executionEnvironment.finishedCompiling(thy.namespace, parsetree, bytecode)
          states.register(thy.namespace, completedState)
          true 
        }
    }
  }  

  /** Returns true if the theory has been compiled successfully, otherwise false. */
  private def compileTheory(theory : Namespace) : Boolean = {
    executionEnvironment.lookupTheory(theory) match {
      case Some(theory : Theory) if theory.isFaulty => false
      case Some(theory : CompiledTheory) => 
        loadTheory(theory) 
        true
      case Some(rootedTheory : RootedTheory) =>
        for (parent <- rootedTheory.parents) {
          if (!compileTheory(parent)) {
            addFault(rootedTheory.namespace, "parent theory does not compile: " + parent)
            return false
          }
        }
        evalTheory(rootedTheory)
      case _ => throw new RuntimeException("cannot compile non-existing or non-rooted theory '" + theory + "'")
    }
  }

  def compileTheories(theories : Set[Namespace]) {
    for (theory <- theories) compileTheory(theory)
  }

}