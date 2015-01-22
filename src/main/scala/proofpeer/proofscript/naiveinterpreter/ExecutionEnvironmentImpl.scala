package proofpeer.proofscript.naiveinterpreter

import proofpeer.general.Bytes
import proofpeer.proofscript.frontend._
import proofpeer.proofscript.logic._
import proofpeer.proofscript.serialization._

trait ExecutionEnvironmentAdapter {

  /** Returns either None if no such theory exists in the system, or Some(((source, content, contentKey), rootingData)). 
    * The rootingData might be None if no rooting data has been stored yet via storeRootingData. */
  def lookupTheory(namespace : Namespace) : Option[((Source, Bytes, String), Option[Bytes])]

  def storeRootingData(namespace : Namespace, rootingData : Bytes)

  def loadCompiledData(compileKey : Bytes) : Option[Bytes]

  def storeCompiledData(compileKey : Bytes, info : Bytes)

}

class ExecutionEnvironmentImpl(eeAdapter : ExecutionEnvironmentAdapter) extends ExecutionEnvironment {

  import ExecutionEnvironment._
  import ExecutionEnvironmentImpl._

  private var theories : Map[Namespace, Theory] = Map()

  val kernel = Kernel.createDefaultKernel()

  private def bytecodeOfTheory(namespace : String) : Option[Bytes] = {
    lookupTheory(Namespace(namespace)) match {
      case Some(theory : RootedTheory) => eeAdapter.loadCompiledData(theory.compileKey)
      case _ => None
    }
  }

  private val store = new MultiStore(true, bytecodeOfTheory _)
  private val stateSerializer = new CustomizableStateSerializer(store, kernel.serializers(store))

  /*private def loadTheory(theory : CompiledTheory) {
    if (states.lookup(theory.namespace).isEmpty) {
      for (parent <- theory.parents) 
        loadTheory(lookupTheory(parent).get.asInstanceOf[CompiledTheory])
      val stateId = store.firstIdOf(theory.namespace)
      val state = stateSerializer.deserialize(stateId).asInstanceOf[State]
      states.register(theory.namespace, state)
      kernel.completeNamespace(state.context)
    }
  }*/


  def lookupTheory(namespace : Namespace) : Option[Theory] = {
    throw new RuntimeException("not implemented yet")
  }

  private def updateTheory(thy : Theory) : Theory = {
    theories = theories + (thy.namespace -> thy)
    thy
  }

  def addFaults(namespace : Namespace, faults : Vector[Fault]) : Theory = {
    throw new RuntimeException("not implemented yet")
/*    
    lookupTheory(namespace) match {
      case Some(thy : LocalTheory) =>
        updateTheory(LocalTheory(thy.namespace, thy.source, thy.content, thy.contentKey, thy.faults ++ faults))
      case Some(thy : LocalRootedTheory) =>
        updateTheory(LocalRootedTheory(thy.namespace, thy.source, thy.content, thy.contentKey, thy.faults ++ faults, thy.parents, 
          thy.aliases, thy.compileKey, thy.proofscriptVersion))
      case Some(thy : LocalCompiledTheory) =>
        updateTheory(LocalCompiledTheory(thy.namespace, thy.source, thy.content, thy.contentKey, thy.faults ++ faults, thy.parents,
          thy.aliases, thy.compileKey, thy.proofscriptVersion, thy.parseTree, thy.state, thy.capturedOutput))
      case _ =>
        throw new RuntimeException("cannot add faults to theory '" + namespace + "'")
    }*/
  }

  def finishedRooting(namespace : Namespace, parents : Set[Namespace], aliases : Aliases, proofscriptVersion : Option[String]) : RootedTheory = {
    throw new RuntimeException("not implemented yet")

/*    lookupTheory(namespace) match {
      case Some(thy : LocalTheory) =>
        var version = proofscriptVersion
        var parentCompileKeys : Vector[Bytes] = Vector()
        val vparents = parents.toVector.sortBy(p => p.toString.toLowerCase)
        for (parent <- vparents) {
          lookupTheory(parent) match {
            case Some(parentThy : RootedTheory) =>
              version = Some(parentThy.proofscriptVersion)
              parentCompileKeys = parentCompileKeys :+ parentThy.compileKey
            case _ =>
              throw new RuntimeException("cannot finish rooting of theory '" + namespace + "' because of parent theory '" + parent + "'")
          }
        }
        if (parents.isEmpty && namespace != Namespace.root) throw new RuntimeException("theory '" + namespace + "' does not have any parent theories")
        if (version.isEmpty) throw new RuntimeException("theory '" + namespace + "' doesn't have a version of ProofScript associated with it")
        val compileKey = Bytes.encode((thy.contentKey, parentCompileKeys)).sha256
        val rootedTheory = LocalRootedTheory(thy.namespace, thy.source, thy.content, thy.contentKey, thy.faults, parents, aliases, compileKey, version.get)
        updateTheory(rootedTheory)
        rootedTheory
      case _ => 
        throw new RuntimeException("cannot finish rooting of theory '" + namespace + "'")
    }*/
  }

  def finishedCompiling(namespace : Namespace, parseTree : ParseTree.Block, state : State, capturedOutput : Output.Captured) : CompiledTheory = {
    throw new RuntimeException("not implemented yet")

/*    lookupTheory(namespace) match {
      case Some(thy : LocalRootedTheory) =>
        val compiledTheory = LocalCompiledTheory(thy.namespace, thy.source, thy.content, thy.contentKey, thy.faults, thy.parents, 
          thy.aliases, thy.compileKey, thy.proofscriptVersion, parseTree, state, capturedOutput)
        updateTheory(compiledTheory)
        compiledTheory
      case _ => throw new RuntimeException("cannot finish compiling of theory '" + namespace + "'")
    }*/
  }

}

object ExecutionEnvironmentImpl {

  import ExecutionEnvironment._
  import proofpeer.general.Bytes

  private case class TheoryImpl(namespace : Namespace, source : Source, content : String, contentKey : Bytes, faults : Vector[Fault]) extends Theory 

  private case class RootedTheoryImpl(namespace : Namespace, source : Source, content : String, contentKey : Bytes, faults : Vector[Fault],
    parents : Set[Namespace], aliases : Aliases, compileKey : Bytes, proofscriptVersion : String) extends RootedTheory

  private case class CompiledTheoryImpl(namespace : Namespace, source : Source, content : String, contentKey : Bytes, faults : Vector[Fault],
    parents : Set[Namespace], aliases : Aliases, compileKey : Bytes, proofscriptVersion : String, 
    parseTree : ParseTree.Block, state : State, capturedOutput : Output.Captured) extends CompiledTheory

}