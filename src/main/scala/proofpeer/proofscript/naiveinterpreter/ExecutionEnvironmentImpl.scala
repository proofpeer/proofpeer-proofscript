package proofpeer.proofscript.naiveinterpreter

import proofpeer.general._
import proofpeer.proofscript.frontend._
import proofpeer.proofscript.logic._
import proofpeer.proofscript.serialization._

trait ExecutionEnvironmentAdapter {

  /** Returns either None if no such theory exists in the system, or Some((source, contentKey, content, optionalTheoryData)). */
  def lookupTheory(namespace : Namespace) : Option[(Source, Bytes, String, Option[Bytes])]

  /** Can be called multiple times to override previously stored data. */
  def storeTheoryData(namespace : Namespace, theoryData : Bytes)

  def loadCompileKeyData(compileKey : Bytes) : Option[Bytes]

  /** Can be called multiple times to override previously stored data. */
  def storeCompileKeyData(compileKey : Bytes, data : Bytes)

}

class ExecutionEnvironmentImpl(eeAdapter : ExecutionEnvironmentAdapter, loadNotification : Namespace => Unit = _ => ()) extends ExecutionEnvironment {

  import ExecutionEnvironment._
  import ExecutionEnvironmentImpl._

  private var theories : Map[Namespace, Theory] = Map()
  private var ancestors : Map[Namespace, Set[String]] = Map()
  private var storedBytes : Map[Namespace, Bytes] = Map()

  val kernel = Kernel.createDefaultKernel()

  private def bytecodeOfTheory(namespace : String) : Option[Bytes] = {
    val ns = Namespace(namespace)
    storedBytes.get(ns) match {
      case Some(bytes) => 
        storedBytes = storedBytes - ns
        Some(bytes)
      case None => None
    }
  }

  private val store = new MultiStore(true, bytecodeOfTheory _, n => ancestors(n))
  private val kernelSerializers = kernel.serializers(store)

  private type RootingData = (Bytes, Set[Namespace], Aliases, String)
  private type TheoryData = (Option[RootingData], Vector[Fault])
  private type CompileKeyData = State

  private val AliasSerializer = new BasicAliasSerializer(BasicNamespaceSerializer)
  private val AliasesSerializer = new BasicAliasesSerializer(BasicNamespaceSerializer, AliasSerializer)
  private val RootingDataSerializer : Serializer[RootingData] = QuadrupleSerializer(BytesSerializer,
    SetSerializer(BasicNamespaceSerializer), AliasesSerializer, StringSerializer)
  private val TheoryDataSerializer : Serializer[TheoryData] = PairSerializer(OptionSerializer(RootingDataSerializer), 
    VectorSerializer(FaultSerializer()))
  private val StateSerializer = new CustomizableStateSerializer(store, kernelSerializers)
  //private val OutputSerializer = CapturedOutputSerializer(kernelSerializers.NamespaceSerializer)
  private val CompileKeyDataSerializer : Serializer[CompileKeyData] = StateSerializer
  private val CompileKeyDataBytesSerializer : Serializer[(Bytes, Bytes)] = PairSerializer(BytesSerializer, BytesSerializer)

  private def updateTheory[A <: Theory](thy : A) : A = {
    theories = theories + (thy.namespace -> thy)
    thy match {
      case thy : RootedTheory =>
        var a : Set[String] = Set(thy.namespace.toString.toLowerCase)
        for (parent <- thy.parents) {
          a = a ++ ancestors(parent)
        }
        ancestors = ancestors + (thy.namespace -> a)
      case _ =>
    }
    thy
  }

  private def loadTheory(namespace : Namespace) : Option[Theory] = {
    eeAdapter.lookupTheory(namespace) match {
      case None => None
      case Some((source, contentKey, content, optionalTheoryData)) =>
        optionalTheoryData match {
          case None => Some(updateTheory(TheoryImpl(namespace, source, content, contentKey, Vector())))
          case Some(theoryDataBytes) =>
            TheoryDataSerializer.deserialize(Bytes.decode(theoryDataBytes)) match {
              case (None, faults) =>
                Some(updateTheory(TheoryImpl(namespace, source, content, contentKey, faults)))  
              case (Some((compileKey, parents, aliases, proofscriptVersion)), faults) =>
                // lookup all the parents of the theory first; this is necessary for 2 reasons:
                // 1. when loading the state of a theory, we might reference the states of earlier theories,
                //    and this means that storedBytes must have been primed with the data for those earlier theories.
                // 2. in order to complete the context with the kernel, its parent contexts must have been completed already
                for (parent <- parents) {
                  if (!lookupTheory(parent).isDefined) 
                    throw new RuntimeException("cannot load parent theory '" + parent + "' of theory '" + namespace + "'")
                }
                eeAdapter.loadCompileKeyData(compileKey) match {
                  case None => Some(updateTheory(RootedTheoryImpl(namespace, source, content, contentKey, faults,
                    parents, aliases, compileKey, proofscriptVersion)))
                  case Some(compileKeyDataBytes) =>
                    val (encodedBytes, storeBytes) = CompileKeyDataBytesSerializer.deserialize(Bytes.decode(compileKeyDataBytes))
                    storedBytes = storedBytes + (namespace -> storeBytes)
                    val state = CompileKeyDataSerializer.deserialize(Bytes.decode(encodedBytes))
                    val thy = CompiledTheoryImpl(namespace, source, content, contentKey, faults, 
                      parents, aliases, compileKey, proofscriptVersion, state)
                    kernel.restoreCompletedNamespace(thy.parents, thy.aliases, thy.state.context)
                    updateTheory(thy)
                    loadNotification(thy.namespace)
                    Some(thy)
                }
            }
        }
    }    
  }

  def lookupTheory(namespace : Namespace) : Option[Theory] = {
    theories.get(namespace) match {
      case Some(thy) => Some(thy)
      case None => loadTheory(namespace)
    }
  }

  private def saveCompileKeyData(thy : Theory) {
    thy match {
      case thy : CompiledTheory =>
        store.setCurrentNamespace(thy.namespace)
        val compileKeyData : CompileKeyData = thy.state
        val encoding = Bytes.encode(CompileKeyDataSerializer.serialize(compileKeyData))
        val storeBytes = store.toBytes(thy.namespace).get
        val bytes = Bytes.encode(CompileKeyDataBytesSerializer.serialize((encoding, storeBytes)))
        eeAdapter.storeCompileKeyData(thy.compileKey, bytes)
      case _ => throw new RuntimeException("there is no compile key data to save for non-compiled theory '" + thy.namespace + "'")
    }
  }

  private def saveTheoryData(thy : Theory) {
    thy match {
      case t : RootedTheory =>
        val data : TheoryData = (Some(t.compileKey, t.parents, t.aliases, t.proofscriptVersion), t.faults)
        eeAdapter.storeTheoryData(thy.namespace, Bytes.encode(TheoryDataSerializer.serialize(data)))
      case t : Theory =>
        val data : TheoryData = (None, t.faults)
        eeAdapter.storeTheoryData(thy.namespace, Bytes.encode(TheoryDataSerializer.serialize(data)))
    }
  }

  def addFaults(namespace : Namespace, faults : Vector[Fault]) : Theory = {
    lookupTheory(namespace) match {
      case Some(t : CompiledTheory) => 
        val thy = updateTheory(CompiledTheoryImpl(t.namespace, t.source, t.content, t.contentKey, t.faults ++ faults, 
          t.parents, t.aliases, t.compileKey, t.proofscriptVersion, t.state))
        saveCompileKeyData(thy)
        thy
      case Some(t : RootedTheory) => 
        val thy = updateTheory(RootedTheoryImpl(t.namespace, t.source, t.content, t.contentKey, t.faults ++ faults, 
          t.parents, t.aliases, t.compileKey, t.proofscriptVersion))
        saveTheoryData(thy)
        thy
      case Some(t : Theory) => 
        val thy = updateTheory(TheoryImpl(t.namespace, t.source, t.content, t.contentKey, t.faults ++ faults)) 
        saveTheoryData(thy)
        thy
      case _ =>
        throw new RuntimeException("cannot add faults to theory '" + namespace + "'")
    }
  }

  def finishedRooting(namespace : Namespace, parents : Set[Namespace], aliases : Aliases, proofscriptVersion : Option[String]) : RootedTheory = 
  {
    lookupTheory(namespace) match {
      case Some(t : RootedTheory) =>
        throw new RuntimeException("cannot finish rooting of already rooted theory '" + namespace + "'")
      case Some(t : Theory) =>
        var version = proofscriptVersion
        var parentCompileKeys : Vector[Bytes] = Vector()
        val vparents = parents.toVector.sortBy(p => p.toString.toLowerCase)
        for (parent <- vparents) {
          lookupTheory(parent) match {
            case Some(parentThy : RootedTheory) =>
              version = Some(parentThy.proofscriptVersion)
              parentCompileKeys = parentCompileKeys :+ parentThy.compileKey
            case _ =>
              throw new RuntimeException("cannot finish rooting of theory '" + namespace + "' because parent theory '" + parent + "' is not rooted")
          }
        }
        if (parents.isEmpty && namespace != Namespace.root) throw new RuntimeException("theory '" + namespace + "' does not have any parent theories")
        if (version.isEmpty) throw new RuntimeException("theory '" + namespace + "' doesn't have a version of ProofScript associated with it")
        val compileKey = Bytes.encode((namespace.toString.toLowerCase, t.contentKey, parentCompileKeys)).sha256
        val thy = updateTheory(RootedTheoryImpl(t.namespace, t.source, t.content, t.contentKey, t.faults, 
          parents, aliases, compileKey, version.get))
        saveTheoryData(thy)
        loadTheory(thy.namespace).get.asInstanceOf[RootedTheory]
      case _ => throw new RuntimeException("cannot finish rooting of theory '" + namespace + "'")
    }
  }

  def finishedCompiling(namespace : Namespace, state : State) : CompiledTheory = {
    lookupTheory(namespace) match {
      case Some(t : CompiledTheory) =>
        throw new RuntimeException("cannot finish compiling of already compiled theory '" + namespace + "'")
      case Some(t : RootedTheory) =>
        for (parent <- t.parents) {
          lookupTheory(parent) match {
            case Some(_ : CompiledTheory) =>            
            case _ => 
              throw new RuntimeException("cannot finish compiling of theory '" + namespace + "' because parent theory '" + parent + "' is not compiled")            
          }
        }
        val thy = updateTheory(CompiledTheoryImpl(t.namespace, t.source, t.content, t.contentKey, t.faults, 
          t.parents, t.aliases, t.compileKey, t.proofscriptVersion, state))
        saveCompileKeyData(thy)
        thy
      case _ => throw new RuntimeException("cannot finish rooting of theory '" + namespace + "'")
    }
  }

}

object ExecutionEnvironmentImpl {

  import ExecutionEnvironment._
  import proofpeer.general.Bytes

  private case class TheoryImpl(namespace : Namespace, source : Source, content : String, contentKey : Bytes, faults : Vector[Fault]) extends Theory 

  private case class RootedTheoryImpl(namespace : Namespace, source : Source, content : String, contentKey : Bytes, faults : Vector[Fault],
    parents : Set[Namespace], aliases : Aliases, compileKey : Bytes, proofscriptVersion : String) extends RootedTheory

  private case class CompiledTheoryImpl(namespace : Namespace, source : Source, content : String, contentKey : Bytes, faults : Vector[Fault],
    parents : Set[Namespace], aliases : Aliases, compileKey : Bytes, proofscriptVersion : String, state : State) extends CompiledTheory

}