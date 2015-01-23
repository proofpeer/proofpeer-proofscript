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

  def loadCompileKeyData(compileKey : Bytes) : Bytes

  /** Can be called multiple times to override previously stored data. */
  def storeCompileKeyData(compileKey : Bytes, data : Bytes)

}

class ExecutionEnvironmentImpl(eeAdapter : ExecutionEnvironmentAdapter) extends ExecutionEnvironment {

  import ExecutionEnvironment._
  import ExecutionEnvironmentImpl._

  private var theories : Map[Namespace, Theory] = Map()
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

  private val store = new MultiStore(true, bytecodeOfTheory _)
  private val kernelSerializers = kernel.serializers(store)

  private type TheoryData = Either[(Set[Namespace], Bytes), Vector[Fault]] 
  private type RootingData = (Set[Namespace], Aliases, String)
  private type CompiledData = (ParseTree, Output.Captured, State)
  private type CompileKeyData = (RootingData, Option[CompiledData], Vector[Fault])

  private val StateSerializer = new CustomizableStateSerializer(store, kernelSerializers)
  private val OutputSerializer = CapturedOutputSerializer(kernelSerializers.NamespaceSerializer)
  private val TheoryDataSerializer : Serializer[TheoryData] = EitherSerializer(PairSerializer(
    SetSerializer(BasicNamespaceSerializer), BytesSerializer), VectorSerializer(FaultSerializer()))
  private val RootingDataSerializer : Serializer[RootingData] = TripleSerializer(
    SetSerializer(kernelSerializers.NamespaceSerializer), kernelSerializers.AliasesSerializer, StringSerializer)
  private val CompiledDataSerializer : Serializer[CompiledData]
    = TripleSerializer(StateSerializer.ParseTreeSerializer, OutputSerializer, StateSerializer)
  private val CompileKeyDataSerializer : Serializer[CompileKeyData] = 
    TripleSerializer(RootingDataSerializer, OptionSerializer(CompiledDataSerializer), 
      VectorSerializer(FaultSerializer(StateSerializer.SourcePositionSerializer)))
  private val CompileKeyDataBytesSerializer : Serializer[(Bytes, Bytes)] = PairSerializer(BytesSerializer, BytesSerializer)

  private def updateTheory[A <: Theory](thy : A) : A = {
    theories = theories + (thy.namespace -> thy)
    thy
  }

  def lookupTheory(namespace : Namespace) : Option[Theory] = {
    theories.get(namespace) match {
      case Some(thy) => Some(thy)
      case None =>
        eeAdapter.lookupTheory(namespace) match {
          case None => None
          case Some((source, contentKey, content, optionalTheoryData)) =>
            optionalTheoryData match {
              case None => Some(updateTheory(TheoryImpl(namespace, source, content, contentKey, Vector())))
              case Some(theoryDataBytes) =>
                TheoryDataSerializer.deserialize(Bytes.decode(theoryDataBytes)) match {
                  case Right(faults) =>
                    Some(updateTheory(TheoryImpl(namespace, source, content, contentKey, faults)))  
                  case Left((parents, compileKey)) =>
                    // lookup all the parents of the theory first; this is necessary for 2 reasons:
                    // 1. when loading the state of a theory, we might reference the states of earlier theories,
                    //    and this means that storedBytes must have been primed with the data for those earlier theories.
                    // 2. in order to complete the context with the kernel, its parent contexts must have been completed already
                    for (parent <- parents) {
                      if (!lookupTheory(parent).isDefined) 
                        throw new RuntimeException("cannot load parent theory '" + parent + "' of theory '" + namespace + "'")
                    }
                    val (encodedBytes, storeBytes) = CompileKeyDataBytesSerializer.deserialize(Bytes.decode(eeAdapter.loadCompileKeyData(compileKey)))
                    storedBytes = storedBytes + (namespace -> storeBytes)
                    val (rootingData, optionalCompiledData, faults) = CompileKeyDataSerializer.deserialize(Bytes.decode(encodedBytes))
                    optionalCompiledData match {
                      case None => Some(updateTheory(RootedTheoryImpl(namespace, source, content, contentKey, faults,
                        rootingData._1, rootingData._2, compileKey, rootingData._3)))
                      case Some((parsetree, capturedOutput, state)) =>
                        val thy = CompiledTheoryImpl(namespace, source, content, contentKey, faults, 
                          rootingData._1, rootingData._2, compileKey, rootingData._3, parsetree.asInstanceOf[ParseTree.Block],
                          state, capturedOutput)
                        kernel.completeNamespace(thy.state.context)
                        Some(updateTheory(thy))
                    }
                }
            }
        }
    }
  }

  private def saveCompileKeyData(thy : Theory) {
    thy match {
      case thy : RootedTheory =>
        store.setCurrentNamespace(thy.namespace)
        val rootingData = (thy.parents, thy.aliases, thy.proofscriptVersion)
        val compiledData = 
          thy match {
            case thy: CompiledTheory =>
              Some((thy.parseTree, thy.capturedOutput, thy.state))
            case _ => None
          }
        val compileKeyData : CompileKeyData = (rootingData, compiledData, thy.faults)
        val encoding = Bytes.encode(CompileKeyDataSerializer.serialize(compileKeyData))
        val storeBytes = store.toBytes(thy.namespace).get
        val bytes = Bytes.encode(CompileKeyDataBytesSerializer.serialize((encoding, storeBytes)))
        eeAdapter.storeCompileKeyData(thy.compileKey, bytes)
      case _ => throw new RuntimeException("there is no compile key data to save for non-rooted theory '" + thy.namespace + "'")
    }
  }

  private def saveTheoryData(thy : Theory) {
    thy match {
      case t : RootedTheory =>
        val data : TheoryData = Left((t.parents, t.compileKey))
        eeAdapter.storeTheoryData(thy.namespace, Bytes.encode(TheoryDataSerializer.serialize(data)))
      case t : Theory =>
        val data : TheoryData = Right(t.faults)
        eeAdapter.storeTheoryData(thy.namespace, Bytes.encode(TheoryDataSerializer.serialize(data)))
    }
  }

  def addFaults(namespace : Namespace, faults : Vector[Fault]) : Theory = {
    lookupTheory(namespace) match {
      case Some(t : CompiledTheory) => 
        val thy = updateTheory(CompiledTheoryImpl(t.namespace, t.source, t.content, t.contentKey, t.faults ++ faults, 
          t.parents, t.aliases, t.compileKey, t.proofscriptVersion, t.parseTree, t.state, t.capturedOutput))
        saveCompileKeyData(thy)
        thy
      case Some(t : RootedTheory) => 
        val thy = updateTheory(RootedTheoryImpl(t.namespace, t.source, t.content, t.contentKey, t.faults ++ faults, 
          t.parents, t.aliases, t.compileKey, t.proofscriptVersion))
        saveCompileKeyData(thy)
        thy
      case Some(t : Theory) => 
        val thy = updateTheory(TheoryImpl(t.namespace, t.source, t.content, t.contentKey, t.faults ++ faults)) 
        saveTheoryData(thy)
        thy
      case _ =>
        throw new RuntimeException("cannot add faults to theory '" + namespace + "'")
    }
  }

  def finishedRooting(namespace : Namespace, parents : Set[Namespace], aliases : Aliases, proofscriptVersion : Option[String]) : RootedTheory = {
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
        val compileKey = Bytes.encode((t.contentKey, parentCompileKeys)).sha256
        val thy = updateTheory(RootedTheoryImpl(t.namespace, t.source, t.content, t.contentKey, t.faults, 
          parents, aliases, compileKey, version.get))
        saveCompileKeyData(thy)
        saveTheoryData(thy)
        thy
      case _ => throw new RuntimeException("cannot finish rooting of theory '" + namespace + "'")
    }
  }

  def finishedCompiling(namespace : Namespace, parseTree : ParseTree.Block, state : State, capturedOutput : Output.Captured) : CompiledTheory = {
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
          t.parents, t.aliases, t.compileKey, t.proofscriptVersion, parseTree, state, capturedOutput))
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
    parents : Set[Namespace], aliases : Aliases, compileKey : Bytes, proofscriptVersion : String, 
    parseTree : ParseTree.Block, state : State, capturedOutput : Output.Captured) extends CompiledTheory

}