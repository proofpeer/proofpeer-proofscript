package proofpeer.proofscript.serialization

import proofpeer.proofscript.logic._
import proofpeer.proofscript.naiveinterpreter.State

class Storage(kernel : Kernel) {

  val store = new InMemoryFlatStore(true)
  
  val kernelSerializers = kernel.serializers(store)
  val stateSerializer = new CustomizableStateSerializer(store, kernelSerializers)
  
  def store(namespace : Namespace, state : State) {
    stateSerializer.serialize(state)
  }

}
