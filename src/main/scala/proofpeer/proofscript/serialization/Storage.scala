package proofpeer.proofscript.serialization

import proofpeer.proofscript.logic._

class Storage(kernel : Kernel) {

  val store = new InMemoryFlatStore(true)
  
  val serializers = kernel.serializers(store)
  
  def storeContext(context : Context) {
    serializers.ContextSerializer.serialize(context)
  }

}
