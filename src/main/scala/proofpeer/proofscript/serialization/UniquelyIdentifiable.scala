package proofpeer.proofscript.serialization

import proofpeer.general._

object UniquelyIdentifiableStore {
  type Id = Any
  type Item = Any
}

trait UniquelyIdentifiable extends AnyRef {
  var optionalUniqueIdentifier : Option[UniquelyIdentifiableStore.Id] = None
}

trait CyclicSerializer[T] extends Serializer[T] {

  def create(b : Any) : T

  def assign(dest : T, src : T) : T

}

trait UniquelyIdentifiableStore {
  
  import UniquelyIdentifiableStore._

  def lookup[T <: UniquelyIdentifiable](id : Id, create : Item => T, deserialize : Item => T, assign : (T, T) => T) : T

  def acyclicLookup[T <: UniquelyIdentifiable](id : Id, deserialize : Item => T) : T = 
    lookup(id, _ => null.asInstanceOf[T], deserialize, (dest : T, src : T) => src)

  def add[T <: UniquelyIdentifiable](t : T, serialize : T => Item) : Id

}

class UniquelyIdentifiableSerializer[T <: UniquelyIdentifiable] (store : UniquelyIdentifiableStore, 
  serializer : Serializer[T], typeCode : Int) extends Serializer[T]
{

  private def encode(t : T) : UniquelyIdentifiableStore.Item = Vector(typeCode, serializer.serialize(t))

  private def decompose(item : UniquelyIdentifiableStore.Item) : Any = {
    item match {
      case Vector(tCode, serialized) =>
        if (tCode != typeCode) throw new RuntimeException("wrong typeCode " + tCode + " found, expected code is " + typeCode)
        serialized
      case _ => throw new RuntimeException("Invalid Store.Item: " + item)
    }
  }

  private def decode(item : UniquelyIdentifiableStore.Item) : T = 
    serializer.deserialize(decompose(item))
  
  private def create(item : UniquelyIdentifiableStore.Item) : T = 
    serializer.asInstanceOf[CyclicSerializer[T]].create(decompose(item))

  private def assign(dest : T, src : T) : T = 
    serializer.asInstanceOf[CyclicSerializer[T]].assign(dest, src)

  def serialize(t : T) : UniquelyIdentifiableStore.Id = {
    store.add(t, encode _)
  }

  def deserialize(id : Any) : T = {
    if (serializer.isInstanceOf[CyclicSerializer[_]]) {
      store.lookup[T](id.asInstanceOf[UniquelyIdentifiableStore.Id], create _, decode _, assign _)
    } else
      store.acyclicLookup[T](id.asInstanceOf[UniquelyIdentifiableStore.Id], decode _)
  }

} 

final class StoreItem {
  var item : UniquelyIdentifiableStore.Item = null
  var deserialized : Any = null
}

object UISTypeCodes {
  val INDEXEDNAME = 1
  val NAMESPACE = 2
  val NAME = 3
  val TYPE = 4
  val TERM = 5
  val ALIAS = 6
  val ALIASES = 7
  val SOURCE = 8
  val CONTEXTKIND = 9
  val CONTEXT = 10
  val THEOREM = 11
  val STATEVALUE = 12
  val ENV = 13
  val STATE = 14
}
