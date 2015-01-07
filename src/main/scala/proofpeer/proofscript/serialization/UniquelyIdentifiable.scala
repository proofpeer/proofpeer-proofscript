package proofpeer.proofscript.serialization

import proofpeer.general._

object UniquelyIdentifiableStore {
  type Id = Any
  type Item = Any
}

trait UniquelyIdentifiable {
  var optionalUniqueIdentifier : Option[UniquelyIdentifiableStore.Id] = None
}

trait UniquelyIdentifiableStore {
  
  import UniquelyIdentifiableStore._

  def lookup[T <: AnyRef](id : Id, deserialize : Item => T) : T

  def add(item : Item) : Id

  def addNull() : Id

}

class UniquelyIdentifiableSerializer[T <: UniquelyIdentifiable] (store : UniquelyIdentifiableStore, 
  serializer : Serializer[T], typeCode : Int) extends Serializer[T]
{

  def serialize(t : T) : UniquelyIdentifiableStore.Id = {
    if (t == null) return store.addNull()
    t.optionalUniqueIdentifier match {
      case Some(id) => id
      case None => 
        val serialized = Vector(typeCode, serializer.serialize(t))
        val uniqueIdentifier = store.add(serialized)
        t.optionalUniqueIdentifier = Some(uniqueIdentifier)
        uniqueIdentifier
    }   
  }

  private def decode(item : UniquelyIdentifiableStore.Item) : T = {
    item match {
      case Vector(tCode : Long, serialized) =>
        if (tCode != typeCode) throw new RuntimeException("wrong typeCode " + tCode + " found, expected code is " + typeCode)
        serializer.deserialize(serialized)
      case _ => throw new RuntimeException("Invalid Store.Item: " + item)
    }
  }

  def deserialize(id : Any) : T = {
    store.lookup(id.asInstanceOf[UniquelyIdentifiableStore.Id], decode _)
  }

} 

class StoreItem(val item : UniquelyIdentifiableStore.Item) {
  var deserialized : Any = null
}

/** In memory store implementation which doesn't distinguish by namespace. */
class InMemoryFlatStore(sharing : Boolean) extends UniquelyIdentifiableStore {

  import UniquelyIdentifiableStore._

  private var items : Vector[StoreItem] = Vector()
  private var itemsIndex : Map[Item, Id] = Map()

  def size : Int = items.size

  private def decodeId(id : Id) : Int = {
    id match {
      case i : Int => i
      case l : Long => l.toInt
      case _ => throw new RuntimeException("Cannot decode id: " + id)
    }
  }

  def lookup[T <: AnyRef](id : Id, deserialize : Item => T) : T = {
    if (id == -1) return null.asInstanceOf[T]
    val storeItem = items(decodeId(id))
    if (storeItem.deserialized != null) return storeItem.deserialized.asInstanceOf[T]
    val t = deserialize(storeItem.item)
    storeItem.deserialized = t
    t
  }

  def add(item : Item) : Id = { 
    itemsIndex.get(item) match {
      case Some(id) => id
      case None =>
        items = items :+ new StoreItem(item)
        val id = items.size - 1
        if (sharing) itemsIndex = itemsIndex + (item -> id)
        id
    }
  }

  def addNull() : Id = -1

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
}
