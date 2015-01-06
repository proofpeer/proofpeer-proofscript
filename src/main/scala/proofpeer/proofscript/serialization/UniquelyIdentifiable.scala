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

  def lookup[T](id : Id, deserialize : Item => T) : T

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

}
