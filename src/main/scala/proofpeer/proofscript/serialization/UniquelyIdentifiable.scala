package proofpeer.proofscript.serialization

import proofpeer.general._

object Store {
  type Id = Vector[Any]
  type Item = Any
}

trait UniquelyIdentifiable {
  var optionalUniqueIdentifier : Option[Store.Id] = None
}

trait Store {
  
  import Store._

  def lookup[T](id : Id, deserialize : Item => T) : T

  def add(item : Item) : Id

}

class UniquelyIdentifiableSerializer[T <: UniquelyIdentifiable] (store : Store, 
  serializer : Serializer[T], typeCode : Int) extends Serializer[T]
{

  def serialize(t : T) : Store.Id = {
    t.optionalUniqueIdentifier match {
      case Some(id) => id
      case None => 
        val serialized = Vector(typeCode, serializer.serialize(t))
        val uniqueIdentifier = store.add(serialized)
        t.optionalUniqueIdentifier = Some(uniqueIdentifier)
        uniqueIdentifier
    }   
  }

  private def decode(item : Store.Item) : T = {
    item match {
      case Vector(tCode : Long, serialized) =>
        if (tCode != typeCode) throw new RuntimeException("wrong typeCode " + tCode + " found, expected code is " + typeCode)
        serializer.deserialize(serialized)
      case _ => throw new RuntimeException("Invalid Store.Item: " + item)
    }
  }

  def deserialize(id : Any) : T = {
    store.lookup(id.asInstanceOf[Store.Id], decode _)
  }

} 

object UISTypeCodes {

  val INDEXEDNAME = 1
  val NAMESPACE = 2
  val NAME = 3
  val TYPE = 4
  val TERM = 5

}
