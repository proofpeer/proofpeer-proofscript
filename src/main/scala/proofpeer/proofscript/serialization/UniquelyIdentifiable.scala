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
  serializer : Serializer[T, _]) extends CompoundSerializer[T]
{

  def serialize(t : T) : Store.Id = {
    t.optionalUniqueIdentifier match {
      case Some(id) => id
      case None => 
        val serialized = serializer.serialize(t)
        val uniqueIdentifier = store.add(serialized)
        t.optionalUniqueIdentifier = Some(uniqueIdentifier)
        uniqueIdentifier
    }   
  }

  def deserialize(id : Any) : T = {
    store.lookup(id.asInstanceOf[Store.Id], item => serializer.deserialize(item))
  }


} 
