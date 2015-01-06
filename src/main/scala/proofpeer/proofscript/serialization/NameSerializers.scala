package proofpeer.proofscript.serialization

import proofpeer.general._
import proofpeer.proofscript.logic._

object BasicIndexedNameSerializer extends CompoundSerializer[IndexedName] {

  private val serializer = PairSerializer(StringSerializer, OptionSerializer(BigIntSerializer))

  def serialize(indexedName : IndexedName) : Vector[Any] = {
    serializer.serialize(indexedName.name, indexedName.index)
  }

  def deserialize(b : Any) : IndexedName = {
    IndexedName.tupled(serializer.deserialize(b))
  }

}

object BasicNamespaceSerializer extends CompoundSerializer[Namespace] {

  private val serializer = PairSerializer(BooleanSerializer, VectorSerializer(StringSerializer))

  def serialize(namespace : Namespace) : Vector[Any] = {
    serializer.serialize((namespace.isAbsolute, namespace.components))
  }

  def deserialize(b : Any) : Namespace = {
    val n = serializer.deserialize(b)
    Namespace(n._1, n._2)
  }

}

class BasicNameSerializer(IndexedNameSerializer : CompoundSerializer[IndexedName], 
  NamespaceSerializer : CompoundSerializer[Namespace]) extends CompoundSerializer[Name] 
{

  private val serializer = PairSerializer(OptionSerializer(NamespaceSerializer), IndexedNameSerializer)

  def serialize(name : Name) : Vector[Any] = {
    serializer.serialize((name.namespace, name.name))
  }

  def deserialize(b : Any) : Name = {
    Name.tupled(serializer.deserialize(b))
  }

}

class NameSerializers(store : Store) {

  object IndexedNameSerializer extends UniquelyIdentifiableSerializer(store, BasicIndexedNameSerializer)

  object NamespaceSerializer extends UniquelyIdentifiableSerializer(store, BasicNamespaceSerializer)

  object NameSerializer extends UniquelyIdentifiableSerializer(store, 
    new BasicNameSerializer(IndexedNameSerializer, NamespaceSerializer))

}
