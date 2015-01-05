package proofpeer.proofscript.serialization

import proofpeer.general._
import proofpeer.proofscript.logic._

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

object BasicIndexedNameSerializer extends CompoundSerializer[IndexedName] {

  private val serializer = PairSerializer(StringSerializer, OptionSerializer(BigIntSerializer))

  def serialize(indexedName : IndexedName) : Vector[Any] = {
    serializer.serialize(indexedName.name, indexedName.index)
  }

  def deserialize(b : Any) : IndexedName = {
    IndexedName.tupled(serializer.deserialize(b))
  }

}


