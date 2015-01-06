package proofpeer.proofscript.serialization

import proofpeer.general._
import proofpeer.proofscript.logic._

object BasicIndexedNameSerializer extends TransformSerializer(PairSerializer(StringSerializer, OptionSerializer(BigIntSerializer)),
  (indexedName : IndexedName) => (indexedName.name, indexedName.index), IndexedName.tupled)

object BasicNamespaceSerializer extends TransformSerializer(PairSerializer(BooleanSerializer, VectorSerializer(StringSerializer)),
  (namespace : Namespace) => (namespace.isAbsolute, namespace.components), 
  (n : (Boolean, Vector[String])) => Namespace(n._1, n._2))

class BasicNameSerializer(NamespaceSerializer : Serializer[Namespace], IndexedNameSerializer : Serializer[IndexedName]) 
extends TransformSerializer(PairSerializer(OptionSerializer(NamespaceSerializer), IndexedNameSerializer),
  (name : Name) => (name.namespace, name.name), Name.tupled)

class BasicAliasSerializer(NamespaceSerializer : Serializer[Namespace]) extends TransformSerializer(
  PairSerializer(StringSerializer, NamespaceSerializer), (alias : Alias) => (alias.alias, alias.namespace), Alias.tupled)
  
class BasicAliasesSerializer(NamespaceSerializer : Serializer[Namespace], AliasSerializer : Serializer[Alias]) extends TransformSerializer(
  PairSerializer(NamespaceSerializer, ListSerializer(AliasSerializer)),
  (aliases : Aliases) => (aliases.base, aliases.aliases), (x : (Namespace, List[Alias])) => new Aliases(x._1, x._2))

class NameSerializers(store : UniquelyIdentifiableStore) {

  object IndexedNameSerializer extends UniquelyIdentifiableSerializer(store, BasicIndexedNameSerializer, UISTypeCodes.INDEXEDNAME)

  object NamespaceSerializer extends UniquelyIdentifiableSerializer(store, BasicNamespaceSerializer, UISTypeCodes.NAMESPACE)

  object NameSerializer extends UniquelyIdentifiableSerializer(store, 
    new BasicNameSerializer(NamespaceSerializer, IndexedNameSerializer), UISTypeCodes.NAME)

  object AliasSerializer extends UniquelyIdentifiableSerializer(store, new BasicAliasSerializer(NamespaceSerializer), UISTypeCodes.ALIAS)

  object AliasesSerializer extends UniquelyIdentifiableSerializer(store, 
    new BasicAliasesSerializer(NamespaceSerializer, AliasSerializer), UISTypeCodes.ALIASES)

}
