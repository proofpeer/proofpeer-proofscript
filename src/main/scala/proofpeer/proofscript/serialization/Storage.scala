package proofpeer.proofscript.serialization

import proofpeer.proofscript.logic._
import proofpeer.proofscript.naiveinterpreter.State
import proofpeer.general._

import UniquelyIdentifiableStore.{Id => StoreId}

/** In memory store implementation. */
class FlatStore(val storename : String, sharing : Boolean, 
  exportId : StoreId => StoreId, 
  importId : StoreId => Either[StoreId, UniquelyIdentifiableStore],
  isCompatible : StoreId => Boolean,
  storedBytes : Option[Bytes]) 
extends UniquelyIdentifiableStore {

  private val nullId = exportId(-1)
  final val firstId = exportId(0)

  import UniquelyIdentifiableStore._

  private var items : Vector[StoreItem] = Vector()
  private var itemsIndex : Map[Item, Id] = Map()

  def toBytes : Bytes = {
    val data = items.map(_.item)
    Bytes.encode(data)
  }

  private def mkStoreItem(item : UniquelyIdentifiableStore.Item) : StoreItem = {
    val si = new StoreItem()
    si.item = item
    si
  }

  private def fromBytes(bytes : Bytes) {
    val data = Bytes.decode(bytes, 0)._1.asInstanceOf[Vector[UniquelyIdentifiableStore.Item]]
    items = data.map(mkStoreItem _)
    itemsIndex = Map() // not needed for deserialization
  }

  if (storedBytes.isDefined) fromBytes(storedBytes.get)

  def size : Int = items.size

  private def decodeId(id : Id) : Int = {
    id match {
      case i : Int => i
      case l : Long => l.toInt
      case _ => throw new RuntimeException("Cannot decode id: " + id)
    }
  }

  def lookup[T <: UniquelyIdentifiable](exportedId : Id, create : Item => T, deserialize : Item => T, assign : (T, T) => T) : T = {
    importId(exportedId) match {
      case Right(otherStore) => otherStore.lookup(exportedId, create, deserialize, assign)
      case Left(id) =>
        if (id == -1) return null.asInstanceOf[T]
        val storeItem = items(decodeId(id))
        if (storeItem.deserialized != null) return storeItem.deserialized.asInstanceOf[T]
        val fresh_t = create(storeItem.item)
        storeItem.deserialized = fresh_t
        val t = deserialize(storeItem.item)
        val result = assign(fresh_t, t)
        result.uniqueIdentifiers = exportedId :: result.uniqueIdentifiers
        storeItem.deserialized = result
        result
    }
  }

  def add[T <: UniquelyIdentifiable](t : T, serialize : T => Item) : Id = {
    if (t == null) return nullId
    t.uniqueIdentifiers.find(isCompatible) match {
      case Some(id) => id
      case None =>
        val storeItem = new StoreItem()
        val id = items.size
        items = items :+ storeItem
        var exportedId = exportId(id)
        t.uniqueIdentifiers = exportedId :: t.uniqueIdentifiers
        val item = serialize(t)
        if (sharing && id == items.size - 1 && itemsIndex.get(item).isDefined) {
          items = items.dropRight(1)
          val id = itemsIndex(item)
          exportedId = exportId(id)
          t.uniqueIdentifiers = exportedId :: t.uniqueIdentifiers.tail          
        } else {
          storeItem.item = item
          if (sharing) itemsIndex = itemsIndex + (item -> id)
        }
        exportedId
    }
  }

}


/** Store implementation which maintains separate stores for each namespace. */
class MultiStore(sharing : Boolean, loadNamespace : String => Option[Bytes], ancestors : Namespace => Set[String]) extends UniquelyIdentifiableStore {

  import UniquelyIdentifiableStore._

  private var stores : Map[String, FlatStore] = Map()
  private var currentStore : FlatStore = null

  def allStores : Map[String, FlatStore] = stores

  def size : Int = {
    var s = 0
    for ((m, store) <- stores)
      s += store.size
    s
  }

  private def getStore(namespace : String) : FlatStore = {
    stores.get(namespace) match {
      case Some(store) => store
      case None =>
        val ns = namespace.toString.toLowerCase
        def exportId(x : Any) : Any = Vector(ns, x)
        def importId(id : Any) : Either[Any, UniquelyIdentifiableStore] = {
          id match {
            case Vector(n : String, x) if n == ns => Left(x)
            case Vector(n : String, _) => Right(getStore(n))
            case _ => throw new RuntimeException("Invalid id " + id)
          }
        }
        val a = ancestors(Namespace(ns))
        def isCompatible(id : Any) : Boolean = {
          id match {
            case Vector(n : String, x) => a.contains(n)
            case _ => throw new RuntimeException("Invalid id " + id)
          }
        }
        val store = new FlatStore(namespace, sharing, exportId _, importId _, isCompatible _, loadNamespace(namespace))
        stores = stores + (namespace -> store)
        store
    }
  }

  /** Selects the namespace to which items are added. */
  def setCurrentNamespace(namespace : Namespace) {
    currentStore = getStore(namespace.toString.toLowerCase)
  }

  def toBytes(namespace : Namespace) : Option[Bytes] = {
    stores.get(namespace.toString.toLowerCase) match {
      case Some(store) => Some(store.toBytes)
      case None => None
    }
  }

  def firstIdOf(namespace : Namespace) : Id = {
    getStore(namespace.toString.toLowerCase).firstId
  }

  def add[T <: UniquelyIdentifiable](t : T, serialize : T => Item) : Id = {
    currentStore.add[T](t, serialize)
  }

  def lookup[T <: UniquelyIdentifiable](id : Id, create : Item => T, deserialize : Item => T, assign : (T, T) => T) : T = {
    id match {
      case Vector(n : String, _) => getStore(n).lookup[T](id, create, deserialize, assign)
      case _ => throw new RuntimeException("Invalid id for lookup: " + id)
    }
  }

}