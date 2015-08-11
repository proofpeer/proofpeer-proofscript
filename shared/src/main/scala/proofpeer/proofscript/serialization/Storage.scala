package proofpeer.proofscript.serialization

import proofpeer.proofscript.logic._
import proofpeer.proofscript.naiveinterpreter.State
import proofpeer.general._

import UniquelyIdentifiableStore.{Id => StoreId}

/** In memory store implementation. */
class FlatStore(val storename : String, sharing : Boolean, 
  exportId : StoreId => (StoreId, StoreId), // the first one is used as a reference, the second one as a label in uniqueIdentifiers
  importId : StoreId => Either[StoreId, UniquelyIdentifiableStore],
  isCompatible : StoreId => Option[StoreId],
  storedBytes : Option[Bytes]) 
extends UniquelyIdentifiableStore {

  private val (nullId, _) = exportId(-1)

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
        val (_, uniqueIdentifier) = exportId(id)
        result.uniqueIdentifiers = uniqueIdentifier :: result.uniqueIdentifiers
        storeItem.deserialized = result
        result
    }
  }

  private def findUniqueIdentifier(uniqueIdentifiers : Seq[StoreId]) : Option[StoreId] = {
    for (u <- uniqueIdentifiers) {
      isCompatible(u) match {
        case Some(id) => return Some(id)
        case None =>
      }
    }
    None
  }

  def add[T <: UniquelyIdentifiable](t : T, serialize : T => Item) : Id = {
    if (t == null) return nullId
    findUniqueIdentifier(t.uniqueIdentifiers) match {
      case Some(id) => id
      case None =>
        val storeItem = new StoreItem()
        val id = items.size
        items = items :+ storeItem
        var (exportedId, uniqueIdentifier) = exportId(id)
        t.uniqueIdentifiers = uniqueIdentifier :: t.uniqueIdentifiers
        val item = serialize(t)
        if (sharing && id == items.size - 1 && itemsIndex.get(item).isDefined) {
          items = items.dropRight(1)
          val id = itemsIndex(item)
          val (_exportedId, uniqueIdentifier) = exportId(id)
          exportedId = _exportedId
          t.uniqueIdentifiers = uniqueIdentifier :: t.uniqueIdentifiers.tail          
        } else {
          storeItem.item = item
          if (sharing) itemsIndex = itemsIndex + (item -> id)
        }
        exportedId
    }
  }

}

object MultiStore {
  
  import java.util.concurrent.atomic.AtomicLong
  
  private val uniqueStoreId = new AtomicLong(0)

  def obtainNewStoreId() : Long = uniqueStoreId.incrementAndGet()
}

/** Store implementation which maintains separate stores for each namespace. */
class MultiStore(sharing : Boolean, loadNamespace : String => Option[Bytes], ancestors : Namespace => Set[String]) extends UniquelyIdentifiableStore {

  import UniquelyIdentifiableStore._

  private val myStoreId = MultiStore.obtainNewStoreId()

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
        def exportId(x : Any) : (Any, Any) = (Vector(ns, x), Vector(myStoreId, ns, x))
        def importId(id : Any) : Either[Any, UniquelyIdentifiableStore] = {
          id match {
            case Vector(n : String, x) if n == ns => Left(x)
            case Vector(n : String, _) => Right(getStore(n))
            case _ => throw new RuntimeException("Invalid id " + id)
          }
        }
        val a = ancestors(Namespace(ns))
        def isCompatible(id : Any) : Option[Any] = {
          id match {
            case Vector(storeId : Long, n : String, x) =>
              if (storeId == myStoreId && a.contains(n)) 
                Some((Vector(n, x)))
              else None 
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