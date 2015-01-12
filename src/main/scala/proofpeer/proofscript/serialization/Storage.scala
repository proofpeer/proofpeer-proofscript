package proofpeer.proofscript.serialization

import proofpeer.proofscript.logic._
import proofpeer.proofscript.naiveinterpreter.State
import proofpeer.general._

class Storage(kernel : Kernel) {

  val theStore = new MultiStore(true)
  
  val kernelSerializers = kernel.serializers(theStore)

  val stateSerializer = new CustomizableStateSerializer(theStore, kernelSerializers)
  
  def store(namespace : Namespace, state : State) : Any = {
    theStore.setCurrentNamespace(namespace)
    stateSerializer.serialize(state)
  }

  def restore(storedStateId : Any) : State = {
    stateSerializer.deserialize(storedStateId).asInstanceOf[State]
  }

  def printStats() {
    println("number of items in store: " + theStore.size)
    println("number of namespaces in store: " + theStore.allStores.size)
    var size = 0
    for ((namespace, flatstore) <- theStore.allStores) {
      val b = flatstore.toBytes
      size = size + b.length
      println(namespace + " has " + b.length + " bytes")
    }
    println("total size in bytes: " + size)

  }

}

import UniquelyIdentifiableStore.{Id => StoreId}

/** In memory store implementation. */
class FlatStore(sharing : Boolean, 
  exportId : StoreId => StoreId, 
  importId : StoreId => Either[StoreId, UniquelyIdentifiableStore]) 
extends UniquelyIdentifiableStore {

  private val nullId = exportId(-1)

  import UniquelyIdentifiableStore._

  private var items : Vector[StoreItem] = Vector()
  private var itemsIndex : Map[Item, Id] = Map()

  def toBytes : Bytes = {
    val data = items.map(_.item)
    var symbols : Map[String, Bytes] = Map()
    def intern(x : Any) : Any = {
      x match {
        case s : String => 
          symbols.get(s) match {
            case Some(id) => id
            case None =>
              val index = symbols.size
              val id = Bytes.encode(index)
              symbols = symbols + (s -> id)
              id
          }
        case v : Vector[_] => v.map(intern _)
        case _ => x
      }
    }
    var symbolTable : Array[String] = new Array(symbols.size)
    for ((s, id) <- symbols) {
      val index = Bytes.decode(id, 0).asInstanceOf[Long].toInt
      symbolTable(index) = s
    }
    val internedData = intern(data)
    val output = Vector(symbolTable.toVector, internedData)
    Bytes.encode(output)
  }

  def size : Int = items.size

  private def decodeId(id : Id) : Int = {
    id match {
      case i : Int => i
      case l : Long => l.toInt
      case _ => throw new RuntimeException("Cannot decode id: " + id)
    }
  }

  def lookup[T <: UniquelyIdentifiable](id : Id, create : Item => T, deserialize : Item => T, assign : (T, T) => T) : T = {
    importId(id) match {
      case Right(otherStore) => otherStore.lookup(id, create, deserialize, assign)
      case Left(id) =>
        if (id == -1) return null.asInstanceOf[T]
        val storeItem = items(decodeId(id))
        if (storeItem.deserialized != null) return storeItem.deserialized.asInstanceOf[T]
        val fresh_t = create(storeItem.item)
        storeItem.deserialized = fresh_t
        val t = deserialize(storeItem.item)
        val result = assign(fresh_t, t)
        storeItem.deserialized = result
        result
    }
  }

  def add[T <: UniquelyIdentifiable](t : T, serialize : T => Item) : Id = {
    if (t == null) return nullId
    t.optionalUniqueIdentifier match {
      case Some(id) => id
      case None =>
        val storeItem = new StoreItem()
        val id = items.size
        items = items :+ storeItem
        t.optionalUniqueIdentifier = Some(exportId(id))
        val item = serialize(t)
        if (sharing && id == items.size - 1 && itemsIndex.get(item).isDefined) {
          items = items.dropRight(1)
          val id = itemsIndex(item)
          t.optionalUniqueIdentifier = Some(exportId(id))
        } else {
          storeItem.item = item
          if (sharing) itemsIndex = itemsIndex + (item -> id)
        }
        t.optionalUniqueIdentifier.get
    }
  }

}


/** Store implementation which maintains separate stores for each namespace. */
class MultiStore(sharing : Boolean) extends UniquelyIdentifiableStore {

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
        val store = new FlatStore(sharing, exportId _, importId _)
        stores = stores + (namespace -> store)
        store
    }
  }

  /** Selects the namespace to which items are added. */
  def setCurrentNamespace(namespace : Namespace) {
    currentStore = getStore(namespace.toString.toLowerCase)
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