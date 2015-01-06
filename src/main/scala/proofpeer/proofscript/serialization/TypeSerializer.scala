package proofpeer.proofscript.serialization

import proofpeer.proofscript.logic._
import proofpeer.general._

class CustomizableTypeSerializer(store : Store) extends CompoundSerializer[Type] {

  import Type._

  private object TypeSerializer extends UniquelyIdentifiableSerializer(store, TypeSerializerBase)

  private object TypeSerializerBase extends CaseClassSerializerBase[Type] {

    object Kind {
      val UNIVERSE = 0
      val PROP = 1
      val FUN = -1
    }

    object Serializers {
      val FUN = PairSerializer(TypeSerializer,TypeSerializer)
    }

    def decomposeAndSerialize(obj : Type) : (Int, Vector[Any]) = {
      obj match {
        case Universe =>
          (Kind.UNIVERSE, Vector())
        case Prop =>
          (Kind.PROP, Vector())
        case t : Fun =>
          (Kind.FUN, Serializers.FUN.serialize(Fun.unapply(t).get))
        case _ => throw new RuntimeException("TypeSerializerBase: cannot serialize " + obj)
      }
    }

    def deserializeAndCompose(kind : Int, args : Vector[Any]) : Type = {
      kind match {
        case Kind.UNIVERSE if args.size == 0 => 
          Universe
        case Kind.PROP if args.size == 0 => 
          Prop
        case Kind.FUN => 
          Fun.tupled(Serializers.FUN.deserialize(args))
        case _ => throw new RuntimeException("TypeSerializerBase: cannot deserialize " + (kind, args))
      }
    }

  }

  def serialize(ty : Type) : Vector[Any] = TypeSerializerBase.serialize(ty)

  def deserialize(b : Any) : Type = TypeSerializerBase.deserialize(b)

}

object TypeSerializerGenerator {

  val cases = Vector(
    "Universe",
    "Prop",
    ("Fun", "TypeSerializer", "TypeSerializer") 
  )

  def _main(args : Array[String]) {
    val tool = new CaseClassSerializerTool("TypeSerializerBase", cases, "Type")
    tool.output()
  }

} 

