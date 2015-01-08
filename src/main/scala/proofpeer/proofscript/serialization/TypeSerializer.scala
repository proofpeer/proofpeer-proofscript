package proofpeer.proofscript.serialization

import proofpeer.proofscript.logic._
import proofpeer.general._

final class CustomizableTypeSerializer(store : UniquelyIdentifiableStore) extends NestedSerializer[Type] {

  import Type._

  private object TypeSerializer extends UniquelyIdentifiableSerializer(store, TypeSerializerBase, UISTypeCodes.TYPE)

  private object TypeSerializerBase extends CaseClassSerializerBase[Type] {

    object Kind {
      val UNIVERSE = 0
      val PROP = 1
      val FUN = -1
    }

    object Serializers {
      val FUN = PairSerializer(TypeSerializer,TypeSerializer)
    }

    def decomposeAndSerialize(obj : Type) : (Int, Option[Any]) = {
      obj match {
        case Universe =>
          (Kind.UNIVERSE, None)
        case Prop =>
          (Kind.PROP, None)
        case t : Fun =>
          (Kind.FUN, Some(Serializers.FUN.serialize(Fun.unapply(t).get)))
        case _ => throw new RuntimeException("TypeSerializerBase: cannot serialize " + obj)
      }
    }

    def deserializeAndCompose(kind : Int, args : Option[Any]) : Type = {
      kind match {
        case Kind.UNIVERSE if args.isEmpty => 
          Universe
        case Kind.PROP if args.isEmpty => 
          Prop
        case Kind.FUN if args.isDefined => 
          Fun.tupled(Serializers.FUN.deserialize(args.get))
        case _ => throw new RuntimeException("TypeSerializerBase: cannot deserialize " + (kind, args))
      }
    }

  }

  protected val innerSerializer : Serializer[Type] = TypeSerializerBase

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

