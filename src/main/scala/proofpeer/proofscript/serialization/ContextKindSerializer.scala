package proofpeer.proofscript.serialization

import proofpeer.general._
import proofpeer.proofscript.logic._

class BasicContextKindSerializer(TermSerializer : Serializer[Term], TypeSerializer : Serializer[Type],
  NamespaceSerializer : Serializer[Namespace], NameSerializer : Serializer[Name]) extends NestedSerializer[ContextKind]
{

  import ContextKind._ 

  private object ContextKindSerializerBase extends CaseClassSerializerBase[ContextKind] {

    object Kind {
      val ASSUME = 0
      val DEFINE = 1
      val CHOOSE = -1
      val INTRODUCE = 2
      val CREATED = -2
      val COMPLETE = 3
    }

    object Serializers {
      val ASSUME = TermSerializer
      val DEFINE = TripleSerializer(NameSerializer,TypeSerializer,TermSerializer)
      val CHOOSE = TripleSerializer(NameSerializer,TypeSerializer,TermSerializer)
      val INTRODUCE = PairSerializer(NameSerializer,TypeSerializer)
      val CREATED = TripleSerializer(NamespaceSerializer,SetSerializer(NamespaceSerializer),SetSerializer(NamespaceSerializer))
    }

    def decomposeAndSerialize(obj : ContextKind) : (Int, Option[Any]) = {
      obj match {
        case Assume(x) =>
          (Kind.ASSUME, Some(Serializers.ASSUME.serialize(x)))
        case t : Define =>
          (Kind.DEFINE, Some(Serializers.DEFINE.serialize(Define.unapply(t).get)))
        case t : Choose =>
          (Kind.CHOOSE, Some(Serializers.CHOOSE.serialize(Choose.unapply(t).get)))
        case t : Introduce =>
          (Kind.INTRODUCE, Some(Serializers.INTRODUCE.serialize(Introduce.unapply(t).get)))
        case t : Created =>
          (Kind.CREATED, Some(Serializers.CREATED.serialize(Created.unapply(t).get)))
        case Complete =>
          (Kind.COMPLETE, None)
        case _ => throw new RuntimeException("ContextKindSerializerBase: cannot serialize " + obj)
      }
    }

    def deserializeAndCompose(kind : Int, args : Option[Any]) : ContextKind = {
      kind match {
        case Kind.ASSUME if args.isDefined => 
          Assume(Serializers.ASSUME.deserialize(args.get))
        case Kind.DEFINE if args.isDefined => 
          Define.tupled(Serializers.DEFINE.deserialize(args.get))
        case Kind.CHOOSE if args.isDefined => 
          Choose.tupled(Serializers.CHOOSE.deserialize(args.get))
        case Kind.INTRODUCE if args.isDefined => 
          Introduce.tupled(Serializers.INTRODUCE.deserialize(args.get))
        case Kind.CREATED if args.isDefined => 
          Created.tupled(Serializers.CREATED.deserialize(args.get))
        case Kind.COMPLETE if args.isEmpty => 
          Complete
        case _ => throw new RuntimeException("ContextKindSerializerBase: cannot deserialize " + (kind, args))
      }
    }

  }

  protected val innerSerializer : Serializer[ContextKind] = ContextKindSerializerBase

}

class CustomizableContextKindSerializer(store : UniquelyIdentifiableStore, TermSerializer : Serializer[Term], 
  TypeSerializer : Serializer[Type], NamespaceSerializer : Serializer[Namespace], NameSerializer : Serializer[Name]) 
extends UniquelyIdentifiableSerializer(store, new BasicContextKindSerializer(TermSerializer, TypeSerializer, 
  NamespaceSerializer, NameSerializer), UISTypeCodes.CONTEXTKIND)

object ContextKindSerializerGenerator {

  val cases = Vector(
    ("Assume", "TermSerializer"),
    ("Define", "NameSerializer", "TypeSerializer", "TermSerializer"),
    ("Choose", "NameSerializer", "TypeSerializer", "TermSerializer"),
    ("Introduce", "NameSerializer", "TypeSerializer"),
    ("Created", "NamespaceSerializer", "SetSerializer(NamespaceSerializer)", "SetSerializer(NamespaceSerializer)"),
    "Complete"
  )

  def _main(args : Array[String]) {
    val tool = new CaseClassSerializerTool("ContextKindSerializerBase", cases, "ContextKind")
    tool.output()
  }

}
