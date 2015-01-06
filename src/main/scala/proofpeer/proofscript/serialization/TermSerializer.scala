package proofpeer.proofscript.serialization

import proofpeer.proofscript.logic._
import proofpeer.general._

class CustomizableTermSerializer(store : UniquelyIdentifiableStore, 
  IndexedNameSerializer : Serializer[IndexedName], 
  NameSerializer : Serializer[Name]) 
extends Serializer[Term] 
{

  import Term._

  val TypeSerializer = new CustomizableTypeSerializer(store)

  private object TermSerializer extends UniquelyIdentifiableSerializer(store, TermSerializerBase, UISTypeCodes.TERM)

  private object TermSerializerBase extends CaseClassSerializerBase[Term] {

    object Kind {
      val POLYCONST = 0
      val CONST = 1
      val COMB = -1
      val ABS = 2
      val VAR = -2
    }

    object Serializers {
      val POLYCONST = PairSerializer(NameSerializer,TypeSerializer)
      val CONST = NameSerializer
      val COMB = PairSerializer(TermSerializer,TermSerializer)
      val ABS = TripleSerializer(IndexedNameSerializer,TypeSerializer,TermSerializer)
      val VAR = IndexedNameSerializer
    }

    def decomposeAndSerialize(obj : Term) : (Int, Option[Any]) = {
      obj match {
        case t : PolyConst =>
          (Kind.POLYCONST, Some(Serializers.POLYCONST.serialize(PolyConst.unapply(t).get)))
        case Const(x) =>
          (Kind.CONST, Some(Serializers.CONST.serialize(x)))
        case t : Comb =>
          (Kind.COMB, Some(Serializers.COMB.serialize(Comb.unapply(t).get)))
        case t : Abs =>
          (Kind.ABS, Some(Serializers.ABS.serialize(Abs.unapply(t).get)))
        case Var(x) =>
          (Kind.VAR, Some(Serializers.VAR.serialize(x)))
        case _ => throw new RuntimeException("TermSerializerBase: cannot serialize " + obj)
      }
    }

    def deserializeAndCompose(kind : Int, args : Option[Any]) : Term = {
      kind match {
        case Kind.POLYCONST if args.isDefined => 
          PolyConst.tupled(Serializers.POLYCONST.deserialize(args.get))
        case Kind.CONST if args.isDefined => 
          Const(Serializers.CONST.deserialize(args.get))
        case Kind.COMB if args.isDefined => 
          Comb.tupled(Serializers.COMB.deserialize(args.get))
        case Kind.ABS if args.isDefined => 
          Abs.tupled(Serializers.ABS.deserialize(args.get))
        case Kind.VAR if args.isDefined => 
          Var(Serializers.VAR.deserialize(args.get))
        case _ => throw new RuntimeException("TermSerializerBase: cannot deserialize " + (kind, args))
      }
    }

  }

  def serialize(tm : Term) = TermSerializerBase.serialize(tm)

  def deserialize(b : Any) : Term = TermSerializerBase.deserialize(b)

}

object TermSerializerGenerator {

  val cases = Vector(
    ("PolyConst", "NameSerializer", "TypeSerializer"),
    ("Const", "NameSerializer"),
    ("Comb", "TermSerializer", "TermSerializer"),
    ("Abs", "IndexedNameSerializer", "TypeSerializer", "TermSerializer"),
    ("Var", "IndexedNameSerializer")
  )

  def _main(args : Array[String]) {
    val tool = new CaseClassSerializerTool("TermSerializerBase", cases, "Term")
    tool.output()
  }

} 

