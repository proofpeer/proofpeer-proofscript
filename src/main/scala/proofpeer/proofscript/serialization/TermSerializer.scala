package proofpeer.proofscript.serialization

import proofpeer.proofscript.logic._
import proofpeer.general._

class CustomizableTermSerializer(store : Store, 
  IndexedNameSerializer : CompoundSerializer[IndexedName], 
  NameSerializer : CompoundSerializer[Name]) 
extends CompoundSerializer[Term] 
{

  import Term._

  val TypeSerializer = new CustomizableTypeSerializer(store)

  private object TermSerializer extends UniquelyIdentifiableSerializer(store, TermSerializerBase)

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

    def decomposeAndSerialize(obj : Term) : (Int, Vector[Any]) = {
      obj match {
        case t : PolyConst =>
          (Kind.POLYCONST, Serializers.POLYCONST.serialize(PolyConst.unapply(t).get))
        case Const(x) =>
          (Kind.CONST, Serializers.CONST.serialize(x))
        case t : Comb =>
          (Kind.COMB, Serializers.COMB.serialize(Comb.unapply(t).get))
        case t : Abs =>
          (Kind.ABS, Serializers.ABS.serialize(Abs.unapply(t).get))
        case Var(x) =>
          (Kind.VAR, Serializers.VAR.serialize(x))
        case _ => throw new RuntimeException("TermSerializerBase: cannot serialize " + obj)
      }
    }

    def deserializeAndCompose(kind : Int, args : Vector[Any]) : Term = {
      kind match {
        case Kind.POLYCONST => 
          PolyConst.tupled(Serializers.POLYCONST.deserialize(args))
        case Kind.CONST => 
          Const(Serializers.CONST.deserialize(args))
        case Kind.COMB => 
          Comb.tupled(Serializers.COMB.deserialize(args))
        case Kind.ABS => 
          Abs.tupled(Serializers.ABS.deserialize(args))
        case Kind.VAR => 
          Var(Serializers.VAR.deserialize(args))
        case _ => throw new RuntimeException("TermSerializerBase: cannot deserialize " + (kind, args))
      }
    }

  }

  def serialize(tm : Term) : Vector[Any] = TermSerializerBase.serialize(tm)

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

