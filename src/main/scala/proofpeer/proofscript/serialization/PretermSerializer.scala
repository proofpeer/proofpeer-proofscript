package proofpeer.proofscript.serialization

import proofpeer.proofscript.logic._
import proofpeer.general._
import proofpeer.proofscript.frontend.{ParseTree, SourcePosition}
import Pretype._
import Preterm._
import proofpeer.indent.Span

class CustomizablePretermSerializer(
  SourcePositionSerializer : CompoundSerializer[SourcePosition], 
  IndexedNameSerializer : CompoundSerializer[IndexedName],
  NamespaceSerializer : CompoundSerializer[Namespace],
  NameSerializer : CompoundSerializer[Name],
  ParseTreeSerializer : CompoundSerializer[ParseTree]) 
extends CompoundSerializer[Preterm]
{

  val PretermSerializer = this 

  object PretypeSerializer extends DummySerializer[Pretype, Vector[Any]]

  object QuotedSerializer extends TypecastSerializer[ParseTree, Any, Vector[Any]](ParseTreeSerializer)

  object PretermSerializerBase extends CaseClassSerializerBase[Any] {

    object Kind {
      val PTYUNIVERSE = 0
      val PTYPROP = 1
      val PTYFUN = -1
      val PTYANY = 2
      val PTYVAR = -2
      val PTMTYPING = 3
      val PTMNAME = -3
      val PTMABS = 4
      val PTMCOMB = -4
      val PTMQUOTE = 5
      val PTMERROR = -5
    }

    object Serializers {
      val PTYFUN = PairSerializer(PretypeSerializer,PretypeSerializer)
      val PTYVAR = BigIntSerializer
      val PTMTYPING = PairSerializer(PretermSerializer,PretypeSerializer)
      val PTMNAME = PairSerializer(NameSerializer,PretypeSerializer)
      val PTMABS = QuadrupleSerializer(IndexedNameSerializer,PretypeSerializer,PretermSerializer,PretypeSerializer)
      val PTMCOMB = QuadrupleSerializer(PretermSerializer,PretermSerializer,OptionSerializer(BooleanSerializer),PretypeSerializer)
      val PTMQUOTE = PairSerializer(QuotedSerializer,PretypeSerializer)
      val PTMERROR = StringSerializer
    }

    def decomposeAndSerialize(obj : Any) : (Int, Vector[Any]) = {
      obj match {
        case PTyUniverse =>
          (Kind.PTYUNIVERSE, Vector())
        case PTyProp =>
          (Kind.PTYPROP, Vector())
        case t : PTyFun =>
          (Kind.PTYFUN, Serializers.PTYFUN.serialize(PTyFun.unapply(t).get))
        case PTyAny =>
          (Kind.PTYANY, Vector())
        case PTyVar(x) =>
          (Kind.PTYVAR, Vector(Serializers.PTYVAR.serialize(x)))
        case t : PTmTyping =>
          (Kind.PTMTYPING, Serializers.PTMTYPING.serialize(PTmTyping.unapply(t).get))
        case t : PTmName =>
          (Kind.PTMNAME, Serializers.PTMNAME.serialize(PTmName.unapply(t).get))
        case t : PTmAbs =>
          (Kind.PTMABS, Serializers.PTMABS.serialize(PTmAbs.unapply(t).get))
        case t : PTmComb =>
          (Kind.PTMCOMB, Serializers.PTMCOMB.serialize(PTmComb.unapply(t).get))
        case t : PTmQuote =>
          (Kind.PTMQUOTE, Serializers.PTMQUOTE.serialize(PTmQuote.unapply(t).get))
        case PTmError(x) =>
          (Kind.PTMERROR, Vector(Serializers.PTMERROR.serialize(x)))
        case _ => throw new RuntimeException("PretermSerializerBase: cannot serialize " + obj)
      }
    }

    def deserializeAndCompose(kind : Int, args : Vector[Any]) : Any = {
      kind match {
        case Kind.PTYUNIVERSE if args.size == 0 => 
          PTyUniverse
        case Kind.PTYPROP if args.size == 0 => 
          PTyProp
        case Kind.PTYFUN => 
          PTyFun.tupled(Serializers.PTYFUN.deserialize(args))
        case Kind.PTYANY if args.size == 0 => 
          PTyAny
        case Kind.PTYVAR if args.size == 1 => 
          PTyVar(Serializers.PTYVAR.deserialize(args(0)))
        case Kind.PTMTYPING => 
          PTmTyping.tupled(Serializers.PTMTYPING.deserialize(args))
        case Kind.PTMNAME => 
          PTmName.tupled(Serializers.PTMNAME.deserialize(args))
        case Kind.PTMABS => 
          PTmAbs.tupled(Serializers.PTMABS.deserialize(args))
        case Kind.PTMCOMB => 
          PTmComb.tupled(Serializers.PTMCOMB.deserialize(args))
        case Kind.PTMQUOTE => 
          PTmQuote.tupled(Serializers.PTMQUOTE.deserialize(args))
        case Kind.PTMERROR if args.size == 1 => 
          PTmError(Serializers.PTMERROR.deserialize(args(0)))
        case _ => throw new RuntimeException("PretermSerializerBase: cannot deserialize " + (kind, args))
      }
    }

  }

  def serialize(x : Preterm) : Vector[Any] = PretermSerializerBase.serialize(x)

  def deserialize(b : Any) : Preterm = PretermSerializerBase.deserialize(b).asInstanceOf[Preterm]

}

/** This is code used to create most of the above code. It is not needed during runtime, just during programming. */
object PretermSerializerGenerator {

  val typeCases : Vector[Any] = Vector(
    "PTyUniverse",
    "PTyProp",
    ("PTyFun", "PretypeSerializer", "PretypeSerializer"),
    "PTyAny",
    ("PTyVar", "BigIntSerializer")
  )

  val cases : Vector[Any] = Vector(
    "PTyUniverse",
    "PTyProp",
    ("PTyFun", "PretypeSerializer", "PretypeSerializer"),
    "PTyAny",
    ("PTyVar", "BigIntSerializer"),
    ("PTmTyping", "PretermSerializer", "PretypeSerializer"),
    ("PTmName", "NameSerializer", "PretypeSerializer"),
    ("PTmAbs", "IndexedNameSerializer", "PretypeSerializer", "PretermSerializer", "PretypeSerializer"),
    ("PTmComb", "PretermSerializer", "PretermSerializer", "OptionSerializer(BooleanSerializer)", "PretypeSerializer"),
    ("PTmQuote", "QuotedSerializer", "PretypeSerializer"),
    ("PTmError", "StringSerializer")
  )

  /** Rename _main to main to generate the code. */
  def _main(args : Array[String]) {
    val tool = new CaseClassSerializerTool("PretermSerializerBase", cases)
    tool.output()
  }

}



