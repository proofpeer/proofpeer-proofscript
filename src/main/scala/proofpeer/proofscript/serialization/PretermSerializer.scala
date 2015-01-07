package proofpeer.proofscript.serialization

import proofpeer.proofscript.logic._
import proofpeer.general._
import proofpeer.proofscript.frontend.{ParseTree, SourcePosition}
import Pretype._
import Preterm._
import proofpeer.indent.Span

class CustomizablePretermSerializer(
  SourcePositionSerializer : Serializer[SourcePosition], 
  IndexedNameSerializer : Serializer[IndexedName],
  NamespaceSerializer : Serializer[Namespace],
  NameSerializer : Serializer[Name],
  ParseTreeSerializer : Serializer[ParseTree]) 
extends Serializer[Preterm]
{

  val PretermSerializer = this 

  object PretypeSerializer extends DummySerializer[Pretype]

  object QuotedSerializer extends TypecastSerializer[Any, ParseTree](ParseTreeSerializer)

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

    def decomposeAndSerialize(obj : Any) : (Int, Option[Any]) = {
      obj match {
        case PTyUniverse =>
          (Kind.PTYUNIVERSE, None)
        case PTyProp =>
          (Kind.PTYPROP, None)
        case t : PTyFun =>
          (Kind.PTYFUN, Some(Serializers.PTYFUN.serialize(PTyFun.unapply(t).get)))
        case PTyAny =>
          (Kind.PTYANY, None)
        case PTyVar(x) =>
          (Kind.PTYVAR, Some(Serializers.PTYVAR.serialize(x)))
        case t : PTmTyping =>
          (Kind.PTMTYPING, Some(Serializers.PTMTYPING.serialize(PTmTyping.unapply(t).get)))
        case t : PTmName =>
          (Kind.PTMNAME, Some(Serializers.PTMNAME.serialize(PTmName.unapply(t).get)))
        case t : PTmAbs =>
          (Kind.PTMABS, Some(Serializers.PTMABS.serialize(PTmAbs.unapply(t).get)))
        case t : PTmComb =>
          (Kind.PTMCOMB, Some(Serializers.PTMCOMB.serialize(PTmComb.unapply(t).get)))
        case t : PTmQuote =>
          (Kind.PTMQUOTE, Some(Serializers.PTMQUOTE.serialize(PTmQuote.unapply(t).get)))
        case PTmError(x) =>
          (Kind.PTMERROR, Some(Serializers.PTMERROR.serialize(x)))
        case _ => throw new RuntimeException("PretermSerializerBase: cannot serialize " + obj)
      }
    }

    def deserializeAndCompose(kind : Int, args : Option[Any]) : Any = {
      kind match {
        case Kind.PTYUNIVERSE if args.isEmpty => 
          PTyUniverse
        case Kind.PTYPROP if args.isEmpty => 
          PTyProp
        case Kind.PTYFUN if args.isDefined => 
          PTyFun.tupled(Serializers.PTYFUN.deserialize(args.get))
        case Kind.PTYANY if args.isEmpty => 
          PTyAny
        case Kind.PTYVAR if args.isDefined => 
          PTyVar(Serializers.PTYVAR.deserialize(args.get))
        case Kind.PTMTYPING if args.isDefined => 
          PTmTyping.tupled(Serializers.PTMTYPING.deserialize(args.get))
        case Kind.PTMNAME if args.isDefined => 
          PTmName.tupled(Serializers.PTMNAME.deserialize(args.get))
        case Kind.PTMABS if args.isDefined => 
          PTmAbs.tupled(Serializers.PTMABS.deserialize(args.get))
        case Kind.PTMCOMB if args.isDefined => 
          PTmComb.tupled(Serializers.PTMCOMB.deserialize(args.get))
        case Kind.PTMQUOTE if args.isDefined => 
          PTmQuote.tupled(Serializers.PTMQUOTE.deserialize(args.get))
        case Kind.PTMERROR if args.isDefined => 
          PTmError(Serializers.PTMERROR.deserialize(args.get))
        case _ => throw new RuntimeException("PretermSerializerBase: cannot deserialize " + (kind, args))
      }
    }

  }  

  def serialize(x : Preterm) = PretermSerializerBase.serialize(x)

  def deserialize(b : Any) : Preterm = PretermSerializerBase.deserialize(b).asInstanceOf[Preterm]

}

/** This is code used to create most of the above code. It is not needed during runtime, just during programming. */
object PretermSerializerGenerator {

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



