package proofpeer.proofscript.serialization

import proofpeer.proofscript.logic._
import proofpeer.general._
import proofpeer.proofscript.frontend.{ParseTree, SourcePosition}
import Pretype._
import Preterm._
import proofpeer.indent.Span

final class CustomizablePretermSerializer(
  SourcePositionSerializer : Serializer[SourcePosition], 
  IndexedNameSerializer : Serializer[IndexedName],
  NamespaceSerializer : Serializer[Namespace],
  NameSerializer : Serializer[Name],
  TermSerializer : Serializer[Term],
  TypeSerializer : Serializer[Type],
  ParseTreeSerializer : Serializer[ParseTree]) 
extends NestedSerializer[Preterm]
{

  val PretermSerializer = this

  object QuotedSerializer extends TypecastSerializer[Any, ParseTree](ParseTreeSerializer)

  object PretypeSerializer extends CaseClassSerializerBase[Pretype] {

    object Kind {
      val PTYUNIVERSE = 0
      val PTYPROP = 1
      val PTYFUN = -1
      val PTYANY = 2
      val PTYVAR = -2
      val PTYQUOTE = 3
    }

    object Serializers {
      val PTYFUN = PairSerializer(PretypeSerializer,PretypeSerializer)
      val PTYVAR = BigIntSerializer
      val PTYQUOTE = QuotedSerializer
    }

    def decomposeAndSerialize(obj : Pretype) : (Int, Option[Any]) = {
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
        case PTyQuote(x) =>
          (Kind.PTYQUOTE, Some(Serializers.PTYQUOTE.serialize(x)))
        case _ => throw new RuntimeException("PretypeSerializer: cannot serialize " + obj)
      }
    }

    def deserializeAndCompose(kind : Int, args : Option[Any]) : Pretype = {
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
        case Kind.PTYQUOTE if args.isDefined => 
          PTyQuote(Serializers.PTYQUOTE.deserialize(args.get))
        case _ => throw new RuntimeException("PretypeSerializer: cannot deserialize " + (kind, args))
      }
    }

  }

  object PretermSerializerBase extends CaseClassSerializerBase[Preterm] {

    object Kind {
      val PTMTYPING = 0
      val PTMNAME = 1
      val PTMABS = -1
      val PTMCOMB = 2
      val PTMQUOTE = -2
      val PTMTERM = 3
      val PTMERROR = -3
    }

    object Serializers {
      val PTMTYPING = PairSerializer(PretermSerializer,PretypeSerializer)
      val PTMNAME = PairSerializer(NameSerializer,PretypeSerializer)
      val PTMABS = QuadrupleSerializer(IndexedNameSerializer,PretypeSerializer,PretermSerializer,PretypeSerializer)
      val PTMCOMB = QuadrupleSerializer(PretermSerializer,PretermSerializer,OptionSerializer(BooleanSerializer),PretypeSerializer)
      val PTMQUOTE = PairSerializer(QuotedSerializer,PretypeSerializer)
      val PTMTERM = PairSerializer(TermSerializer,TypeSerializer)
      val PTMERROR = StringSerializer
    }

    def decomposeAndSerialize(obj : Preterm) : (Int, Option[Any]) = {
      obj match {
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
        case t : PTmTerm =>
          (Kind.PTMTERM, Some(Serializers.PTMTERM.serialize(PTmTerm.unapply(t).get)))
        case PTmError(x) =>
          (Kind.PTMERROR, Some(Serializers.PTMERROR.serialize(x)))
        case _ => throw new RuntimeException("PretermSerializerBase: cannot serialize " + obj)
      }
    }

    def deserializeAndCompose(kind : Int, args : Option[Any]) : Preterm = {
      kind match {
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
        case Kind.PTMTERM if args.isDefined => 
          PTmTerm.tupled(Serializers.PTMTERM.deserialize(args.get))
        case Kind.PTMERROR if args.isDefined => 
          PTmError(Serializers.PTMERROR.deserialize(args.get))
        case _ => throw new RuntimeException("PretermSerializerBase: cannot deserialize " + (kind, args))
      }
    }

  }
  protected lazy val innerSerializer : Serializer[Preterm] = PretermSerializerBase

}

/** This is code used to create most of the above code. It is not needed during runtime, just during programming. */
object PretermSerializerGenerator {

  val typeCases : Vector[Any] = Vector(
    "PTyUniverse",
    "PTyProp",
    ("PTyFun", "PretypeSerializer", "PretypeSerializer"),
    "PTyAny",
    ("PTyVar", "BigIntSerializer"),
    ("PTyQuote", "QuotedSerializer")
  )

  val termCases : Vector[Any] = Vector(
    ("PTmTyping", "PretermSerializer", "PretypeSerializer"),
    ("PTmName", "NameSerializer", "PretypeSerializer"),
    ("PTmAbs", "IndexedNameSerializer", "PretypeSerializer", "PretermSerializer", "PretypeSerializer"),
    ("PTmComb", "PretermSerializer", "PretermSerializer", "OptionSerializer(BooleanSerializer)", "PretypeSerializer"),
    ("PTmQuote", "QuotedSerializer", "PretypeSerializer"),
    ("PTmTerm", "TermSerializer", "TypeSerializer"),
    ("PTmError", "StringSerializer")
  )

  /** Rename _main to main to generate the code. */
  def _main(args : Array[String]) {
    val typeTool = new CaseClassSerializerTool("PretypeSerializer", typeCases, "Pretype")
    //typeTool.output()
    val termTool = new CaseClassSerializerTool("PretermSerializerBase", termCases, "Preterm")
    termTool.output()
  }

}



