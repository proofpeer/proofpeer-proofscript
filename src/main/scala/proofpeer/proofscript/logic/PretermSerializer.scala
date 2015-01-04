package proofpeer.proofscript.logic

import proofpeer.general._
import proofpeer.proofscript.frontend.{ParseTree, ParseTreeSerializer}
import Pretype._
import Preterm._

object NamespaceSerializer extends Serializer[Namespace, Vector[Any]] {

  private val serializer = PairSerializer(BooleanSerializer, VectorSerializer(StringSerializer))

  def serialize(namespace : Namespace) : Vector[Any] = {
    serializer.serialize((namespace.isAbsolute, namespace.components))
  }

  def deserialize(b : Any) : Namespace = {
    val (isAbsolute, components) = serializer.deserialize(b)
    Namespace(isAbsolute, components)
  }

} 

object PretermSerializer extends SpecializedSerializer[Any, Preterm, Vector[Any]](PretermSerializerBase)
object PretypeSerializer extends SpecializedSerializer[Any, Pretype, Vector[Any]](PretermSerializerBase)
object IndexedNameSerializer extends SpecializedSerializer[Any, IndexedName, Vector[Any]](PretermSerializerBase)
object NameSerializer extends SpecializedSerializer[Any, Name, Vector[Any]](PretermSerializerBase)

object QuotedSerializer extends Serializer[Any, Vector[Any]] {

  private val serializer = new ParseTreeSerializer(null, (_,_) => null)

  def serialize(parsetree : Any) : Vector[Any] = {
    serializer.serialize(parsetree.asInstanceOf[ParseTree])
  }

  def deserialize(b : Any) : Any = {
    serializer.deserialize(b)
  }

}

object PretermSerializerBase extends CaseClassSerializerBase[Any] {

  object Kind {
    val PTYUNIVERSE = 0
    val PTYPROP = 1
    val PTYFUN = -1
    val PTYANY = 2
    val PTYVAR = -2
    val INDEXEDNAME = 3
    val NAME = -3
    val PTMTYPING = 4
    val PTMNAME = -4
    val PTMABS = 5
    val PTMCOMB = -5
    val PTMQUOTE = 6
    val PTMERROR = -6
  }

  object Serializers {
    val PTYFUN = PairSerializer(PretypeSerializer,PretypeSerializer)
    val PTYVAR = BigIntSerializer
    val INDEXEDNAME = PairSerializer(StringSerializer,OptionSerializer(BigIntSerializer))
    val NAME = PairSerializer(OptionSerializer(NamespaceSerializer),IndexedNameSerializer)
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
      case t : IndexedName =>
        (Kind.INDEXEDNAME, Serializers.INDEXEDNAME.serialize(IndexedName.unapply(t).get))
      case t : Name =>
        (Kind.NAME, Serializers.NAME.serialize(Name.unapply(t).get))
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
      case Kind.INDEXEDNAME => 
        IndexedName.tupled(Serializers.INDEXEDNAME.deserialize(args))
      case Kind.NAME => 
        Name.tupled(Serializers.NAME.deserialize(args))
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
    ("IndexedName", "StringSerializer", "OptionSerializer(BigIntSerializer)"),
    ("Name", "OptionSerializer(NamespaceSerializer)", "IndexedNameSerializer"),
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



