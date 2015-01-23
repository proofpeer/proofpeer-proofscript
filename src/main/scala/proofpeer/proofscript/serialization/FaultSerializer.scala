package proofpeer.proofscript.serialization

import proofpeer.general._
import proofpeer.proofscript.naiveinterpreter._
import proofpeer.proofscript.frontend._
import proofpeer.proofscript.logic.Namespace

object SourceLabelSerializer extends CaseClassSerializerBase[SourceLabel] {

  object Kind {
    val NOSOURCELABEL = 0
    val ANONYMOUSFUNCTIONLABEL = 1
    val DEFFUNCTIONLABEL = -1
  }

  object Serializers {
    val ANONYMOUSFUNCTIONLABEL = StringSerializer
    val DEFFUNCTIONLABEL = PairSerializer(StringSerializer,StringSerializer)
  }

  def decomposeAndSerialize(obj : SourceLabel) : (Int, Option[Any]) = {
    obj match {
      case NoSourceLabel =>
        (Kind.NOSOURCELABEL, None)
      case AnonymousFunctionLabel(x) =>
        (Kind.ANONYMOUSFUNCTIONLABEL, Some(Serializers.ANONYMOUSFUNCTIONLABEL.serialize(x)))
      case t : DefFunctionLabel =>
        (Kind.DEFFUNCTIONLABEL, Some(Serializers.DEFFUNCTIONLABEL.serialize(DefFunctionLabel.unapply(t).get)))
      case _ => throw new RuntimeException("SourceLabelSerializer: cannot serialize " + obj)
    }
  }

  def deserializeAndCompose(kind : Int, args : Option[Any]) : SourceLabel = {
    kind match {
      case Kind.NOSOURCELABEL if args.isEmpty => 
        NoSourceLabel
      case Kind.ANONYMOUSFUNCTIONLABEL if args.isDefined => 
        AnonymousFunctionLabel(Serializers.ANONYMOUSFUNCTIONLABEL.deserialize(args.get))
      case Kind.DEFFUNCTIONLABEL if args.isDefined => 
        DefFunctionLabel.tupled(Serializers.DEFFUNCTIONLABEL.deserialize(args.get))
      case _ => throw new RuntimeException("SourceLabelSerializer: cannot deserialize " + (kind, args))
    }
  }

}

object FaultSerializer { 

  import ExecutionEnvironment.Fault

  private type Triple = (SourcePosition, String, Vector[(SourcePosition, SourceLabel)])

  private val SourcePositionSerializer : Serializer[SourcePosition] =
    new BasicSourcePositionSerializer(BasicSourceSerializer)

  private val serializer : Serializer[Fault] =
    new TransformSerializer[Fault, Triple](
      TripleSerializer(SourcePositionSerializer, StringSerializer, VectorSerializer(PairSerializer(SourcePositionSerializer, SourceLabelSerializer))),
      (fault : Fault) => (fault.pos, fault.description, fault.trace),
      (triple : Triple) => Fault(triple._1, triple._2, triple._3))

  def apply(SourcePositionSerializer : Serializer[SourcePosition] = SourcePositionSerializer) : Serializer[Fault] = 
    new TransformSerializer[Fault, Triple](
      TripleSerializer(SourcePositionSerializer, StringSerializer, VectorSerializer(PairSerializer(SourcePositionSerializer, SourceLabelSerializer))),
      (fault : Fault) => (fault.pos, fault.description, fault.trace),
      (triple : Triple) => Fault(triple._1, triple._2, triple._3))
    
}

object SourceLabelSerializerGenerator {

  val cases = Vector(
    "NoSourceLabel",
    ("AnonymousFunctionLabel", "StringSerializer"),
    ("DefFunctionLabel", "StringSerializer", "StringSerializer")
  )

  def _main(args : Array[String]) {
    val tool = new CaseClassSerializerTool("SourceLabelSerializer", cases, "SourceLabel")
    tool.output()
  }

} 