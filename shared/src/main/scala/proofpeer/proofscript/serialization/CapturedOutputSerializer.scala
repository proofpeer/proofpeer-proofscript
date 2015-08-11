package proofpeer.proofscript.serialization

import proofpeer.general._
import proofpeer.proofscript.naiveinterpreter._
import proofpeer.proofscript.logic.Namespace

object OutputKindSerializer extends TransformSerializer[OutputKind, Int](IntSerializer,
  (kind : OutputKind) => 
    kind match {
      case OutputKind.SHOW => 0
      case OutputKind.FAILURE => 1
      case OutputKind.TIMEIT => 2
    },
  (kind : Int) =>
    kind match {
      case 0 => OutputKind.SHOW
      case 1 => OutputKind.FAILURE
      case 2 => OutputKind.TIMEIT
    })

object CapturedOutputSerializer {

  def apply(namespaceSerializer : Serializer[Namespace]) : Serializer[Output.Captured] =
    VectorSerializer(
      QuadrupleSerializer(
        namespaceSerializer, 
        OptionSerializer(SpanSerializer), 
        OutputKindSerializer, 
        StringSerializer))  

}




