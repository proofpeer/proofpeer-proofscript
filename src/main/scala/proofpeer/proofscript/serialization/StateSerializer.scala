package proofpeer.proofscript.serialization

import proofpeer.general._
import proofpeer.proofscript.logic.KernelSerializers
import proofpeer.proofscript.frontend.ParseTree
import proofpeer.proofscript.naiveinterpreter._

class CustomizableCollectSerializer(StateValueSerializer : Serializer[StateValue]) extends Serializer[Collect] {

  import Collect._

  val CollectorSerializer = new CollectorSerializer(StateValueSerializer)

  private object CollectSerializerBase extends CaseClassSerializerBase[Collect] {

    object Kind {
      val ZERO = 0
      val ONE = 1
      val MULTIPLE = -1
    }

    object Serializers {
      val ONE = OptionSerializer(StateValueSerializer)
      val MULTIPLE = CollectorSerializer
    }

    def decomposeAndSerialize(obj : Collect) : (Int, Option[Any]) = {
      obj match {
        case Zero =>
          (Kind.ZERO, None)
        case One(x) =>
          (Kind.ONE, Some(Serializers.ONE.serialize(x)))
        case Multiple(x) =>
          (Kind.MULTIPLE, Some(Serializers.MULTIPLE.serialize(x)))
        case _ => throw new RuntimeException("CollectSerializerBase: cannot serialize " + obj)
      }
    }

    def deserializeAndCompose(kind : Int, args : Option[Any]) : Collect = {
      kind match {
        case Kind.ZERO if args.isEmpty => 
          Zero
        case Kind.ONE if args.isDefined => 
          One(Serializers.ONE.deserialize(args.get))
        case Kind.MULTIPLE if args.isDefined => 
          Multiple(Serializers.MULTIPLE.deserialize(args.get))
        case _ => throw new RuntimeException("CollectSerializerBase: cannot deserialize " + (kind, args))
      }
    }
  }

  def serialize(x : Collect) = CollectSerializerBase.serialize(x)

  def deserialize(b : Any) : Collect = CollectSerializerBase.deserialize(b)

}

object NativeFunctionSerializer extends TransformSerializer[NativeFunctions.F, String](StringSerializer,
  (f : NativeFunctions.F) => f.name, (name : String) => NativeFunctions.environment(name))

class BasicStateValueSerializer(StateValueSerializer : Serializer[StateValue], StateSerializer : Serializer[State],
  kernelSerializers : KernelSerializers, ParseTreeSerializer : Serializer[ParseTree])
{

  private val ContextSerializer = kernelSerializers.ContextSerializer
  private val TheoremSerializer = kernelSerializers.TheoremSerializer
  private val TermSerializer = kernelSerializers.TermSerializer
  private object PTFunSerializer extends TypecastSerializer[ParseTree.Fun, ParseTree](ParseTreeSerializer)
  private object PTDefCaseSerializer extends TypecastSerializer[ParseTree.DefCase, ParseTree](ParseTreeSerializer)

  private object StateValueSerializerBase extends CaseClassSerializerBase[StateValue] {

    object Kind {
      val NILVALUE = 0
      val CONTEXTVALUE = 1
      val THEOREMVALUE = -1
      val TERMVALUE = 2
      val BOOLVALUE = -2
      val INTVALUE = 3
      val SIMPLEFUNCTIONVALUE = -3
      val RECURSIVEFUNCTIONVALUE = 4
      val NATIVEFUNCTIONVALUE = -4
      val STRINGVALUE = 5
      val TUPLEVALUE = -5
    }

    object Serializers {
      val CONTEXTVALUE = ContextSerializer
      val THEOREMVALUE = TheoremSerializer
      val TERMVALUE = TermSerializer
      val BOOLVALUE = BooleanSerializer
      val INTVALUE = BigIntSerializer
      val SIMPLEFUNCTIONVALUE = PairSerializer(StateSerializer,PTFunSerializer)
      val RECURSIVEFUNCTIONVALUE = PairSerializer(StateSerializer,VectorSerializer(PTDefCaseSerializer))
      val NATIVEFUNCTIONVALUE = NativeFunctionSerializer
      val STRINGVALUE = VectorSerializer(IntSerializer)
      val TUPLEVALUE = VectorSerializer(StateValueSerializer)
    }

    def decomposeAndSerialize(obj : StateValue) : (Int, Option[Any]) = {
      obj match {
        case NilValue =>
          (Kind.NILVALUE, None)
        case ContextValue(x) =>
          (Kind.CONTEXTVALUE, Some(Serializers.CONTEXTVALUE.serialize(x)))
        case TheoremValue(x) =>
          (Kind.THEOREMVALUE, Some(Serializers.THEOREMVALUE.serialize(x)))
        case TermValue(x) =>
          (Kind.TERMVALUE, Some(Serializers.TERMVALUE.serialize(x)))
        case BoolValue(x) =>
          (Kind.BOOLVALUE, Some(Serializers.BOOLVALUE.serialize(x)))
        case IntValue(x) =>
          (Kind.INTVALUE, Some(Serializers.INTVALUE.serialize(x)))
        case t : SimpleFunctionValue =>
          (Kind.SIMPLEFUNCTIONVALUE, Some(Serializers.SIMPLEFUNCTIONVALUE.serialize(SimpleFunctionValue.unapply(t).get)))
        case t : RecursiveFunctionValue =>
          (Kind.RECURSIVEFUNCTIONVALUE, Some(Serializers.RECURSIVEFUNCTIONVALUE.serialize(RecursiveFunctionValue.unapply(t).get)))
        case NativeFunctionValue(x) =>
          (Kind.NATIVEFUNCTIONVALUE, Some(Serializers.NATIVEFUNCTIONVALUE.serialize(x)))
        case StringValue(x) =>
          (Kind.STRINGVALUE, Some(Serializers.STRINGVALUE.serialize(x)))
        case TupleValue(x) =>
          (Kind.TUPLEVALUE, Some(Serializers.TUPLEVALUE.serialize(x)))
        case _ => throw new RuntimeException("StateValueSerializerBase: cannot serialize " + obj)
      }
    }

    def deserializeAndCompose(kind : Int, args : Option[Any]) : StateValue = {
      kind match {
        case Kind.NILVALUE if args.isEmpty => 
          NilValue
        case Kind.CONTEXTVALUE if args.isDefined => 
          ContextValue(Serializers.CONTEXTVALUE.deserialize(args.get))
        case Kind.THEOREMVALUE if args.isDefined => 
          TheoremValue(Serializers.THEOREMVALUE.deserialize(args.get))
        case Kind.TERMVALUE if args.isDefined => 
          TermValue(Serializers.TERMVALUE.deserialize(args.get))
        case Kind.BOOLVALUE if args.isDefined => 
          BoolValue(Serializers.BOOLVALUE.deserialize(args.get))
        case Kind.INTVALUE if args.isDefined => 
          IntValue(Serializers.INTVALUE.deserialize(args.get))
        case Kind.SIMPLEFUNCTIONVALUE if args.isDefined => 
          SimpleFunctionValue.tupled(Serializers.SIMPLEFUNCTIONVALUE.deserialize(args.get))
        case Kind.RECURSIVEFUNCTIONVALUE if args.isDefined => 
          RecursiveFunctionValue.tupled(Serializers.RECURSIVEFUNCTIONVALUE.deserialize(args.get))
        case Kind.NATIVEFUNCTIONVALUE if args.isDefined => 
          NativeFunctionValue(Serializers.NATIVEFUNCTIONVALUE.deserialize(args.get))
        case Kind.STRINGVALUE if args.isDefined => 
          StringValue(Serializers.STRINGVALUE.deserialize(args.get))
        case Kind.TUPLEVALUE if args.isDefined => 
          TupleValue(Serializers.TUPLEVALUE.deserialize(args.get))
        case _ => throw new RuntimeException("StateValueSerializerBase: cannot deserialize " + (kind, args))
      }
    }
  }

}

object StateSerializerGenerator {

  val collectCases = Vector("Zero", ("One", "OptionSerializer(StateValueSerializer)"), ("Multiple", "CollectorSerializer"))

  val stateValueCases = Vector(
    "NilValue",
    ("ContextValue", "ContextSerializer"),
    ("TheoremValue", "TheoremSerializer"),
    ("TermValue", "TermSerializer"),
    ("BoolValue", "BooleanSerializer"),
    ("IntValue", "BigIntSerializer"),
    ("SimpleFunctionValue", "StateSerializer", "PTFunSerializer"),
    ("RecursiveFunctionValue", "StateSerializer", "VectorSerializer(PTDefCaseSerializer)"),
    ("NativeFunctionValue", "NativeFunctionSerializer"),
    ("StringValue", "VectorSerializer(IntSerializer)"),
    ("TupleValue", "VectorSerializer(StateValueSerializer)")
  )

  def main(args : Array[String]) {
    val collectTool = new CaseClassSerializerTool("CollectSerializerBase", collectCases, "Collect")
    // collectTool.output()
    val stateValueTool = new CaseClassSerializerTool("StateValueSerializerBase", stateValueCases, "StateValue")
    stateValueTool.output()
  }

}