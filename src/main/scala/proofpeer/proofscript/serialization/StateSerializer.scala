package proofpeer.proofscript.serialization

import proofpeer.general._
import proofpeer.proofscript.logic.{Context, Namespace, KernelSerializers}
import proofpeer.proofscript.frontend.{SourcePosition, ParseTree}
import proofpeer.proofscript.naiveinterpreter._

final class CustomizableCollectSerializer(StateValueSerializer : Serializer[StateValue]) extends NestedSerializer[Collect] {

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

  protected val innerSerializer : Serializer[Collect] = CollectSerializerBase

}

object NativeFunctionSerializer extends TransformSerializer[NativeFunctions.F, String](StringSerializer, _.name, 
  NativeFunctions.environment(_))

final class BasicCustomTypeSerializer(NamespaceSerializer : Serializer[Namespace]) 
  extends TransformSerializer[CustomType, (Namespace, String)](
    PairSerializer(NamespaceSerializer, StringSerializer),
    ct => (ct.namespace, ct.name), CustomType.tupled)

final class CustomizableCustomTypeSerializer(store : UniquelyIdentifiableStore,
  NamespaceSerializer : Serializer[Namespace]) extends UniquelyIdentifiableSerializer[CustomType](store, 
    new BasicCustomTypeSerializer(NamespaceSerializer), UISTypeCodes.CUSTOMTYPE)

final class BasicStateValueSerializer(StateValueSerializer : Serializer[StateValue], CustomTypeSerializer : Serializer[CustomType],
  StateSerializer : Serializer[State], kernelSerializers : KernelSerializers, ParseTreeSerializer : Serializer[ParseTree]) 
extends NestedSerializer[StateValue] with CyclicSerializer[StateValue]
{

  private val ContextSerializer = kernelSerializers.ContextSerializer
  private val TheoremSerializer = kernelSerializers.TheoremSerializer
  private val TermSerializer = kernelSerializers.TermSerializer
  private val CTermSerializer = kernelSerializers.CTermSerializer  
  private val TypeSerializer = kernelSerializers.TypeSerializer
  private object PTFunSerializer extends TypecastSerializer[ParseTree.Fun, ParseTree](ParseTreeSerializer)
  private object PTDefCaseSerializer extends TypecastSerializer[ParseTree.DefCase, ParseTree](ParseTreeSerializer)
  private object PTPatternSerializer extends TypecastSerializer[ParseTree.Pattern, ParseTree](ParseTreeSerializer)

  object StateValueSerializerBase extends CaseClassSerializerBase[StateValue] {

    object Kind {
      val NILVALUE = 0
      val CONTEXTVALUE = 1
      val THEOREMVALUE = -1
      val TERMVALUE = 2
      val TYPEVALUE = -2
      val BOOLVALUE = 3
      val INTVALUE = -3
      val SIMPLEFUNCTIONVALUE = 4
      val RECURSIVEFUNCTIONVALUE = -4
      val NATIVEFUNCTIONVALUE = 5
      val STRINGVALUE = -5
      val TUPLEVALUE = 6
      val SETVALUE = -6
      val MAPVALUE = 7
      val CONSTRVALUE = -7
      val CONSTRAPPLIEDVALUE = 8
      val CONSTRUNAPPLIEDVALUE = -8
    }

    object Serializers {
      val CONTEXTVALUE = ContextSerializer
      val THEOREMVALUE = TheoremSerializer
      val TERMVALUE = CTermSerializer
      val TYPEVALUE = TypeSerializer
      val BOOLVALUE = BooleanSerializer
      val INTVALUE = BigIntSerializer
      val SIMPLEFUNCTIONVALUE = PairSerializer(StateSerializer,PTFunSerializer)
      val RECURSIVEFUNCTIONVALUE = QuadrupleSerializer(StateSerializer,VectorSerializer(PTDefCaseSerializer),NullableSerializer(MapSerializer(StateValueSerializer, StateValueSerializer)),OptionSerializer(ContextSerializer))
      val NATIVEFUNCTIONVALUE = NativeFunctionSerializer
      val STRINGVALUE = VectorSerializer(IntSerializer)
      val TUPLEVALUE = PairSerializer(VectorSerializer(StateValueSerializer),BooleanSerializer)
      val SETVALUE = SetSerializer(StateValueSerializer)
      val MAPVALUE = PairSerializer(MapSerializer(StateValueSerializer, StateValueSerializer),BooleanSerializer)
      val CONSTRVALUE = PairSerializer(StringSerializer,CustomTypeSerializer)
      val CONSTRAPPLIEDVALUE = QuadrupleSerializer(StringSerializer,StateValueSerializer,CustomTypeSerializer,BooleanSerializer)
      val CONSTRUNAPPLIEDVALUE = QuadrupleSerializer(StateSerializer,StringSerializer,PTPatternSerializer,CustomTypeSerializer)
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
        case TypeValue(x) =>
          (Kind.TYPEVALUE, Some(Serializers.TYPEVALUE.serialize(x)))
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
        case t : TupleValue =>
          (Kind.TUPLEVALUE, Some(Serializers.TUPLEVALUE.serialize(TupleValue.unapply(t).get)))
        case SetValue(x) =>
          (Kind.SETVALUE, Some(Serializers.SETVALUE.serialize(x)))
        case t : MapValue =>
          (Kind.MAPVALUE, Some(Serializers.MAPVALUE.serialize(MapValue.unapply(t).get)))
        case t : ConstrValue =>
          (Kind.CONSTRVALUE, Some(Serializers.CONSTRVALUE.serialize(ConstrValue.unapply(t).get)))
        case t : ConstrAppliedValue =>
          (Kind.CONSTRAPPLIEDVALUE, Some(Serializers.CONSTRAPPLIEDVALUE.serialize(ConstrAppliedValue.unapply(t).get)))
        case t : ConstrUnappliedValue =>
          (Kind.CONSTRUNAPPLIEDVALUE, Some(Serializers.CONSTRUNAPPLIEDVALUE.serialize(ConstrUnappliedValue.unapply(t).get)))
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
        case Kind.TYPEVALUE if args.isDefined => 
          TypeValue(Serializers.TYPEVALUE.deserialize(args.get))
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
          TupleValue.tupled(Serializers.TUPLEVALUE.deserialize(args.get))
        case Kind.SETVALUE if args.isDefined => 
          SetValue(Serializers.SETVALUE.deserialize(args.get))
        case Kind.MAPVALUE if args.isDefined => 
          MapValue.tupled(Serializers.MAPVALUE.deserialize(args.get))
        case Kind.CONSTRVALUE if args.isDefined => 
          ConstrValue.tupled(Serializers.CONSTRVALUE.deserialize(args.get))
        case Kind.CONSTRAPPLIEDVALUE if args.isDefined => 
          ConstrAppliedValue.tupled(Serializers.CONSTRAPPLIEDVALUE.deserialize(args.get))
        case Kind.CONSTRUNAPPLIEDVALUE if args.isDefined => 
          ConstrUnappliedValue.tupled(Serializers.CONSTRUNAPPLIEDVALUE.deserialize(args.get))
        case _ => throw new RuntimeException("StateValueSerializerBase: cannot deserialize " + (kind, args))
      }
    }

  }

  def create(b : Any) : StateValue = {
    StateValueSerializerBase.determineKind(b) match {
      case StateValueSerializerBase.Kind.RECURSIVEFUNCTIONVALUE =>
        RecursiveFunctionValue(null, null, null, null)
      case StateValueSerializerBase.Kind.CONSTRUNAPPLIEDVALUE =>
        ConstrUnappliedValue(null, null, null, null)
      case _ => null
    }
  }

  def assign(dest : StateValue, src : StateValue) : StateValue = {
    src match {
      case v : RecursiveFunctionValue =>
        val w = dest.asInstanceOf[RecursiveFunctionValue]
        w.state = v.state
        w.cases = v.cases
        w.cache = v.cache
        w.context = v.context
        dest
      case v : ConstrUnappliedValue =>
        val w = dest.asInstanceOf[ConstrUnappliedValue]
        w.state = v.state
        w.name = v.name
        w.param = v.param
        w.customtype = v.customtype
        dest
      case _ =>
        src
    }
  }

  protected val innerSerializer : Serializer[StateValue] = StateValueSerializerBase

}

final class CustomizableStateValueSerializer(store : UniquelyIdentifiableStore, CustomTypeSerializer : Serializer[CustomType],
  StateSerializer : Serializer[State], kernelSerializers : KernelSerializers, 
  ParseTreeSerializer : Serializer[ParseTree]) extends NestedSerializer[StateValue]
{

  private object StateValueSerializer extends UniquelyIdentifiableSerializer(store, 
    new BasicStateValueSerializer(this, CustomTypeSerializer, StateSerializer, kernelSerializers, ParseTreeSerializer), UISTypeCodes.STATEVALUE)

  protected val innerSerializer : Serializer[StateValue] = StateValueSerializer

}

final class StateValueRefSerializer(StateValueSerializer : Serializer[StateValue]) extends TransformSerializer(
  StateValueSerializer, (r : State.StateValueRef) => r.value, (v : StateValue) => State.StateValueRef(v))

final class BasicEnvSerializer(StateValueSerializer : Serializer[StateValue],
  CustomTypeSerializer : Serializer[CustomType]) extends TransformSerializer(
  TripleSerializer(
    MapSerializer(StringSerializer, CustomTypeSerializer),
    MapSerializer(StringSerializer, StateValueSerializer), 
    MapSerializer(StringSerializer, new StateValueRefSerializer(StateValueSerializer))),
  (env : State.Env) => (env.types, env.nonlinear, env.linear), State.Env.tupled)

final class BasicStateSerializer(ContextSerializer : Serializer[Context], EnvSerializer : Serializer[State.Env],
  CollectSerializer : Serializer[Collect]) extends TransformSerializer(
  QuadrupleSerializer(ContextSerializer, EnvSerializer, CollectSerializer, BooleanSerializer),
  (s : State) => (s.context, s.env, s.collect, s.canReturn),
  (s : (Context, State.Env, Collect, Boolean)) => new State(s._1, s._2, s._3, s._4))

final class CustomizableStateSerializer(store : UniquelyIdentifiableStore, val kernelSerializers : KernelSerializers) 
extends NestedSerializer[State] 
{

  val SourcePositionSerializer : Serializer[SourcePosition] = new BasicSourcePositionSerializer(new CustomizableSourceSerializer(store))
  val ParseTreeSerializer = new CustomizableParseTreeSerializer(SourcePositionSerializer, 
    kernelSerializers.IndexedNameSerializer, kernelSerializers.NamespaceSerializer, kernelSerializers.NameSerializer, 
    kernelSerializers.TermSerializer, kernelSerializers.TypeSerializer).ParseTreeSerializer
  val CustomTypeSerializer = new CustomizableCustomTypeSerializer(store, kernelSerializers.NamespaceSerializer)
  val StateValueSerializer = new CustomizableStateValueSerializer(store, CustomTypeSerializer, this, kernelSerializers, ParseTreeSerializer)
  val EnvSerializer = new UniquelyIdentifiableSerializer(store, new BasicEnvSerializer(StateValueSerializer, CustomTypeSerializer), UISTypeCodes.ENV)
  val CollectSerializer = new CustomizableCollectSerializer(StateValueSerializer)

  protected val innerSerializer : Serializer[State] = new UniquelyIdentifiableSerializer(store, new BasicStateSerializer(
    kernelSerializers.ContextSerializer, EnvSerializer, CollectSerializer), UISTypeCodes.STATE)

}

object StateSerializerGenerator {

  val collectCases = Vector("Zero", ("One", "OptionSerializer(StateValueSerializer)"), ("Multiple", "CollectorSerializer"))

  val stateValueCases = Vector(
    "NilValue",
    ("ContextValue", "ContextSerializer"),
    ("TheoremValue", "TheoremSerializer"),
    ("TermValue", "CTermSerializer"),
    ("TypeValue", "TypeSerializer"),
    ("BoolValue", "BooleanSerializer"),
    ("IntValue", "BigIntSerializer"),
    ("SimpleFunctionValue", "StateSerializer", "PTFunSerializer"),
    ("RecursiveFunctionValue", "StateSerializer", "VectorSerializer(PTDefCaseSerializer)", "NullableSerializer(MapSerializer(StateValueSerializer, StateValueSerializer))", "OptionSerializer(ContextSerializer)"),
    ("NativeFunctionValue", "NativeFunctionSerializer"),
    ("StringValue", "VectorSerializer(IntSerializer)"),
    ("TupleValue", "VectorSerializer(StateValueSerializer)", "BooleanSerializer"),
    ("SetValue", "SetSerializer(StateValueSerializer)"),
    ("MapValue", "MapSerializer(StateValueSerializer, StateValueSerializer)", "BooleanSerializer"),
    ("ConstrValue", "StringSerializer", "CustomTypeSerializer"),
    ("ConstrAppliedValue", "StringSerializer", "StateValueSerializer", "CustomTypeSerializer", "BooleanSerializer"),
    ("ConstrUnappliedValue", "StateSerializer", "StringSerializer", "PTPatternSerializer", "CustomTypeSerializer")
  )

  def _main(args : Array[String]) {
    val collectTool = new CaseClassSerializerTool("CollectSerializerBase", collectCases, "Collect")
    //collectTool.output()
    val stateValueTool = new CaseClassSerializerTool("StateValueSerializerBase", stateValueCases, "StateValue")
    stateValueTool.output()
  }

}