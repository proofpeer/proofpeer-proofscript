package proofpeer.proofscript.serialization

import proofpeer.proofscript.frontend._
import ParseTree._
import proofpeer.general._
import proofpeer.indent.Span
import proofpeer.proofscript.logic._

final class CustomizableSourceSerializer(store : UniquelyIdentifiableStore) extends UniquelyIdentifiableSerializer(store,
  new TransformSerializer(StringSerializer, (s : Source) => s.toString, (s : String) => new Source { override def toString = s }),
  UISTypeCodes.SOURCE)

object SpanSerializer extends TransformSerializer(VectorSerializer(IntSerializer),
  (s : Span) => Vector(s.firstRow, s.lastRow, s.leftMostInFirst, s.leftMost, s.leftMostFirst, s.leftMostRest, 
    s.rightMostLast, s.firstTokenIndex, s.lastTokenIndex),
  (s : Vector[Int]) => 
    if (s.size == 9) Span(s(0), s(1), s(2), s(3), s(4), s(5), s(6), s(7), s(8))
    else throw new RuntimeException("cannot deserialize span: " + s))

final class BasicSourcePositionSerializer(SourceSerializer : Serializer[Source]) 
extends TransformSerializer[SourcePosition, Option[(Source, Option[Span])]](
  OptionSerializer(PairSerializer(SourceSerializer, OptionSerializer(SpanSerializer))),
  (p : SourcePosition) => if (p == null) None else Some((p.source, p.span)),
  (p : Option[(Source, Option[Span])]) => {
    p match {
      case None => null
      case Some((_source, _span)) => new SourcePosition { val source = _source; val span = _span }
    }
  })

final class CustomizableParseTreeSerializer(
  SourcePositionSerializer : Serializer[SourcePosition], 
  IndexedNameSerializer : Serializer[IndexedName],
  NamespaceSerializer : Serializer[Namespace],
  NameSerializer : Serializer[Name]) 
extends Serializer[ParseTree] 
{

  private val ParseTreeSerializer = this

  val PretermSerializer = new CustomizablePretermSerializer(SourcePositionSerializer, IndexedNameSerializer, 
    NamespaceSerializer, NameSerializer, this)

  private class PTSerializer[Special <: TracksSourcePosition] extends Serializer[Special] {

    def serialize(special : Special) = ParseTreeSerializerBase.serialize(special)

    def deserialize(serialized : Any) : Special = {
      ParseTreeSerializerBase.deserialize(serialized).asInstanceOf[Special]
    }
  
  }

  private object StatementSerializer extends PTSerializer[Statement]
  private object IdSerializer extends PTSerializer[Id]
  private object BlockSerializer extends PTSerializer[Block]
  private object ExprSerializer extends PTSerializer[Expr]
  private object DefCaseSerializer extends PTSerializer[DefCase]
  private object PatternSerializer extends PTSerializer[Pattern]
  private object UnaryOperatorSerializer extends PTSerializer[UnaryOperator]
  private object BinaryOperatorSerializer extends PTSerializer[BinaryOperator]
  private object CmpOperatorSerializer extends PTSerializer[CmpOperator]
  private object ControlFlowSerializer extends PTSerializer[ControlFlow]
  private object MatchCaseSerializer extends PTSerializer[MatchCase]
  private object CommentSerializer extends PTSerializer[Comment]

  private object ParseTreeSerializerBase extends CaseClassSerializerBase[TracksSourcePosition] {

    object Kind {
      val NILEXPR = 0
      val BOOL = 1
      val INTEGER = -1
      val STRINGLITERAL = 2
      val QUALIFIEDID = -2
      val ID = 3
      val UNARYOPERATION = -3
      val BINARYOPERATION = 4
      val CMPOPERATION = -4
      val TUPLE = 5
      val APP = -5
      val FUN = 6
      val LAZY = -6
      val LOGICTERM = 7
      val CONTROLFLOWEXPR = -7
      val DO = 8
      val IF = -8
      val WHILE = 9
      val FOR = -9
      val MATCHCASE = 10
      val MATCH = -10
      val CONTEXTCONTROL = 11
      val NEG = -11
      val NOT = 12
      val RANGETO = -12
      val RANGEDOWNTO = 13
      val ADD = -13
      val SUB = 14
      val MUL = -14
      val DIV = 15
      val MOD = -15
      val AND = 16
      val OR = -16
      val PREPEND = 17
      val APPEND = -17
      val CONCAT = 18
      val EQ = -18
      val NEQ = 19
      val LE = -19
      val LEQ = 20
      val GR = -20
      val GEQ = 21
      val PANY = -21
      val PID = 22
      val PINT = -22
      val PBOOL = 23
      val PSTRING = -23
      val PLOGIC = 24
      val PTUPLE = -24
      val PPREPEND = 25
      val PAPPEND = -25
      val PIF = 26
      val PAS = -26
      val PNIL = 27
      val COMMENT = -27
      val STCOMMENT = 28
      val STEXPR = -28
      val STCONTROLFLOW = 29
      val STSHOW = -29
      val STFAIL = 30
      val STASSERT = -30
      val STFAILURE = 31
      val STVAL = -31
      val STVALINTRO = 32
      val STASSIGN = -32
      val STDEF = 33
      val DEFCASE = -33
      val STRETURN = 34
      val STASSUME = -34
      val STLET = 35
      val STCHOOSE = -35
      val STTHEOREM = 36
      val STTHEORY = -36
      val BLOCK = 37
    }

    object Serializers {
      val BOOL = BooleanSerializer
      val INTEGER = BigIntSerializer
      val STRINGLITERAL = VectorSerializer(IntSerializer)
      val QUALIFIEDID = PairSerializer(NamespaceSerializer,StringSerializer)
      val ID = StringSerializer
      val UNARYOPERATION = PairSerializer(UnaryOperatorSerializer,ExprSerializer)
      val BINARYOPERATION = TripleSerializer(BinaryOperatorSerializer,ExprSerializer,ExprSerializer)
      val CMPOPERATION = PairSerializer(VectorSerializer(CmpOperatorSerializer),VectorSerializer(ExprSerializer))
      val TUPLE = VectorSerializer(ExprSerializer)
      val APP = PairSerializer(ExprSerializer,ExprSerializer)
      val FUN = PairSerializer(PatternSerializer,BlockSerializer)
      val LAZY = ExprSerializer
      val LOGICTERM = PretermSerializer
      val CONTROLFLOWEXPR = ControlFlowSerializer
      val DO = PairSerializer(BlockSerializer,BooleanSerializer)
      val IF = TripleSerializer(ExprSerializer,BlockSerializer,BlockSerializer)
      val WHILE = PairSerializer(ExprSerializer,BlockSerializer)
      val FOR = TripleSerializer(PatternSerializer,ExprSerializer,BlockSerializer)
      val MATCHCASE = PairSerializer(PatternSerializer,BlockSerializer)
      val MATCH = PairSerializer(ExprSerializer,VectorSerializer(MatchCaseSerializer))
      val CONTEXTCONTROL = PairSerializer(OptionSerializer(ExprSerializer),BlockSerializer)
      val PID = StringSerializer
      val PINT = BigIntSerializer
      val PBOOL = BooleanSerializer
      val PSTRING = VectorSerializer(IntSerializer)
      val PLOGIC = PretermSerializer
      val PTUPLE = VectorSerializer(PatternSerializer)
      val PPREPEND = PairSerializer(PatternSerializer,PatternSerializer)
      val PAPPEND = PairSerializer(PatternSerializer,PatternSerializer)
      val PIF = PairSerializer(PatternSerializer,ExprSerializer)
      val PAS = PairSerializer(PatternSerializer,StringSerializer)
      val COMMENT = StringSerializer
      val STCOMMENT = CommentSerializer
      val STEXPR = ExprSerializer
      val STCONTROLFLOW = ControlFlowSerializer
      val STSHOW = ExprSerializer
      val STFAIL = OptionSerializer(ExprSerializer)
      val STASSERT = ExprSerializer
      val STFAILURE = BlockSerializer
      val STVAL = PairSerializer(PatternSerializer,BlockSerializer)
      val STVALINTRO = ListSerializer(IdSerializer)
      val STASSIGN = PairSerializer(PatternSerializer,BlockSerializer)
      val STDEF = MapSerializer(StringSerializer,VectorSerializer(DefCaseSerializer))
      val DEFCASE = TripleSerializer(StringSerializer,PatternSerializer,BlockSerializer)
      val STRETURN = OptionSerializer(ExprSerializer)
      val STASSUME = PairSerializer(OptionSerializer(StringSerializer),ExprSerializer)
      val STLET = PairSerializer(OptionSerializer(StringSerializer),ExprSerializer)
      val STCHOOSE = TripleSerializer(OptionSerializer(StringSerializer),ExprSerializer,BlockSerializer)
      val STTHEOREM = TripleSerializer(OptionSerializer(StringSerializer),ExprSerializer,BlockSerializer)
      val STTHEORY = TripleSerializer(NamespaceSerializer,ListSerializer(PairSerializer(IdSerializer,NamespaceSerializer)),ListSerializer(NamespaceSerializer))
      val BLOCK = VectorSerializer(StatementSerializer)
    }

    def decomposeAndSerialize(obj : TracksSourcePosition) : (Int, Option[Any]) = {
      obj match {
        case NilExpr =>
          (Kind.NILEXPR, None)
        case Bool(x) =>
          (Kind.BOOL, Some(Serializers.BOOL.serialize(x)))
        case Integer(x) =>
          (Kind.INTEGER, Some(Serializers.INTEGER.serialize(x)))
        case StringLiteral(x) =>
          (Kind.STRINGLITERAL, Some(Serializers.STRINGLITERAL.serialize(x)))
        case t : QualifiedId =>
          (Kind.QUALIFIEDID, Some(Serializers.QUALIFIEDID.serialize(QualifiedId.unapply(t).get)))
        case Id(x) =>
          (Kind.ID, Some(Serializers.ID.serialize(x)))
        case t : UnaryOperation =>
          (Kind.UNARYOPERATION, Some(Serializers.UNARYOPERATION.serialize(UnaryOperation.unapply(t).get)))
        case t : BinaryOperation =>
          (Kind.BINARYOPERATION, Some(Serializers.BINARYOPERATION.serialize(BinaryOperation.unapply(t).get)))
        case t : CmpOperation =>
          (Kind.CMPOPERATION, Some(Serializers.CMPOPERATION.serialize(CmpOperation.unapply(t).get)))
        case Tuple(x) =>
          (Kind.TUPLE, Some(Serializers.TUPLE.serialize(x)))
        case t : App =>
          (Kind.APP, Some(Serializers.APP.serialize(App.unapply(t).get)))
        case t : Fun =>
          (Kind.FUN, Some(Serializers.FUN.serialize(Fun.unapply(t).get)))
        case Lazy(x) =>
          (Kind.LAZY, Some(Serializers.LAZY.serialize(x)))
        case LogicTerm(x) =>
          (Kind.LOGICTERM, Some(Serializers.LOGICTERM.serialize(x)))
        case ControlFlowExpr(x) =>
          (Kind.CONTROLFLOWEXPR, Some(Serializers.CONTROLFLOWEXPR.serialize(x)))
        case t : Do =>
          (Kind.DO, Some(Serializers.DO.serialize(Do.unapply(t).get)))
        case t : If =>
          (Kind.IF, Some(Serializers.IF.serialize(If.unapply(t).get)))
        case t : While =>
          (Kind.WHILE, Some(Serializers.WHILE.serialize(While.unapply(t).get)))
        case t : For =>
          (Kind.FOR, Some(Serializers.FOR.serialize(For.unapply(t).get)))
        case t : MatchCase =>
          (Kind.MATCHCASE, Some(Serializers.MATCHCASE.serialize(MatchCase.unapply(t).get)))
        case t : Match =>
          (Kind.MATCH, Some(Serializers.MATCH.serialize(Match.unapply(t).get)))
        case t : ContextControl =>
          (Kind.CONTEXTCONTROL, Some(Serializers.CONTEXTCONTROL.serialize(ContextControl.unapply(t).get)))
        case Neg =>
          (Kind.NEG, None)
        case Not =>
          (Kind.NOT, None)
        case RangeTo =>
          (Kind.RANGETO, None)
        case RangeDownto =>
          (Kind.RANGEDOWNTO, None)
        case Add =>
          (Kind.ADD, None)
        case Sub =>
          (Kind.SUB, None)
        case Mul =>
          (Kind.MUL, None)
        case Div =>
          (Kind.DIV, None)
        case Mod =>
          (Kind.MOD, None)
        case And =>
          (Kind.AND, None)
        case Or =>
          (Kind.OR, None)
        case Prepend =>
          (Kind.PREPEND, None)
        case Append =>
          (Kind.APPEND, None)
        case Concat =>
          (Kind.CONCAT, None)
        case Eq =>
          (Kind.EQ, None)
        case NEq =>
          (Kind.NEQ, None)
        case Le =>
          (Kind.LE, None)
        case Leq =>
          (Kind.LEQ, None)
        case Gr =>
          (Kind.GR, None)
        case Geq =>
          (Kind.GEQ, None)
        case PAny =>
          (Kind.PANY, None)
        case PId(x) =>
          (Kind.PID, Some(Serializers.PID.serialize(x)))
        case PInt(x) =>
          (Kind.PINT, Some(Serializers.PINT.serialize(x)))
        case PBool(x) =>
          (Kind.PBOOL, Some(Serializers.PBOOL.serialize(x)))
        case PString(x) =>
          (Kind.PSTRING, Some(Serializers.PSTRING.serialize(x)))
        case PLogic(x) =>
          (Kind.PLOGIC, Some(Serializers.PLOGIC.serialize(x)))
        case PTuple(x) =>
          (Kind.PTUPLE, Some(Serializers.PTUPLE.serialize(x)))
        case t : PPrepend =>
          (Kind.PPREPEND, Some(Serializers.PPREPEND.serialize(PPrepend.unapply(t).get)))
        case t : PAppend =>
          (Kind.PAPPEND, Some(Serializers.PAPPEND.serialize(PAppend.unapply(t).get)))
        case t : PIf =>
          (Kind.PIF, Some(Serializers.PIF.serialize(PIf.unapply(t).get)))
        case t : PAs =>
          (Kind.PAS, Some(Serializers.PAS.serialize(PAs.unapply(t).get)))
        case PNil =>
          (Kind.PNIL, None)
        case Comment(x) =>
          (Kind.COMMENT, Some(Serializers.COMMENT.serialize(x)))
        case STComment(x) =>
          (Kind.STCOMMENT, Some(Serializers.STCOMMENT.serialize(x)))
        case STExpr(x) =>
          (Kind.STEXPR, Some(Serializers.STEXPR.serialize(x)))
        case STControlFlow(x) =>
          (Kind.STCONTROLFLOW, Some(Serializers.STCONTROLFLOW.serialize(x)))
        case STShow(x) =>
          (Kind.STSHOW, Some(Serializers.STSHOW.serialize(x)))
        case STFail(x) =>
          (Kind.STFAIL, Some(Serializers.STFAIL.serialize(x)))
        case STAssert(x) =>
          (Kind.STASSERT, Some(Serializers.STASSERT.serialize(x)))
        case STFailure(x) =>
          (Kind.STFAILURE, Some(Serializers.STFAILURE.serialize(x)))
        case t : STVal =>
          (Kind.STVAL, Some(Serializers.STVAL.serialize(STVal.unapply(t).get)))
        case STValIntro(x) =>
          (Kind.STVALINTRO, Some(Serializers.STVALINTRO.serialize(x)))
        case t : STAssign =>
          (Kind.STASSIGN, Some(Serializers.STASSIGN.serialize(STAssign.unapply(t).get)))
        case STDef(x) =>
          (Kind.STDEF, Some(Serializers.STDEF.serialize(x)))
        case t : DefCase =>
          (Kind.DEFCASE, Some(Serializers.DEFCASE.serialize(DefCase.unapply(t).get)))
        case STReturn(x) =>
          (Kind.STRETURN, Some(Serializers.STRETURN.serialize(x)))
        case t : STAssume =>
          (Kind.STASSUME, Some(Serializers.STASSUME.serialize(STAssume.unapply(t).get)))
        case t : STLet =>
          (Kind.STLET, Some(Serializers.STLET.serialize(STLet.unapply(t).get)))
        case t : STChoose =>
          (Kind.STCHOOSE, Some(Serializers.STCHOOSE.serialize(STChoose.unapply(t).get)))
        case t : STTheorem =>
          (Kind.STTHEOREM, Some(Serializers.STTHEOREM.serialize(STTheorem.unapply(t).get)))
        case t : STTheory =>
          (Kind.STTHEORY, Some(Serializers.STTHEORY.serialize(STTheory.unapply(t).get)))
        case Block(x) =>
          (Kind.BLOCK, Some(Serializers.BLOCK.serialize(x)))
        case _ => throw new RuntimeException("ParseTreeSerializerBase: cannot serialize " + obj)
      }
    }

    def deserializeAndCompose(kind : Int, args : Option[Any]) : TracksSourcePosition = {
      kind match {
        case Kind.NILEXPR if args.isEmpty => 
          NilExpr
        case Kind.BOOL if args.isDefined => 
          Bool(Serializers.BOOL.deserialize(args.get))
        case Kind.INTEGER if args.isDefined => 
          Integer(Serializers.INTEGER.deserialize(args.get))
        case Kind.STRINGLITERAL if args.isDefined => 
          StringLiteral(Serializers.STRINGLITERAL.deserialize(args.get))
        case Kind.QUALIFIEDID if args.isDefined => 
          QualifiedId.tupled(Serializers.QUALIFIEDID.deserialize(args.get))
        case Kind.ID if args.isDefined => 
          Id(Serializers.ID.deserialize(args.get))
        case Kind.UNARYOPERATION if args.isDefined => 
          UnaryOperation.tupled(Serializers.UNARYOPERATION.deserialize(args.get))
        case Kind.BINARYOPERATION if args.isDefined => 
          BinaryOperation.tupled(Serializers.BINARYOPERATION.deserialize(args.get))
        case Kind.CMPOPERATION if args.isDefined => 
          CmpOperation.tupled(Serializers.CMPOPERATION.deserialize(args.get))
        case Kind.TUPLE if args.isDefined => 
          Tuple(Serializers.TUPLE.deserialize(args.get))
        case Kind.APP if args.isDefined => 
          App.tupled(Serializers.APP.deserialize(args.get))
        case Kind.FUN if args.isDefined => 
          Fun.tupled(Serializers.FUN.deserialize(args.get))
        case Kind.LAZY if args.isDefined => 
          Lazy(Serializers.LAZY.deserialize(args.get))
        case Kind.LOGICTERM if args.isDefined => 
          LogicTerm(Serializers.LOGICTERM.deserialize(args.get))
        case Kind.CONTROLFLOWEXPR if args.isDefined => 
          ControlFlowExpr(Serializers.CONTROLFLOWEXPR.deserialize(args.get))
        case Kind.DO if args.isDefined => 
          Do.tupled(Serializers.DO.deserialize(args.get))
        case Kind.IF if args.isDefined => 
          If.tupled(Serializers.IF.deserialize(args.get))
        case Kind.WHILE if args.isDefined => 
          While.tupled(Serializers.WHILE.deserialize(args.get))
        case Kind.FOR if args.isDefined => 
          For.tupled(Serializers.FOR.deserialize(args.get))
        case Kind.MATCHCASE if args.isDefined => 
          MatchCase.tupled(Serializers.MATCHCASE.deserialize(args.get))
        case Kind.MATCH if args.isDefined => 
          Match.tupled(Serializers.MATCH.deserialize(args.get))
        case Kind.CONTEXTCONTROL if args.isDefined => 
          ContextControl.tupled(Serializers.CONTEXTCONTROL.deserialize(args.get))
        case Kind.NEG if args.isEmpty => 
          Neg
        case Kind.NOT if args.isEmpty => 
          Not
        case Kind.RANGETO if args.isEmpty => 
          RangeTo
        case Kind.RANGEDOWNTO if args.isEmpty => 
          RangeDownto
        case Kind.ADD if args.isEmpty => 
          Add
        case Kind.SUB if args.isEmpty => 
          Sub
        case Kind.MUL if args.isEmpty => 
          Mul
        case Kind.DIV if args.isEmpty => 
          Div
        case Kind.MOD if args.isEmpty => 
          Mod
        case Kind.AND if args.isEmpty => 
          And
        case Kind.OR if args.isEmpty => 
          Or
        case Kind.PREPEND if args.isEmpty => 
          Prepend
        case Kind.APPEND if args.isEmpty => 
          Append
        case Kind.CONCAT if args.isEmpty => 
          Concat
        case Kind.EQ if args.isEmpty => 
          Eq
        case Kind.NEQ if args.isEmpty => 
          NEq
        case Kind.LE if args.isEmpty => 
          Le
        case Kind.LEQ if args.isEmpty => 
          Leq
        case Kind.GR if args.isEmpty => 
          Gr
        case Kind.GEQ if args.isEmpty => 
          Geq
        case Kind.PANY if args.isEmpty => 
          PAny
        case Kind.PID if args.isDefined => 
          PId(Serializers.PID.deserialize(args.get))
        case Kind.PINT if args.isDefined => 
          PInt(Serializers.PINT.deserialize(args.get))
        case Kind.PBOOL if args.isDefined => 
          PBool(Serializers.PBOOL.deserialize(args.get))
        case Kind.PSTRING if args.isDefined => 
          PString(Serializers.PSTRING.deserialize(args.get))
        case Kind.PLOGIC if args.isDefined => 
          PLogic(Serializers.PLOGIC.deserialize(args.get))
        case Kind.PTUPLE if args.isDefined => 
          PTuple(Serializers.PTUPLE.deserialize(args.get))
        case Kind.PPREPEND if args.isDefined => 
          PPrepend.tupled(Serializers.PPREPEND.deserialize(args.get))
        case Kind.PAPPEND if args.isDefined => 
          PAppend.tupled(Serializers.PAPPEND.deserialize(args.get))
        case Kind.PIF if args.isDefined => 
          PIf.tupled(Serializers.PIF.deserialize(args.get))
        case Kind.PAS if args.isDefined => 
          PAs.tupled(Serializers.PAS.deserialize(args.get))
        case Kind.PNIL if args.isEmpty => 
          PNil
        case Kind.COMMENT if args.isDefined => 
          Comment(Serializers.COMMENT.deserialize(args.get))
        case Kind.STCOMMENT if args.isDefined => 
          STComment(Serializers.STCOMMENT.deserialize(args.get))
        case Kind.STEXPR if args.isDefined => 
          STExpr(Serializers.STEXPR.deserialize(args.get))
        case Kind.STCONTROLFLOW if args.isDefined => 
          STControlFlow(Serializers.STCONTROLFLOW.deserialize(args.get))
        case Kind.STSHOW if args.isDefined => 
          STShow(Serializers.STSHOW.deserialize(args.get))
        case Kind.STFAIL if args.isDefined => 
          STFail(Serializers.STFAIL.deserialize(args.get))
        case Kind.STASSERT if args.isDefined => 
          STAssert(Serializers.STASSERT.deserialize(args.get))
        case Kind.STFAILURE if args.isDefined => 
          STFailure(Serializers.STFAILURE.deserialize(args.get))
        case Kind.STVAL if args.isDefined => 
          STVal.tupled(Serializers.STVAL.deserialize(args.get))
        case Kind.STVALINTRO if args.isDefined => 
          STValIntro(Serializers.STVALINTRO.deserialize(args.get))
        case Kind.STASSIGN if args.isDefined => 
          STAssign.tupled(Serializers.STASSIGN.deserialize(args.get))
        case Kind.STDEF if args.isDefined => 
          STDef(Serializers.STDEF.deserialize(args.get))
        case Kind.DEFCASE if args.isDefined => 
          DefCase.tupled(Serializers.DEFCASE.deserialize(args.get))
        case Kind.STRETURN if args.isDefined => 
          STReturn(Serializers.STRETURN.deserialize(args.get))
        case Kind.STASSUME if args.isDefined => 
          STAssume.tupled(Serializers.STASSUME.deserialize(args.get))
        case Kind.STLET if args.isDefined => 
          STLet.tupled(Serializers.STLET.deserialize(args.get))
        case Kind.STCHOOSE if args.isDefined => 
          STChoose.tupled(Serializers.STCHOOSE.deserialize(args.get))
        case Kind.STTHEOREM if args.isDefined => 
          STTheorem.tupled(Serializers.STTHEOREM.deserialize(args.get))
        case Kind.STTHEORY if args.isDefined => 
          STTheory.tupled(Serializers.STTHEORY.deserialize(args.get))
        case Kind.BLOCK if args.isDefined => 
          Block(Serializers.BLOCK.deserialize(args.get))
        case _ => throw new RuntimeException("ParseTreeSerializerBase: cannot deserialize " + (kind, args))
      }
    }

  }

  def serialize(parsetree : ParseTree)  = {
    val (kind, args) = ParseTreeSerializerBase.decomposeAndSerialize(parsetree)
    val serializedSourcePosition = SourcePositionSerializer.serialize(parsetree.sourcePosition)
    args match {
      case None => Vector(kind, serializedSourcePosition)
      case Some(args) => Vector(kind, serializedSourcePosition, args)
    }
  }

  def deserialize(serialized : Any) : ParseTree = {
    serialized match {
      case Vector(kind : Long, serializedSourcePosition) =>
        val sourcePosition = SourcePositionSerializer.deserialize(serializedSourcePosition)
        val tree = ParseTreeSerializerBase.deserializeAndCompose(kind.toInt, None).asInstanceOf[ParseTree]
        tree.sourcePosition = sourcePosition
        tree
      case Vector(kind : Long, serializedSourcePosition, args) =>
        val sourcePosition = SourcePositionSerializer.deserialize(serializedSourcePosition)
        val tree = ParseTreeSerializerBase.deserializeAndCompose(kind.toInt, Some(args)).asInstanceOf[ParseTree]
        tree.sourcePosition = sourcePosition
        tree
      case _ => throw new RuntimeException("cannot deserialize parse tree: " + serialized)
    }
  }

}

/** This is code used to create most of the above code. It is not needed during runtime, just during programming. */
object ParseTreeSerializerGenerator {

  val names : Vector[Any] = Vector(
    "NilExpr",
    ("Bool", "BooleanSerializer"),
    ("Integer", "BigIntSerializer"),
    ("StringLiteral", "VectorSerializer(IntSerializer)"),
    ("QualifiedId", "NamespaceSerializer", "StringSerializer"),
    ("Id", "StringSerializer"),
    ("UnaryOperation", "UnaryOperatorSerializer", "ExprSerializer"),
    ("BinaryOperation", "BinaryOperatorSerializer", "ExprSerializer", "ExprSerializer"),
    ("CmpOperation", "VectorSerializer(CmpOperatorSerializer)", "VectorSerializer(ExprSerializer)"),
    ("Tuple", "VectorSerializer(ExprSerializer)"),
    ("App", "ExprSerializer", "ExprSerializer"),
    ("Fun", "PatternSerializer", "BlockSerializer"),
    ("Lazy", "ExprSerializer"),
    ("LogicTerm", "PretermSerializer"),
    ("ControlFlowExpr", "ControlFlowSerializer"),
    ("Do", "BlockSerializer", "BooleanSerializer"),
    ("If", "ExprSerializer", "BlockSerializer", "BlockSerializer"),
    ("While", "ExprSerializer", "BlockSerializer"),
    ("For", "PatternSerializer", "ExprSerializer", "BlockSerializer"),
    ("MatchCase", "PatternSerializer", "BlockSerializer"),
    ("Match", "ExprSerializer", "VectorSerializer(MatchCaseSerializer)"),
    ("ContextControl", "OptionSerializer(ExprSerializer)", "BlockSerializer"),
    "Neg",
    "Not",
    "RangeTo",
    "RangeDownto",
    "Add",
    "Sub",
    "Mul",
    "Div",
    "Mod",
    "And",
    "Or",
    "Prepend",
    "Append",
    "Concat",
    "Eq",
    "NEq",
    "Le",
    "Leq",
    "Gr",
    "Geq",
    "PAny",
    ("PId", "StringSerializer"),
    ("PInt", "BigIntSerializer"),
    ("PBool", "BooleanSerializer"),
    ("PString", "VectorSerializer(IntSerializer)"),
    ("PLogic", "PretermSerializer"),
    ("PTuple", "VectorSerializer(PatternSerializer)"),
    ("PPrepend", "PatternSerializer", "PatternSerializer"),
    ("PAppend", "PatternSerializer", "PatternSerializer"),
    ("PIf", "PatternSerializer", "ExprSerializer"),
    ("PAs", "PatternSerializer", "StringSerializer"),
    "PNil",
    ("Comment", "StringSerializer"),
    ("STComment", "CommentSerializer"),
    ("STExpr", "ExprSerializer"),
    ("STControlFlow", "ControlFlowSerializer"),
    ("STShow", "ExprSerializer"),
    ("STFail", "OptionSerializer(ExprSerializer)"),
    ("STAssert", "ExprSerializer"),
    ("STFailure", "BlockSerializer"),
    ("STVal", "PatternSerializer", "BlockSerializer"),
    ("STValIntro", "ListSerializer(IdSerializer)"),
    ("STAssign", "PatternSerializer", "BlockSerializer"),
    ("STDef", "MapSerializer(StringSerializer,VectorSerializer(DefCaseSerializer))"),
    ("DefCase", "StringSerializer", "PatternSerializer", "BlockSerializer"),
    ("STReturn", "OptionSerializer(ExprSerializer)"),
    ("STAssume", "OptionSerializer(StringSerializer)", "ExprSerializer"),
    ("STLet", "OptionSerializer(StringSerializer)", "ExprSerializer"),
    ("STChoose", "OptionSerializer(StringSerializer)", "ExprSerializer", "BlockSerializer"),
    ("STTheorem", "OptionSerializer(StringSerializer)", "ExprSerializer", "BlockSerializer"),
    ("STTheory", "NamespaceSerializer", "ListSerializer(PairSerializer(IdSerializer,NamespaceSerializer))", "ListSerializer(NamespaceSerializer)"),
    ("Block", "VectorSerializer(StatementSerializer)")
  )
  
  /** Rename _main to main to generate the code. */
  def _main(args : Array[String]) {
    val tool = new CaseClassSerializerTool("ParseTreeSerializerBase", names, "TracksSourcePosition")
    print("private ")
    tool.output()
  }

}

