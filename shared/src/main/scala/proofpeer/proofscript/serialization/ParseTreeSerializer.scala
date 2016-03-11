package proofpeer.proofscript.serialization

import proofpeer.proofscript.frontend._
import ParseTree._
import proofpeer.general._
import proofpeer.indent.Span
import proofpeer.proofscript.logic._

object BasicSourceSerializer extends TransformSerializer[Source, (String, String)](
  PairSerializer(StringSerializer, StringSerializer), 
  (s : Source) => (s.namespace.toString, s.src.toString), 
  (n : (String, String)) => new Source(Namespace(n._1), n._2))

final class CustomizableSourceSerializer(store : UniquelyIdentifiableStore) extends UniquelyIdentifiableSerializer(
  store, BasicSourceSerializer, UISTypeCodes.SOURCE)

object SpanSerializer extends TransformSerializer(VectorSerializer(IntSerializer),
  (s : Span) => Vector(s.firstRow, s.lastRow, s.maxRowGap, s.leftMostInFirst, s.leftMost, s.leftMostFirst, s.leftMostRest, 
    s.rightMostLast, s.firstIndexIncl, s.lastIndexExcl),
  (s : Vector[Int]) => 
    if (s.size == 10) Span(s(0), s(1), s(2), s(3), s(4), s(5), s(6), s(7), s(8), s(9))
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
  NameSerializer : Serializer[Name],
  TermSerializer : Serializer[Term],
  TypeSerializer : Serializer[Type]) 
extends Serializer[TracksSourcePosition] 
{

  val ParseTreeSerializer = new TypecastSerializer[ParseTree, TracksSourcePosition](this)
  private val TracksSourcePositionSerializer = this

  val PretermSerializer = new CustomizablePretermSerializer(SourcePositionSerializer, IndexedNameSerializer, 
    NamespaceSerializer, NameSerializer, TermSerializer, TypeSerializer, ParseTreeSerializer)

  val PretypeSerializer = PretermSerializer.PretypeSerializer

  private class PTSerializer[Special <: TracksSourcePosition] extends Serializer[Special] {

    def serialize(special : Special) = TracksSourcePositionSerializer.serialize(special)

    def deserialize(serialized : Any) : Special = {
      TracksSourcePositionSerializer.deserialize(serialized).asInstanceOf[Special]
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
  private object ValueTypeSerializer extends PTSerializer[ValueType]
  private object DatatypeConstrSerializer extends PTSerializer[DatatypeConstr]
  private object DatatypeCaseSerializer extends PTSerializer[DatatypeCase]


  private object ParseTreeSerializerBase extends CaseClassSerializerBase[TracksSourcePosition] {

    object Kind {
      val NILEXPR = 0
      val LITERALCONTEXTEXPR = 1
      val BOOL = -1
      val INTEGER = 2
      val STRINGLITERAL = -2
      val QUALIFIEDID = 3
      val ID = -3
      val UNARYOPERATION = 4
      val BINARYOPERATION = -4
      val CMPOPERATION = 5
      val TUPLE = -5
      val SETLITERAL = 6
      val MAPLITERAL = -6
      val APP = 7
      val FUN = -7
      val TYPECAST = 8
      val LAZY = -8
      val LOGICTERM = 9
      val LOGICTYPE = -9
      val CONTROLFLOWEXPR = 10
      val DO = -10
      val IF = 11
      val WHILE = -11
      val FOR = 12
      val TIMEIT = -12
      val MATCHCASE = 13
      val MATCH = -13
      val CONTEXTCONTROL = 14
      val INCONTEXTCONTROL = -14
      val INLITERALCONTEXTCONTROL = 15
      val NEG = -15
      val NOT = 16
      val BANG = -16
      val RANGETO = 17
      val RANGEDOWNTO = -17
      val ADD = 18
      val SUB = -18
      val MUL = 19
      val DIV = -19
      val MOD = 20
      val AND = -20
      val OR = 21
      val PREPEND = -21
      val APPEND = 22
      val CONCAT = -22
      val MINUS = 23
      val EQ = -23
      val NEQ = 24
      val LE = -24
      val LEQ = 25
      val GR = -25
      val GEQ = 26
      val PANY = -26
      val PID = 27
      val PINT = -27
      val PBOOL = 28
      val PSTRING = -28
      val PLOGICTERM = 29
      val PLOGICTYPE = -29
      val PTUPLE = 30
      val PPREPEND = -30
      val PAPPEND = 31
      val PIF = -31
      val PAS = 32
      val PNIL = -32
      val PNILBANG = 33
      val PTYPE = -33
      val PCONSTR = 34
      val PDESTRUCT = -34
      val TYANY = 35
      val TYNIL = -35
      val TYCONTEXT = 36
      val TYTHEOREM = -36
      val TYTERM = 37
      val TYTYPE = -37
      val TYBOOLEAN = 38
      val TYINTEGER = -38
      val TYFUNCTION = 39
      val TYSTRING = -39
      val TYTUPLE = 40
      val TYMAP = -40
      val TYSET = 41
      val TYOPTION = -41
      val TYUNION = 42
      val TYCUSTOM = -42
      val COMMENT = 43
      val STCOMMENT = -43
      val STEXPR = 44
      val STCONTROLFLOW = -44
      val STSHOW = 45
      val STFAIL = -45
      val STASSERT = 46
      val STFAILURE = -46
      val STVAL = 47
      val STVALINTRO = -47
      val STASSIGN = 48
      val STDEF = -48
      val DEFCASE = 49
      val DATATYPECONSTR = -49
      val DATATYPECASE = 50
      val STDATATYPE = -50
      val STRETURN = 51
      val STASSUME = -51
      val STLET = 52
      val STCHOOSE = -52
      val STTHEOREM = 53
      val STTHEOREMBY = -53
      val STTHEORY = 54
      val BLOCK = -54
      val FRESHQUOTE = 55
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
      val SETLITERAL = VectorSerializer(ExprSerializer)
      val MAPLITERAL = VectorSerializer(PairSerializer(ExprSerializer, ExprSerializer))
      val APP = PairSerializer(ExprSerializer,ExprSerializer)
      val FUN = PairSerializer(PatternSerializer,BlockSerializer)
      val TYPECAST = PairSerializer(ExprSerializer,ValueTypeSerializer)
      val LAZY = ExprSerializer
      val LOGICTERM = PretermSerializer
      val LOGICTYPE = PretypeSerializer
      val CONTROLFLOWEXPR = ControlFlowSerializer
      val DO = PairSerializer(BlockSerializer,BooleanSerializer)
      val IF = TripleSerializer(ExprSerializer,BlockSerializer,BlockSerializer)
      val WHILE = PairSerializer(ExprSerializer,BlockSerializer)
      val FOR = TripleSerializer(PatternSerializer,ExprSerializer,BlockSerializer)
      val TIMEIT = BlockSerializer
      val MATCHCASE = PairSerializer(PatternSerializer,BlockSerializer)
      val MATCH = PairSerializer(ExprSerializer,VectorSerializer(MatchCaseSerializer))
      val CONTEXTCONTROL = PairSerializer(OptionSerializer(ExprSerializer),BlockSerializer)
      val INCONTEXTCONTROL = PairSerializer(OptionSerializer(ExprSerializer),BlockSerializer)
      val INLITERALCONTEXTCONTROL = PairSerializer(OptionSerializer(ExprSerializer),BlockSerializer)
      val PID = StringSerializer
      val PINT = BigIntSerializer
      val PBOOL = BooleanSerializer
      val PSTRING = VectorSerializer(IntSerializer)
      val PLOGICTERM = PretermSerializer
      val PLOGICTYPE = PretypeSerializer
      val PTUPLE = VectorSerializer(PatternSerializer)
      val PPREPEND = PairSerializer(PatternSerializer,PatternSerializer)
      val PAPPEND = PairSerializer(PatternSerializer,PatternSerializer)
      val PIF = PairSerializer(PatternSerializer,ExprSerializer)
      val PAS = PairSerializer(PatternSerializer,StringSerializer)
      val PTYPE = PairSerializer(PatternSerializer,ValueTypeSerializer)
      val PCONSTR = PairSerializer(NameSerializer,OptionSerializer(PatternSerializer))
      val PDESTRUCT = PairSerializer(StringSerializer,PatternSerializer)
      val TYOPTION = ValueTypeSerializer
      val TYUNION = PairSerializer(ValueTypeSerializer,ValueTypeSerializer)
      val TYCUSTOM = PairSerializer(OptionSerializer(NamespaceSerializer),StringSerializer)
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
      val STDEF = TripleSerializer(MapSerializer(StringSerializer,VectorSerializer(DefCaseSerializer)),BooleanSerializer,OptionSerializer(ExprSerializer))
      val DEFCASE = QuadrupleSerializer(StringSerializer,PatternSerializer,OptionSerializer(ValueTypeSerializer),BlockSerializer)
      val DATATYPECONSTR = PairSerializer(StringSerializer,OptionSerializer(PatternSerializer))
      val DATATYPECASE = PairSerializer(StringSerializer,VectorSerializer(DatatypeConstrSerializer))
      val STDATATYPE = VectorSerializer(DatatypeCaseSerializer)
      val STRETURN = OptionSerializer(ExprSerializer)
      val STASSUME = PairSerializer(OptionSerializer(StringSerializer),ExprSerializer)
      val STLET = PairSerializer(OptionSerializer(StringSerializer),ExprSerializer)
      val STCHOOSE = TripleSerializer(OptionSerializer(StringSerializer),ExprSerializer,BlockSerializer)
      val STTHEOREM = TripleSerializer(OptionSerializer(StringSerializer),ExprSerializer,BlockSerializer)
      val STTHEOREMBY = TripleSerializer(OptionSerializer(StringSerializer),ExprSerializer,ExprSerializer)
      val STTHEORY = TripleSerializer(NamespaceSerializer,ListSerializer(PairSerializer(IdSerializer,NamespaceSerializer)),ListSerializer(NamespaceSerializer))
      val BLOCK = VectorSerializer(StatementSerializer)
      val FRESHQUOTE = PairSerializer(BooleanSerializer,IdSerializer)
    }

    def decomposeAndSerialize(obj : TracksSourcePosition) : (Int, Option[Any]) = {
      obj match {
        case NilExpr =>
          (Kind.NILEXPR, None)
        case LiteralcontextExpr =>
          (Kind.LITERALCONTEXTEXPR, None)
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
        case SetLiteral(x) =>
          (Kind.SETLITERAL, Some(Serializers.SETLITERAL.serialize(x)))
        case MapLiteral(x) =>
          (Kind.MAPLITERAL, Some(Serializers.MAPLITERAL.serialize(x)))
        case t : App =>
          (Kind.APP, Some(Serializers.APP.serialize(App.unapply(t).get)))
        case t : Fun =>
          (Kind.FUN, Some(Serializers.FUN.serialize(Fun.unapply(t).get)))
        case t : TypeCast =>
          (Kind.TYPECAST, Some(Serializers.TYPECAST.serialize(TypeCast.unapply(t).get)))
        case Lazy(x) =>
          (Kind.LAZY, Some(Serializers.LAZY.serialize(x)))
        case LogicTerm(x) =>
          (Kind.LOGICTERM, Some(Serializers.LOGICTERM.serialize(x)))
        case LogicType(x) =>
          (Kind.LOGICTYPE, Some(Serializers.LOGICTYPE.serialize(x)))
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
        case Timeit(x) =>
          (Kind.TIMEIT, Some(Serializers.TIMEIT.serialize(x)))
        case t : MatchCase =>
          (Kind.MATCHCASE, Some(Serializers.MATCHCASE.serialize(MatchCase.unapply(t).get)))
        case t : Match =>
          (Kind.MATCH, Some(Serializers.MATCH.serialize(Match.unapply(t).get)))
        case t : ContextControl =>
          (Kind.CONTEXTCONTROL, Some(Serializers.CONTEXTCONTROL.serialize(ContextControl.unapply(t).get)))
        case t : InContextControl =>
          (Kind.INCONTEXTCONTROL, Some(Serializers.INCONTEXTCONTROL.serialize(InContextControl.unapply(t).get)))
        case t : InLiteralcontextControl =>
          (Kind.INLITERALCONTEXTCONTROL, Some(Serializers.INLITERALCONTEXTCONTROL.serialize(InLiteralcontextControl.unapply(t).get)))
        case Neg =>
          (Kind.NEG, None)
        case Not =>
          (Kind.NOT, None)
        case Bang =>
          (Kind.BANG, None)
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
        case Minus =>
          (Kind.MINUS, None)
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
        case PLogicTerm(x) =>
          (Kind.PLOGICTERM, Some(Serializers.PLOGICTERM.serialize(x)))
        case PLogicType(x) =>
          (Kind.PLOGICTYPE, Some(Serializers.PLOGICTYPE.serialize(x)))
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
        case PNilBang =>
          (Kind.PNILBANG, None)
        case t : PType =>
          (Kind.PTYPE, Some(Serializers.PTYPE.serialize(PType.unapply(t).get)))
        case t : PConstr =>
          (Kind.PCONSTR, Some(Serializers.PCONSTR.serialize(PConstr.unapply(t).get)))
        case t : PDestruct =>
          (Kind.PDESTRUCT, Some(Serializers.PDESTRUCT.serialize(PDestruct.unapply(t).get)))
        case TyAny =>
          (Kind.TYANY, None)
        case TyNil =>
          (Kind.TYNIL, None)
        case TyContext =>
          (Kind.TYCONTEXT, None)
        case TyTheorem =>
          (Kind.TYTHEOREM, None)
        case TyTerm =>
          (Kind.TYTERM, None)
        case TyType =>
          (Kind.TYTYPE, None)
        case TyBoolean =>
          (Kind.TYBOOLEAN, None)
        case TyInteger =>
          (Kind.TYINTEGER, None)
        case TyFunction =>
          (Kind.TYFUNCTION, None)
        case TyString =>
          (Kind.TYSTRING, None)
        case TyTuple =>
          (Kind.TYTUPLE, None)
        case TyMap =>
          (Kind.TYMAP, None)
        case TySet =>
          (Kind.TYSET, None)
        case TyOption(x) =>
          (Kind.TYOPTION, Some(Serializers.TYOPTION.serialize(x)))
        case t : TyUnion =>
          (Kind.TYUNION, Some(Serializers.TYUNION.serialize(TyUnion.unapply(t).get)))
        case t : TyCustom =>
          (Kind.TYCUSTOM, Some(Serializers.TYCUSTOM.serialize(TyCustom.unapply(t).get)))
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
        case t : STDef =>
          (Kind.STDEF, Some(Serializers.STDEF.serialize(STDef.unapply(t).get)))
        case t : DefCase =>
          (Kind.DEFCASE, Some(Serializers.DEFCASE.serialize(DefCase.unapply(t).get)))
        case t : DatatypeConstr =>
          (Kind.DATATYPECONSTR, Some(Serializers.DATATYPECONSTR.serialize(DatatypeConstr.unapply(t).get)))
        case t : DatatypeCase =>
          (Kind.DATATYPECASE, Some(Serializers.DATATYPECASE.serialize(DatatypeCase.unapply(t).get)))
        case STDatatype(x) =>
          (Kind.STDATATYPE, Some(Serializers.STDATATYPE.serialize(x)))
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
        case t : STTheoremBy =>
          (Kind.STTHEOREMBY, Some(Serializers.STTHEOREMBY.serialize(STTheoremBy.unapply(t).get)))
        case t : STTheory =>
          (Kind.STTHEORY, Some(Serializers.STTHEORY.serialize(STTheory.unapply(t).get)))
        case Block(x) =>
          (Kind.BLOCK, Some(Serializers.BLOCK.serialize(x)))
        case t : FreshQuote =>
          (Kind.FRESHQUOTE, Some(Serializers.FRESHQUOTE.serialize(FreshQuote.unapply(t).get)))
        case _ => throw new RuntimeException("ParseTreeSerializerBase: cannot serialize " + obj)
      }
    }

    def deserializeAndCompose(kind : Int, args : Option[Any]) : TracksSourcePosition = {
      kind match {
        case Kind.NILEXPR if args.isEmpty => 
          NilExpr
        case Kind.LITERALCONTEXTEXPR if args.isEmpty => 
          LiteralcontextExpr
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
        case Kind.SETLITERAL if args.isDefined => 
          SetLiteral(Serializers.SETLITERAL.deserialize(args.get))
        case Kind.MAPLITERAL if args.isDefined => 
          MapLiteral(Serializers.MAPLITERAL.deserialize(args.get))
        case Kind.APP if args.isDefined => 
          App.tupled(Serializers.APP.deserialize(args.get))
        case Kind.FUN if args.isDefined => 
          Fun.tupled(Serializers.FUN.deserialize(args.get))
        case Kind.TYPECAST if args.isDefined => 
          TypeCast.tupled(Serializers.TYPECAST.deserialize(args.get))
        case Kind.LAZY if args.isDefined => 
          Lazy(Serializers.LAZY.deserialize(args.get))
        case Kind.LOGICTERM if args.isDefined => 
          LogicTerm(Serializers.LOGICTERM.deserialize(args.get))
        case Kind.LOGICTYPE if args.isDefined => 
          LogicType(Serializers.LOGICTYPE.deserialize(args.get))
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
        case Kind.TIMEIT if args.isDefined => 
          Timeit(Serializers.TIMEIT.deserialize(args.get))
        case Kind.MATCHCASE if args.isDefined => 
          MatchCase.tupled(Serializers.MATCHCASE.deserialize(args.get))
        case Kind.MATCH if args.isDefined => 
          Match.tupled(Serializers.MATCH.deserialize(args.get))
        case Kind.CONTEXTCONTROL if args.isDefined => 
          ContextControl.tupled(Serializers.CONTEXTCONTROL.deserialize(args.get))
        case Kind.INCONTEXTCONTROL if args.isDefined => 
          InContextControl.tupled(Serializers.INCONTEXTCONTROL.deserialize(args.get))
        case Kind.INLITERALCONTEXTCONTROL if args.isDefined => 
          InLiteralcontextControl.tupled(Serializers.INLITERALCONTEXTCONTROL.deserialize(args.get))
        case Kind.NEG if args.isEmpty => 
          Neg
        case Kind.NOT if args.isEmpty => 
          Not
        case Kind.BANG if args.isEmpty => 
          Bang
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
        case Kind.MINUS if args.isEmpty => 
          Minus
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
        case Kind.PLOGICTERM if args.isDefined => 
          PLogicTerm(Serializers.PLOGICTERM.deserialize(args.get))
        case Kind.PLOGICTYPE if args.isDefined => 
          PLogicType(Serializers.PLOGICTYPE.deserialize(args.get))
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
        case Kind.PNILBANG if args.isEmpty => 
          PNilBang
        case Kind.PTYPE if args.isDefined => 
          PType.tupled(Serializers.PTYPE.deserialize(args.get))
        case Kind.PCONSTR if args.isDefined => 
          PConstr.tupled(Serializers.PCONSTR.deserialize(args.get))
        case Kind.PDESTRUCT if args.isDefined => 
          PDestruct.tupled(Serializers.PDESTRUCT.deserialize(args.get))
        case Kind.TYANY if args.isEmpty => 
          TyAny
        case Kind.TYNIL if args.isEmpty => 
          TyNil
        case Kind.TYCONTEXT if args.isEmpty => 
          TyContext
        case Kind.TYTHEOREM if args.isEmpty => 
          TyTheorem
        case Kind.TYTERM if args.isEmpty => 
          TyTerm
        case Kind.TYTYPE if args.isEmpty => 
          TyType
        case Kind.TYBOOLEAN if args.isEmpty => 
          TyBoolean
        case Kind.TYINTEGER if args.isEmpty => 
          TyInteger
        case Kind.TYFUNCTION if args.isEmpty => 
          TyFunction
        case Kind.TYSTRING if args.isEmpty => 
          TyString
        case Kind.TYTUPLE if args.isEmpty => 
          TyTuple
        case Kind.TYMAP if args.isEmpty => 
          TyMap
        case Kind.TYSET if args.isEmpty => 
          TySet
        case Kind.TYOPTION if args.isDefined => 
          TyOption(Serializers.TYOPTION.deserialize(args.get))
        case Kind.TYUNION if args.isDefined => 
          TyUnion.tupled(Serializers.TYUNION.deserialize(args.get))
        case Kind.TYCUSTOM if args.isDefined => 
          TyCustom.tupled(Serializers.TYCUSTOM.deserialize(args.get))
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
          STDef.tupled(Serializers.STDEF.deserialize(args.get))
        case Kind.DEFCASE if args.isDefined => 
          DefCase.tupled(Serializers.DEFCASE.deserialize(args.get))
        case Kind.DATATYPECONSTR if args.isDefined => 
          DatatypeConstr.tupled(Serializers.DATATYPECONSTR.deserialize(args.get))
        case Kind.DATATYPECASE if args.isDefined => 
          DatatypeCase.tupled(Serializers.DATATYPECASE.deserialize(args.get))
        case Kind.STDATATYPE if args.isDefined => 
          STDatatype(Serializers.STDATATYPE.deserialize(args.get))
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
        case Kind.STTHEOREMBY if args.isDefined => 
          STTheoremBy.tupled(Serializers.STTHEOREMBY.deserialize(args.get))
        case Kind.STTHEORY if args.isDefined => 
          STTheory.tupled(Serializers.STTHEORY.deserialize(args.get))
        case Kind.BLOCK if args.isDefined => 
          Block(Serializers.BLOCK.deserialize(args.get))
        case Kind.FRESHQUOTE if args.isDefined => 
          FreshQuote.tupled(Serializers.FRESHQUOTE.deserialize(args.get))
        case _ => throw new RuntimeException("ParseTreeSerializerBase: cannot deserialize " + (kind, args))
      }
    }

  }

  private def decodeInt(b : Any) : Int = {
    b match {
      case i : Int => i
      case l : Long => l.toInt
      case _ => throw new RuntimeException("ParseTreeSerializer.decodeInt " + b + " failed")
    }
  }

  def serialize(parsetree : TracksSourcePosition)  = {
    val (kind, args) = ParseTreeSerializerBase.decomposeAndSerialize(parsetree)
    val serializedSourcePosition = SourcePositionSerializer.serialize(parsetree.sourcePosition)
    args match {
      case None => Vector(kind, serializedSourcePosition)
      case Some(args) => Vector(kind, serializedSourcePosition, args)
    }
  }

  def deserialize(serialized : Any) : TracksSourcePosition = {
    serialized match {
      case Vector(_kind, serializedSourcePosition) =>
        val kind = decodeInt(_kind)
        val sourcePosition = SourcePositionSerializer.deserialize(serializedSourcePosition)
        val tree = ParseTreeSerializerBase.deserializeAndCompose(kind.toInt, None)
        tree.sourcePosition = sourcePosition
        tree
      case Vector(_kind, serializedSourcePosition, args) =>
        val kind = decodeInt(_kind)
        val sourcePosition = SourcePositionSerializer.deserialize(serializedSourcePosition)
        val tree = ParseTreeSerializerBase.deserializeAndCompose(kind.toInt, Some(args))
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
    "LiteralcontextExpr",
    ("Bool", "BooleanSerializer"),
    ("Integer", "BigIntSerializer"),
    ("StringLiteral", "VectorSerializer(IntSerializer)"),
    ("QualifiedId", "NamespaceSerializer", "StringSerializer"),
    ("Id", "StringSerializer"),
    ("UnaryOperation", "UnaryOperatorSerializer", "ExprSerializer"),
    ("BinaryOperation", "BinaryOperatorSerializer", "ExprSerializer", "ExprSerializer"),
    ("CmpOperation", "VectorSerializer(CmpOperatorSerializer)", "VectorSerializer(ExprSerializer)"),
    ("Tuple", "VectorSerializer(ExprSerializer)"),
    ("SetLiteral", "VectorSerializer(ExprSerializer)"),
    ("MapLiteral", "VectorSerializer(PairSerializer(ExprSerializer, ExprSerializer))"),
    ("App", "ExprSerializer", "ExprSerializer"),
    ("Fun", "PatternSerializer", "BlockSerializer"),
    ("TypeCast", "ExprSerializer", "ValueTypeSerializer"),
    ("Lazy", "ExprSerializer"),
    ("LogicTerm", "PretermSerializer"),
    ("LogicType", "PretypeSerializer"),
    ("ControlFlowExpr", "ControlFlowSerializer"),
    ("Do", "BlockSerializer", "BooleanSerializer"),
    ("If", "ExprSerializer", "BlockSerializer", "BlockSerializer"),
    ("While", "ExprSerializer", "BlockSerializer"),
    ("For", "PatternSerializer", "ExprSerializer", "BlockSerializer"),
    ("Timeit", "BlockSerializer"),
    ("MatchCase", "PatternSerializer", "BlockSerializer"),
    ("Match", "ExprSerializer", "VectorSerializer(MatchCaseSerializer)"),
    ("ContextControl", "OptionSerializer(ExprSerializer)", "BlockSerializer"),
    ("InContextControl", "OptionSerializer(ExprSerializer)", "BlockSerializer"),
    ("InLiteralcontextControl", "OptionSerializer(ExprSerializer)", "BlockSerializer"),    
    "Neg",
    "Not",
    "Bang",
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
    "Minus",
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
    ("PLogicTerm", "PretermSerializer"),
    ("PLogicType", "PretypeSerializer"),
    ("PTuple", "VectorSerializer(PatternSerializer)"),
    ("PPrepend", "PatternSerializer", "PatternSerializer"),
    ("PAppend", "PatternSerializer", "PatternSerializer"),
    ("PIf", "PatternSerializer", "ExprSerializer"),
    ("PAs", "PatternSerializer", "StringSerializer"),
    "PNil",
    "PNilBang",
    ("PType", "PatternSerializer", "ValueTypeSerializer"),
    ("PConstr", "NameSerializer", "OptionSerializer(PatternSerializer)"),
    ("PDestruct", "StringSerializer", "PatternSerializer"),
    "TyAny", 
    "TyNil", 
    "TyContext", 
    "TyTheorem", 
    "TyTerm",
    "TyType", 
    "TyBoolean", 
    "TyInteger", 
    "TyFunction", 
    "TyString", 
    "TyTuple",
    "TyMap",
    "TySet",
    ("TyOption", "ValueTypeSerializer"),
    ("TyUnion", "ValueTypeSerializer", "ValueTypeSerializer"),
    ("TyCustom", "OptionSerializer(NamespaceSerializer)", "StringSerializer"),
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
    ("STDef", "MapSerializer(StringSerializer,VectorSerializer(DefCaseSerializer))", "BooleanSerializer", "OptionSerializer(ExprSerializer)"),
    ("DefCase", "StringSerializer", "PatternSerializer", "OptionSerializer(ValueTypeSerializer)", "BlockSerializer"),
    ("DatatypeConstr", "StringSerializer", "OptionSerializer(PatternSerializer)"),
    ("DatatypeCase", "StringSerializer", "VectorSerializer(DatatypeConstrSerializer)"),
    ("STDatatype", "VectorSerializer(DatatypeCaseSerializer)"),
    ("STReturn", "OptionSerializer(ExprSerializer)"),
    ("STAssume", "OptionSerializer(StringSerializer)", "ExprSerializer"),
    ("STLet", "OptionSerializer(StringSerializer)", "ExprSerializer"),
    ("STChoose", "OptionSerializer(StringSerializer)", "ExprSerializer", "BlockSerializer"),
    ("STTheorem", "OptionSerializer(StringSerializer)", "ExprSerializer", "BlockSerializer"),
    ("STTheoremBy", "OptionSerializer(StringSerializer)", "ExprSerializer", "ExprSerializer"),    
    ("STTheory", "NamespaceSerializer", "ListSerializer(PairSerializer(IdSerializer,NamespaceSerializer))", "ListSerializer(NamespaceSerializer)"),
    ("Block", "VectorSerializer(StatementSerializer)"),
    ("FreshQuote", "BooleanSerializer", "IdSerializer")
  )
  
  /** Rename _main to main to generate the code. */
  def _main(args : Array[String]) {
    val tool = new CaseClassSerializerTool("ParseTreeSerializerBase", names, "TracksSourcePosition")
    print("private ")
    tool.output()
  }

}

