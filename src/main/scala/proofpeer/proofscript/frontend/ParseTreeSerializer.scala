package proofpeer.proofscript.frontend

import ParseTree._
import proofpeer.general._
import proofpeer.indent.Span
import proofpeer.proofscript.logic.Namespace
import proofpeer.proofscript.logic.PretermSerializer

case class SerializedSourcePosition(source : Source, span : Option[Span]) extends SourcePosition

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

class ParseTreeSerializer(source : Source, computeSpan : (Int, Int) => Span) extends Serializer[TracksSourcePosition, Vector[Any]] {

  private val PTS = this

  private class PTSerializer[Special <: TracksSourcePosition] extends Serializer[Special, Any] {

    def serialize(special : Special) : Any = PTS.serialize(special)

    def deserialize(serialized : Any) : Special = {
      PTS.deserialize(serialized).asInstanceOf[Special]
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

    def decomposeAndSerialize(obj : TracksSourcePosition) : (Int, Vector[Any]) = {
      obj match {
        case NilExpr =>
          (Kind.NILEXPR, Vector())
        case Bool(x) =>
          (Kind.BOOL, Vector(Serializers.BOOL.serialize(x)))
        case Integer(x) =>
          (Kind.INTEGER, Vector(Serializers.INTEGER.serialize(x)))
        case StringLiteral(x) =>
          (Kind.STRINGLITERAL, Serializers.STRINGLITERAL.serialize(x))
        case t : QualifiedId =>
          (Kind.QUALIFIEDID, Serializers.QUALIFIEDID.serialize(QualifiedId.unapply(t).get))
        case Id(x) =>
          (Kind.ID, Vector(Serializers.ID.serialize(x)))
        case t : UnaryOperation =>
          (Kind.UNARYOPERATION, Serializers.UNARYOPERATION.serialize(UnaryOperation.unapply(t).get))
        case t : BinaryOperation =>
          (Kind.BINARYOPERATION, Serializers.BINARYOPERATION.serialize(BinaryOperation.unapply(t).get))
        case t : CmpOperation =>
          (Kind.CMPOPERATION, Serializers.CMPOPERATION.serialize(CmpOperation.unapply(t).get))
        case Tuple(x) =>
          (Kind.TUPLE, Serializers.TUPLE.serialize(x))
        case t : App =>
          (Kind.APP, Serializers.APP.serialize(App.unapply(t).get))
        case t : Fun =>
          (Kind.FUN, Serializers.FUN.serialize(Fun.unapply(t).get))
        case Lazy(x) =>
          (Kind.LAZY, Vector(Serializers.LAZY.serialize(x)))
        case LogicTerm(x) =>
          (Kind.LOGICTERM, Vector(Serializers.LOGICTERM.serialize(x)))
        case ControlFlowExpr(x) =>
          (Kind.CONTROLFLOWEXPR, Vector(Serializers.CONTROLFLOWEXPR.serialize(x)))
        case t : Do =>
          (Kind.DO, Serializers.DO.serialize(Do.unapply(t).get))
        case t : If =>
          (Kind.IF, Serializers.IF.serialize(If.unapply(t).get))
        case t : While =>
          (Kind.WHILE, Serializers.WHILE.serialize(While.unapply(t).get))
        case t : For =>
          (Kind.FOR, Serializers.FOR.serialize(For.unapply(t).get))
        case t : MatchCase =>
          (Kind.MATCHCASE, Serializers.MATCHCASE.serialize(MatchCase.unapply(t).get))
        case t : Match =>
          (Kind.MATCH, Serializers.MATCH.serialize(Match.unapply(t).get))
        case t : ContextControl =>
          (Kind.CONTEXTCONTROL, Serializers.CONTEXTCONTROL.serialize(ContextControl.unapply(t).get))
        case Neg =>
          (Kind.NEG, Vector())
        case Not =>
          (Kind.NOT, Vector())
        case RangeTo =>
          (Kind.RANGETO, Vector())
        case RangeDownto =>
          (Kind.RANGEDOWNTO, Vector())
        case Add =>
          (Kind.ADD, Vector())
        case Sub =>
          (Kind.SUB, Vector())
        case Mul =>
          (Kind.MUL, Vector())
        case Div =>
          (Kind.DIV, Vector())
        case Mod =>
          (Kind.MOD, Vector())
        case And =>
          (Kind.AND, Vector())
        case Or =>
          (Kind.OR, Vector())
        case Prepend =>
          (Kind.PREPEND, Vector())
        case Append =>
          (Kind.APPEND, Vector())
        case Concat =>
          (Kind.CONCAT, Vector())
        case Eq =>
          (Kind.EQ, Vector())
        case NEq =>
          (Kind.NEQ, Vector())
        case Le =>
          (Kind.LE, Vector())
        case Leq =>
          (Kind.LEQ, Vector())
        case Gr =>
          (Kind.GR, Vector())
        case Geq =>
          (Kind.GEQ, Vector())
        case PAny =>
          (Kind.PANY, Vector())
        case PId(x) =>
          (Kind.PID, Vector(Serializers.PID.serialize(x)))
        case PInt(x) =>
          (Kind.PINT, Vector(Serializers.PINT.serialize(x)))
        case PBool(x) =>
          (Kind.PBOOL, Vector(Serializers.PBOOL.serialize(x)))
        case PString(x) =>
          (Kind.PSTRING, Serializers.PSTRING.serialize(x))
        case PLogic(x) =>
          (Kind.PLOGIC, Vector(Serializers.PLOGIC.serialize(x)))
        case PTuple(x) =>
          (Kind.PTUPLE, Serializers.PTUPLE.serialize(x))
        case t : PPrepend =>
          (Kind.PPREPEND, Serializers.PPREPEND.serialize(PPrepend.unapply(t).get))
        case t : PAppend =>
          (Kind.PAPPEND, Serializers.PAPPEND.serialize(PAppend.unapply(t).get))
        case t : PIf =>
          (Kind.PIF, Serializers.PIF.serialize(PIf.unapply(t).get))
        case t : PAs =>
          (Kind.PAS, Serializers.PAS.serialize(PAs.unapply(t).get))
        case PNil =>
          (Kind.PNIL, Vector())
        case Comment(x) =>
          (Kind.COMMENT, Vector(Serializers.COMMENT.serialize(x)))
        case STComment(x) =>
          (Kind.STCOMMENT, Vector(Serializers.STCOMMENT.serialize(x)))
        case STExpr(x) =>
          (Kind.STEXPR, Vector(Serializers.STEXPR.serialize(x)))
        case STControlFlow(x) =>
          (Kind.STCONTROLFLOW, Vector(Serializers.STCONTROLFLOW.serialize(x)))
        case STShow(x) =>
          (Kind.STSHOW, Vector(Serializers.STSHOW.serialize(x)))
        case STFail(x) =>
          (Kind.STFAIL, Serializers.STFAIL.serialize(x))
        case STAssert(x) =>
          (Kind.STASSERT, Vector(Serializers.STASSERT.serialize(x)))
        case STFailure(x) =>
          (Kind.STFAILURE, Vector(Serializers.STFAILURE.serialize(x)))
        case t : STVal =>
          (Kind.STVAL, Serializers.STVAL.serialize(STVal.unapply(t).get))
        case STValIntro(x) =>
          (Kind.STVALINTRO, Serializers.STVALINTRO.serialize(x))
        case t : STAssign =>
          (Kind.STASSIGN, Serializers.STASSIGN.serialize(STAssign.unapply(t).get))
        case STDef(x) =>
          (Kind.STDEF, Serializers.STDEF.serialize(x))
        case t : DefCase =>
          (Kind.DEFCASE, Serializers.DEFCASE.serialize(DefCase.unapply(t).get))
        case STReturn(x) =>
          (Kind.STRETURN, Serializers.STRETURN.serialize(x))
        case t : STAssume =>
          (Kind.STASSUME, Serializers.STASSUME.serialize(STAssume.unapply(t).get))
        case t : STLet =>
          (Kind.STLET, Serializers.STLET.serialize(STLet.unapply(t).get))
        case t : STChoose =>
          (Kind.STCHOOSE, Serializers.STCHOOSE.serialize(STChoose.unapply(t).get))
        case t : STTheorem =>
          (Kind.STTHEOREM, Serializers.STTHEOREM.serialize(STTheorem.unapply(t).get))
        case t : STTheory =>
          (Kind.STTHEORY, Serializers.STTHEORY.serialize(STTheory.unapply(t).get))
        case Block(x) =>
          (Kind.BLOCK, Serializers.BLOCK.serialize(x))
        case _ => throw new RuntimeException("ParseTreeSerializerBase: cannot serialize " + obj)
      }
    }

    def deserializeAndCompose(kind : Int, args : Vector[Any]) : TracksSourcePosition = {
      kind match {
        case Kind.NILEXPR if args.size == 0 => 
          NilExpr
        case Kind.BOOL if args.size == 1 => 
          Bool(Serializers.BOOL.deserialize(args(0)))
        case Kind.INTEGER if args.size == 1 => 
          Integer(Serializers.INTEGER.deserialize(args(0)))
        case Kind.STRINGLITERAL => 
          StringLiteral(Serializers.STRINGLITERAL.deserialize(args))
        case Kind.QUALIFIEDID => 
          QualifiedId.tupled(Serializers.QUALIFIEDID.deserialize(args))
        case Kind.ID if args.size == 1 => 
          Id(Serializers.ID.deserialize(args(0)))
        case Kind.UNARYOPERATION => 
          UnaryOperation.tupled(Serializers.UNARYOPERATION.deserialize(args))
        case Kind.BINARYOPERATION => 
          BinaryOperation.tupled(Serializers.BINARYOPERATION.deserialize(args))
        case Kind.CMPOPERATION => 
          CmpOperation.tupled(Serializers.CMPOPERATION.deserialize(args))
        case Kind.TUPLE => 
          Tuple(Serializers.TUPLE.deserialize(args))
        case Kind.APP => 
          App.tupled(Serializers.APP.deserialize(args))
        case Kind.FUN => 
          Fun.tupled(Serializers.FUN.deserialize(args))
        case Kind.LAZY if args.size == 1 => 
          Lazy(Serializers.LAZY.deserialize(args(0)))
        case Kind.LOGICTERM if args.size == 1 => 
          LogicTerm(Serializers.LOGICTERM.deserialize(args(0)))
        case Kind.CONTROLFLOWEXPR if args.size == 1 => 
          ControlFlowExpr(Serializers.CONTROLFLOWEXPR.deserialize(args(0)))
        case Kind.DO => 
          Do.tupled(Serializers.DO.deserialize(args))
        case Kind.IF => 
          If.tupled(Serializers.IF.deserialize(args))
        case Kind.WHILE => 
          While.tupled(Serializers.WHILE.deserialize(args))
        case Kind.FOR => 
          For.tupled(Serializers.FOR.deserialize(args))
        case Kind.MATCHCASE => 
          MatchCase.tupled(Serializers.MATCHCASE.deserialize(args))
        case Kind.MATCH => 
          Match.tupled(Serializers.MATCH.deserialize(args))
        case Kind.CONTEXTCONTROL => 
          ContextControl.tupled(Serializers.CONTEXTCONTROL.deserialize(args))
        case Kind.NEG if args.size == 0 => 
          Neg
        case Kind.NOT if args.size == 0 => 
          Not
        case Kind.RANGETO if args.size == 0 => 
          RangeTo
        case Kind.RANGEDOWNTO if args.size == 0 => 
          RangeDownto
        case Kind.ADD if args.size == 0 => 
          Add
        case Kind.SUB if args.size == 0 => 
          Sub
        case Kind.MUL if args.size == 0 => 
          Mul
        case Kind.DIV if args.size == 0 => 
          Div
        case Kind.MOD if args.size == 0 => 
          Mod
        case Kind.AND if args.size == 0 => 
          And
        case Kind.OR if args.size == 0 => 
          Or
        case Kind.PREPEND if args.size == 0 => 
          Prepend
        case Kind.APPEND if args.size == 0 => 
          Append
        case Kind.CONCAT if args.size == 0 => 
          Concat
        case Kind.EQ if args.size == 0 => 
          Eq
        case Kind.NEQ if args.size == 0 => 
          NEq
        case Kind.LE if args.size == 0 => 
          Le
        case Kind.LEQ if args.size == 0 => 
          Leq
        case Kind.GR if args.size == 0 => 
          Gr
        case Kind.GEQ if args.size == 0 => 
          Geq
        case Kind.PANY if args.size == 0 => 
          PAny
        case Kind.PID if args.size == 1 => 
          PId(Serializers.PID.deserialize(args(0)))
        case Kind.PINT if args.size == 1 => 
          PInt(Serializers.PINT.deserialize(args(0)))
        case Kind.PBOOL if args.size == 1 => 
          PBool(Serializers.PBOOL.deserialize(args(0)))
        case Kind.PSTRING => 
          PString(Serializers.PSTRING.deserialize(args))
        case Kind.PLOGIC if args.size == 1 => 
          PLogic(Serializers.PLOGIC.deserialize(args(0)))
        case Kind.PTUPLE => 
          PTuple(Serializers.PTUPLE.deserialize(args))
        case Kind.PPREPEND => 
          PPrepend.tupled(Serializers.PPREPEND.deserialize(args))
        case Kind.PAPPEND => 
          PAppend.tupled(Serializers.PAPPEND.deserialize(args))
        case Kind.PIF => 
          PIf.tupled(Serializers.PIF.deserialize(args))
        case Kind.PAS => 
          PAs.tupled(Serializers.PAS.deserialize(args))
        case Kind.PNIL if args.size == 0 => 
          PNil
        case Kind.COMMENT if args.size == 1 => 
          Comment(Serializers.COMMENT.deserialize(args(0)))
        case Kind.STCOMMENT if args.size == 1 => 
          STComment(Serializers.STCOMMENT.deserialize(args(0)))
        case Kind.STEXPR if args.size == 1 => 
          STExpr(Serializers.STEXPR.deserialize(args(0)))
        case Kind.STCONTROLFLOW if args.size == 1 => 
          STControlFlow(Serializers.STCONTROLFLOW.deserialize(args(0)))
        case Kind.STSHOW if args.size == 1 => 
          STShow(Serializers.STSHOW.deserialize(args(0)))
        case Kind.STFAIL => 
          STFail(Serializers.STFAIL.deserialize(args))
        case Kind.STASSERT if args.size == 1 => 
          STAssert(Serializers.STASSERT.deserialize(args(0)))
        case Kind.STFAILURE if args.size == 1 => 
          STFailure(Serializers.STFAILURE.deserialize(args(0)))
        case Kind.STVAL => 
          STVal.tupled(Serializers.STVAL.deserialize(args))
        case Kind.STVALINTRO => 
          STValIntro(Serializers.STVALINTRO.deserialize(args))
        case Kind.STASSIGN => 
          STAssign.tupled(Serializers.STASSIGN.deserialize(args))
        case Kind.STDEF => 
          STDef(Serializers.STDEF.deserialize(args))
        case Kind.DEFCASE => 
          DefCase.tupled(Serializers.DEFCASE.deserialize(args))
        case Kind.STRETURN => 
          STReturn(Serializers.STRETURN.deserialize(args))
        case Kind.STASSUME => 
          STAssume.tupled(Serializers.STASSUME.deserialize(args))
        case Kind.STLET => 
          STLet.tupled(Serializers.STLET.deserialize(args))
        case Kind.STCHOOSE => 
          STChoose.tupled(Serializers.STCHOOSE.deserialize(args))
        case Kind.STTHEOREM => 
          STTheorem.tupled(Serializers.STTHEOREM.deserialize(args))
        case Kind.STTHEORY => 
          STTheory.tupled(Serializers.STTHEORY.deserialize(args))
        case Kind.BLOCK => 
          Block(Serializers.BLOCK.deserialize(args))
        case _ => throw new RuntimeException("ParseTreeSerializerBase: cannot deserialize " + (kind, args))
      }
    }

  }

  def serialize(parsetree : TracksSourcePosition) : Vector[Any] = {
    val (kind, args) : (Int, Vector[Any]) =
      ParseTreeSerializerBase.decomposeAndSerialize(parsetree)
    val (firstTokenIndex, lastTokenIndex) =
      if (parsetree.sourcePosition == null) 
        (-1, -1)
      else 
        parsetree.sourcePosition.span match {
          case None => (-1, -1)
          case Some(span) => (span.firstTokenIndex, span.lastTokenIndex)
        }
    kind +: firstTokenIndex +: lastTokenIndex +: args
  }

  private def toInt(v : Any) = v.asInstanceOf[Long].toInt

  def deserialize(serialized : Any) : TracksSourcePosition = {
    serialized match {
      case v : Vector[Any] if v.size >= 3 =>
        val kind = toInt(v(0))
        val firstTokenIndex = toInt(v(1))
        val lastTokenIndex = toInt(v(2))
        val args : Vector[Any] = v.drop(3)
        val tree = ParseTreeSerializerBase.deserializeAndCompose(kind, args)
        if (firstTokenIndex < 0)
          tree.sourcePosition = SerializedSourcePosition(source, None)
        else
          tree.sourcePosition = SerializedSourcePosition(source, Some(computeSpan(firstTokenIndex, lastTokenIndex)))
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

