package proofpeer.proofscript.frontend

import proofpeer.general.StringUtils
import proofpeer.indent.{ParseTree => IndentParseTree, _}
import proofpeer.indent.regex._
import proofpeer.indent.{Constraint => CS}
import ParseTree._

import proofpeer.proofscript.logic.{Preterm, Syntax, Namespace}

class ProofScriptGrammar(annotate : (Any, Option[Span]) => Any) {
    
def lex(terminal : String, expr : RegularExpr, prio : Option[Int] = None) : Grammar = 
  Grammar(ScanRule(terminal, "\\root", prio, expr))

var keywords : Set[String] = Set()

def keyword(terminal : String, kw : String) : Grammar = {
  keywords += kw
  lex(terminal, string(kw), Some(2))  
}

/*

≤
LESS-THAN OR EQUAL TO
Unicode: U+2264, UTF-8: E2 89 A4

≥
GREATER-THAN OR EQUAL TO
Unicode: U+2265, UTF-8: E2 89 A5

⇒
RIGHTWARDS DOUBLE ARROW
Unicode: U+21D2, UTF-8: E2 87 92

≔
COLON EQUALS
Unicode: U+2254, UTF-8: E2 89 94

'
APOSTROPHE
Unicode: U+0027, UTF-8: 27

*/ 

val hexdigit = alt(chars('a', 'f'), chars('A', 'F'), chars('0', '9'))

def g_literals = 
  lex("HexDigit", hexdigit) ++
  lex("QuotationMark", char('"')) ++
  lex("StringLiteralToken", REPEAT1(alt(
    string("\\n"),
    string("\\\\"),
    string("\\\""),
    seq(char('\\'), char('u'), hexdigit, hexdigit, hexdigit, hexdigit),
    seq(char('\\'), char('U'), hexdigit, hexdigit, hexdigit, hexdigit, hexdigit, hexdigit),
    char(0x21),
    chars(0x23, 0x5B),
    chars(0x5D, 0x7E),
    chars(0xA0, Int.MaxValue)))) ++
  lex("Hash", char('#')) ++
  lex("AnyToken", REPEAT1(CHAR(Range.universal))) ++
  lex("Plus", char('+')) ++  
  lex("Minus", char('-')) ++
  lex("Times", char('*')) ++
  lex("Slash", char('/')) ++
  lex("Le", char('<')) ++
  lex("Gr", char('>')) ++
  lex("Leq", ALT(char(0x2264), string("<="))) ++
  lex("Geq", ALT(char(0x2265), string(">="))) ++
  lex("QuestionMark", char('?')) ++
  lex("ExclamationMark", char('!')) ++
  lex("SquareBracketOpen", char('[')) ++
  lex("SquareBracketClose", char(']')) ++
  lex("DoubleArrow", ALT(char(0x21D2), string("=>"))) ++
  lex("SingleArrow", ALT(char(0x2192), string("->"))) ++
  lex("ScriptEq", string("==")) ++
  lex("ScriptNotEq", ALT(char(0x2260), string("<>"))) ++  
  lex("Apostrophe", char(0x27)) ++
  lex("Prepend", string("<+")) ++
  lex("Append", string("+>")) ++
  lex("Concat", string("++")) ++
  lex("MinusMinus", string("--")) ++
  keyword("Val", "val") ++
  keyword("Def", "def") ++
  keyword("Table", "table") ++
  keyword("Datatype", "datatype") ++
  keyword("Mod", "mod") ++ 
  keyword("ScriptOr", "or") ++ 
  keyword("ScriptAnd", "and") ++ 
  keyword("ScriptNot", "not") ++ 
  keyword("ScriptTrue", "true") ++ 
  keyword("ScriptFalse", "false") ++ 
  keyword("Lazy", "lazy") ++ 
  keyword("If", "if") ++ 
  keyword("Then", "then") ++ 
  keyword("Else", "else") ++ 
  keyword("While", "while") ++ 
  keyword("Do", "do") ++ 
  keyword("For", "for") ++ 
  keyword("In", "in") ++ 
  keyword("Match", "match") ++ 
  keyword("Case", "case") ++ 
  keyword("Timeit", "timeit") ++ 
  keyword("Return", "return") ++ 
  keyword("Assume", "assume") ++ 
  keyword("Let", "let") ++ 
  keyword("Choose", "choose") ++ 
  keyword("Theory", "theory") ++ 
  keyword("Extends", "extends") ++ 
  keyword("Context", "context") ++ 
  keyword("Show", "show") ++ 
  keyword("Fail", "fail") ++ 
  keyword("Nil", "nil") ++ 
  keyword("To", "to") ++ 
  keyword("Downto", "downto") ++ 
  keyword("Theorem", "theorem") ++ 
  keyword("Assert", "assert") ++ 
  keyword("Failure", "failure") ++ 
  keyword("As", "as") ++
  keyword("By", "by") ++
  keyword("TyNil", "Nil") ++
  keyword("TyTheorem", "Theorem") ++
  keyword("TyTerm", "Term") ++
  keyword("TyString", "String") ++
  keyword("TyType", "Type") ++
  keyword("TyContext", "Context") ++
  keyword("TyBoolean", "Boolean") ++
  keyword("TyInteger", "Integer") ++
  keyword("TyFunction", "Function") ++
  keyword("TyTuple", "Tuple") ++
  keyword("TyMap", "Map") ++
  keyword("TySet", "Set") 

def optspan(span : Span) : Option[Span] = {
  if (span == null) None else Some(span)
}

def arule(n : String, rhs : String, constraint : Constraint,
          action : ParseContext => Any) : Grammar = 
{
  def annotatedAction(c : ParseContext) : Any = {     
    annotate(action(c), optspan(c.span))
  }
  val (r, i) = string2rhsi(rhs)
  Grammar(ParseRule(n, r, i, constraint, annotatedAction))
}

def annotateUnop(b : UnaryOperator, span : Span) : UnaryOperator = 
  annotate(b, optspan(span)).asInstanceOf[UnaryOperator]

def annotateBinop(b : BinaryOperator, span : Span) : BinaryOperator = 
  annotate(b, optspan(span)).asInstanceOf[BinaryOperator]

def arule(n : String, rhs : String, action : ParseContext => Any) : Grammar = 
  arule(n, rhs, Constraint.unconstrained, action)

def mkTuple(elements : Vector[Expr], collapse : Boolean) : Expr = {
  if (collapse && elements.size == 1) 
    elements.head
  else
    Tuple(elements)
}

def mkTuplePattern(elements : Vector[Pattern], collapse : Boolean) : Pattern = {
  if (collapse && elements.size == 1) 
    elements.head
  else
    PTuple(elements)
}

def mkNamePattern(nametext : String, arg : Option[Pattern]) : Pattern = {
  val name = Syntax.parseName(nametext)
  if (StringUtils.isASCIIUpperLetter(name.name.name(0))) 
    PConstr(name, arg)
  else {
    if (name.namespace.isDefined)
      PError("unqualified identifier expected")
    else {
      arg match {
        case None => PId(name.toString)
        case Some(arg) => PDestruct(name.toString, arg)
      }
    }
  }
}

def mkTyCustom(text : String) : TyCustom = {
  val name = Syntax.parseName(text)
  TyCustom(name.namespace, name.name.toString)
}

def mkStringLiteral(c : ParseContext, quot1 : Span, quot2 : Span) : StringLiteral = 
{
  import proofpeer.general.StringUtils
  val len = quot2.lastIndexExcl - quot1.firstIndexIncl
  val s = c.document.getText(quot1.firstIndexIncl, len)
  mkStringLiteralFromCodes(StringUtils.codePoints(s.substring(1, s.length - 1)))
}

def mkStringLiteralFromCodes(escapedCodes : Vector[Int]) : StringLiteral = 
{
  def readInt(i : Int, j : Int) : Int = {
    var v = 0
    for (k <- i until j) {
      v = v * 16
      val c = escapedCodes(k) 
      if (c >= '0' && c <= '9') v = v + (c - '0')
      else if (c >= 'a' && c <= 'z') v = v + (c - 'a' + 10)
      else if (c >= 'A' && c <= 'Z') v = v + (c - 'A' + 10)
      else throw new RuntimeException("hex digit expected, but found "+c)
    }
    v
  }
  var codes : Vector[Int] = Vector()
  var i = 0
  val len = escapedCodes.size
  while (i < len) {
    val c = escapedCodes(i)
    if (c == 0x5C) {
      val d = escapedCodes(i + 1)
      i = i + 2
      d match {
        case 'n' => codes = codes :+ 0x0A
        case '"' => codes = codes :+ 0x22
        case '\\' => codes = codes :+ 0x5C
        case 'u' => 
          codes = codes :+ readInt(i, i + 4)
          i = i + 4
        case 'U' =>
          codes = codes :+ readInt(i, i + 8)
          i = i + 8
        case _ => throw new RuntimeException ("internal error: unexpected escape character code "+d)
      }
    } else {
      codes = codes :+ c
      i = i + 1
    }
  }
  StringLiteral(codes)
}

def Subalign(a : String, b : String) = CS.or(CS.Indent(a, b), CS.Align(a, b))

val g_expr =
  arule("StringLiteral", "", c => null) ++
  arule("StringLiteral", "StringLiteral StringLiteralToken", c => null) ++
  arule("PrimitiveExpr", "Name", c => mkId(Syntax.parseName(c.text))) ++
  arule("Int", "Digits", c => Integer(BigInt(c.text, 10))) ++
  arule("Int", "Minus Digits", c => Integer(-BigInt(c.text("Digits"), 10))) ++  
  arule("PrimitiveExpr", "Digits", c => Integer(BigInt(c.text("Digits"), 10))) ++
  arule("PrimitiveExpr", "RoundBracketOpen ExprList RoundBracketClose", c => mkTuple(c.ExprList, true)) ++
  arule("PrimitiveExpr", "SquareBracketOpen ExprList SquareBracketClose", c => mkTuple(c.ExprList, false)) ++
  arule("PrimitiveExpr", "CurlyBracketOpen ExprSetList1 CurlyBracketClose", c => SetLiteral(c.ExprSetList1)) ++
  arule("PrimitiveExpr", "CurlyBracketOpen ExprMapList1 CurlyBracketClose", c => MapLiteral(c.ExprMapList1)) ++
  arule("PrimitiveExpr", "CurlyBracketOpen CurlyBracketClose", c => SetLiteral(Vector())) ++
  arule("PrimitiveExpr", "CurlyBracketOpen SingleArrow CurlyBracketClose", c => MapLiteral(Vector())) ++  
  arule("PrimitiveExpr", "ScriptTrue", c => Bool(true)) ++  
  arule("PrimitiveExpr", "ScriptFalse", c => Bool(false)) ++  
  arule("PrimitiveExpr", "Nil",  c => NilExpr) ++
  arule("PrimitiveExpr", "Apostrophe ValueTerm Apostrophe", c => LogicTerm(c.ValueTerm)) ++
  arule("PrimitiveExpr", "Apostrophe Colon ValueType Apostrophe", c => LogicType(c.ValueType)) ++
  arule("PrimitiveExpr", "QuotationMark_1 StringLiteral QuotationMark_2", c => mkStringLiteral(c, c.span("QuotationMark_1"), c.span("QuotationMark_2"))) ++
  arule("OrExpr", "OrExpr ScriptOr AndExpr", 
      c => BinaryOperation(annotateBinop(Or, c.span("ScriptOr")), c.OrExpr, c.AndExpr)) ++
  arule("OrExpr", "AndExpr", _.AndExpr[Any]) ++
  arule("AndExpr", "AndExpr ScriptAnd NotExpr", 
      c => BinaryOperation(annotateBinop(And, c.span("ScriptAnd")), c.AndExpr, c.NotExpr)) ++
  arule("AndExpr", "NotExpr", _.NotExpr[Any]) ++
  arule("NotExpr", "ScriptNot NotExpr", 
      c => UnaryOperation(annotateUnop(Not, c.span("ScriptNot")), c.NotExpr)) ++
  arule("NotExpr", "CmpExpr", _.CmpExpr[Any]) ++
  arule("CmpExpr", "CmpExpr CmpOp GeneralArithExpr", { c =>
    val operator : CmpOperator = c.CmpOp
    val operand : Expr = c.GeneralArithExpr
    val cmpExpr : Expr = c.CmpExpr
    cmpExpr match {
      case op : CmpOperation =>
        CmpOperation(op.operators :+ operator, op.operands :+ operand)
      case e =>
        CmpOperation(Vector(operator), Vector(e, operand))
    }
  }) ++
  arule("CmpExpr", "GeneralArithExpr", _.GeneralArithExpr[Any]) ++
  arule("CmpOp", "Le", c => Le) ++
  arule("CmpOp", "Gr", c => Gr) ++
  arule("CmpOp", "Leq", c => Leq) ++
  arule("CmpOp", "Geq", c => Geq) ++
  arule("CmpOp", "ScriptEq", c => Eq) ++
  arule("CmpOp", "ScriptNotEq", c => NEq) ++
  arule("GeneralArithExpr", "ConcatExpr", _.ConcatExpr[Any]) ++
  arule("ConcatExpr", "ConcatExpr MinusMinus ArithExpr", c => BinaryOperation(annotateBinop(Minus, c.span("MinusMinus")), c.ConcatExpr, c.ArithExpr)) ++
  arule("ConcatExpr", "PrependConcatExpr", _.PrependConcatExpr[Any]) ++
  arule("ConcatExpr", "ConcatExpr Append ArithExpr", c => BinaryOperation(annotateBinop(Append, c.span("Append")), c.ConcatExpr, c.ArithExpr)) ++
  arule("PrependConcatExpr", "PrependExpr", _.PrependExpr[Any]) ++ 
  arule("PrependConcatExpr", "PrependConcatExpr Concat ArithExpr", c => BinaryOperation(annotateBinop(Concat, c.span("Concat")), c.PrependConcatExpr, c.ArithExpr)) ++
  arule("PrependExpr", "ArithExpr Prepend PrependExpr", c => BinaryOperation(annotateBinop(Prepend, c.span("Prepend")), c.ArithExpr, c.PrependExpr)) ++
  arule("PrependExpr", "ArithExpr", _.ArithExpr[Any]) ++
  arule("ArithExpr", "RangeExpr", _.RangeExpr[Any]) ++
  arule("RangeExpr", "AddExpr", _.AddExpr[Any]) ++
  arule("RangeExpr", "AddExpr_1 To AddExpr_2", 
    c => BinaryOperation(annotateBinop(RangeTo, c.span("To")), c.AddExpr_1, c.AddExpr_2)) ++
  arule("RangeExpr", "AddExpr_1 Downto AddExpr_2", 
    c => BinaryOperation(annotateBinop(RangeDownto, c.span("Downto")), c.AddExpr_1, c.AddExpr_2)) ++
  arule("AddExpr", "AddExpr Plus NegExpr", 
      c => BinaryOperation(annotateBinop(Add, c.span("Plus")), c.AddExpr, c.NegExpr)) ++
  arule("AddExpr", "AddExpr Minus NegExpr", 
      c => BinaryOperation(annotateBinop(Sub, c.span("Minus")), c.AddExpr, c.NegExpr)) ++  
  arule("AddExpr", "NegExpr", _.NegExpr[Any]) ++
  arule("NegExpr", "Minus NegExpr", 
      c => UnaryOperation(annotateUnop(Neg, c.span("Minus")), c.NegExpr)) ++  
  arule("NegExpr", "MultExpr", _.MultExpr[Any]) ++  
  arule("MultExpr", "MultExpr Times BasicExpr", 
      c => BinaryOperation(annotateBinop(Mul, c.span("Times")), c.MultExpr, c.BasicExpr)) ++
  arule("MultExpr", "MultExpr Slash BasicExpr", 
      c => BinaryOperation(annotateBinop(Div, c.span("Slash")), c.MultExpr, c.BasicExpr)) ++
  arule("MultExpr", "MultExpr Mod BasicExpr", 
      c => BinaryOperation(annotateBinop(Mod, c.span("Mod")), c.MultExpr, c.BasicExpr)) ++
  arule("MultExpr", "BasicExpr", _.BasicExpr[Any]) ++
  arule("BasicExpr", "AppExpr", _.AppExpr[Any]) ++
  arule("AppExpr", "DestructExpr", _.DestructExpr[Any]) ++
  arule("AppExpr", "AppExpr DestructExpr", c => App(c.AppExpr, c.DestructExpr)) ++
  arule("DestructExpr", "PrimitiveExpr", _.PrimitiveExpr[Any]) ++
  arule("DestructExpr", "ExclamationMark DestructExpr", 
    c => UnaryOperation(annotateUnop(Destruct, c.span("ExclamationMark")), c.DestructExpr)) ++
  arule("LazyExpr", "OrExpr", _.OrExpr[Any]) ++
  arule("LazyExpr", "Lazy LazyExpr", c => Lazy(c.LazyExpr)) ++ 
  arule("FunExpr", "Pattern DoubleArrow Block", c => Fun(c.Pattern, c.Block)) ++
  arule("TypedExpr", "LazyExpr Colon ScriptValueType", c => TypeCast(c.LazyExpr, c.ScriptValueType)) ++
  arule("TypedExpr", "LazyExpr", _.LazyExpr[Any]) ++
  arule("FunExpr", "TypedExpr", _.TypedExpr[Any]) ++
  arule("Expr", "FunExpr", _.FunExpr[Any]) ++
  arule("ExprList", "", c => Vector[Expr]()) ++
  arule("ExprList", "ExprList1", _.ExprList1[Any]) ++
  arule("ExprList1", "PExpr", c => Vector[Expr](c.PExpr)) ++
  arule("ExprList1", "Comma PExpr", c => Vector[Expr](NilExpr, c.PExpr)) ++
  arule("ExprList1", "Comma", c => Vector[Expr](NilExpr, NilExpr)) ++
  arule("ExprList1", "ExprList1 Comma PExpr", c => c.ExprList1[Vector[Expr]] :+ c.PExpr) ++
  arule("ExprList1", "ExprList1 Comma", c => c.ExprList1[Vector[Expr]] :+ NilExpr) ++
  arule("ExprSetList1", "PExpr", c => Vector[Expr](c.PExpr)) ++
  arule("ExprSetList1", "ExprSetList1 Comma PExpr", c => c.ExprSetList1[Vector[Expr]] :+ c.PExpr) ++
  arule("ExprMapList1", "PExpr_1 SingleArrow PExpr_2", c => Vector[(Expr, Expr)]((c.PExpr_1, c.PExpr_2))) ++
  arule("ExprMapList1", "ExprMapList1 Comma PExpr_1 SingleArrow PExpr_2", c => c.ExprMapList1[Vector[(Expr, Expr)]] :+ (c.PExpr_1, c.PExpr_2)) ++
  arule("PExpr", "Expr", _.Expr[Expr]) ++
  arule("PExpr", "ControlFlowExpr", c => ControlFlowExpr(c.ControlFlowExpr)) 
  
val g_do = 
  arule("STDo", "Do Block",
      CS.Indent("Do", "Block"),
      c => Do(c.Block, false)) ++
  arule("DoExpr", "Do Block",
      c => Do(c.Block, false)) ++
  arule("STDo", "Do Times Block",
      CS.and(CS.Indent("Do", "Times"), CS.Indent("Do", "Block")),
      c => Do(c.Block, true)) ++
  arule("DoExpr", "Do Times Block",
      c => Do(c.Block, true))
  
val g_if =
  arule("STIf", "If PExpr Then Block_1 Else Block_2", 
      CS.and(
          CS.Indent("If", "PExpr"), 
          CS.ifThenElse(CS.Line("If", "Then"), 
              CS.and(
                  CS.Indent("If", "Block_1"),
                  Subalign("If", "Else")),
              CS.and(
                  Subalign("If", "Then"),
                  CS.Indent("Then", "Block_1"),
                  CS.or(CS.Line("Then", "Else"), CS.Align("Then", "Else")))), 
          CS.ifThenElse(CS.Line("If", "Else"), 
              CS.Indent("If", "Block_2"),
              CS.ifThenElse(CS.Line("Then", "Else"), 
                CS.Indent("Then", "Block_2"),
                CS.Indent("Else", "Block_2")))),
      c => If(c.PExpr, c.Block_1, c.Block_2)) ++
  arule("STIf", "If PExpr Then Block",
      CS.and(
          CS.Indent("If", "PExpr"), 
          CS.ifThenElse(CS.Line("If", "Then"), 
              CS.Indent("If", "Block"), 
              CS.and(
                  Subalign("If", "Then"),
                  CS.Indent("Then", "Block")))),
      c => If(c.PExpr, c.Block, Block(Vector()))) ++
  arule("IfExpr", "If PExpr Then Block_1 Else Block_2", 
      c => If(c.PExpr, c.Block_1, c.Block_2)) ++
  arule("IfExpr", "If PExpr Then Block",
      c => If(c.PExpr, c.Block, Block(Vector())))
    
val g_while = 
  arule("STWhile", "While PExpr Do Block",
      CS.and(
        CS.Indent("While", "PExpr"),
        CS.ifThenElse(CS.Line("While", "Do"),
            CS.Indent("While", "Block"),
            CS.and(Subalign("While", "Do"), CS.Indent("Do", "Block")))),
      c => While(c.PExpr, c.Block)) ++
  arule("WhileExpr", "While PExpr Do Block",
      c => While(c.PExpr, c.Block))
      
val g_for = 
  arule("STFor", "For Pattern In PExpr Do Block",
      CS.and(
          CS.Indent("For", "Pattern"),
          CS.Indent("For", "In"),
          CS.Indent("For", "PExpr"),
          CS.ifThenElse(CS.Line("For", "Do"),
              CS.Indent("For", "Block"),
              CS.and(Subalign("For", "Do"), CS.Indent("Do", "Block")))),              
      c => For(c.Pattern, c.PExpr, c.Block)) ++
  arule("ForExpr", "For Pattern In PExpr Do Block",
      c => For(c.Pattern, c.PExpr, c.Block))

val g_timeit = 
  arule("STTimeit", "Timeit Block",
      CS.Indent("Timeit", "Block"),
      c => Timeit(c.Block)) ++
  arule("TimeitExpr", "Timeit Block",
      c => Timeit(c.Block))

val g_match = 
  arule("STMatch", "Match PExpr STMatchCases",
      CS.and(
          CS.Indent("Match", "PExpr"),
          Subalign("Match", "STMatchCases")),
      c => Match(c.PExpr, c.STMatchCases)) ++
  arule("STMatchCases", "STMatchCases_0 STMatchCase", 
      CS.or(CS.Align("STMatchCases_0", "STMatchCase"), CS.Line("STMatchCases_0", "STMatchCase")),
      c => c.STMatchCases_0[Vector[MatchCase]] :+ c.STMatchCase) ++
  arule("STMatchCases", "", c => Vector[MatchCase]()) ++
  arule("STMatchCase", "Case Pattern DoubleArrow Block", 
      CS.and(
        CS.Indent("Case", "Pattern"),
        CS.SameLine("Pattern", "DoubleArrow"),
        CS.Indent("Case", "Block")),
      c => MatchCase(c.Pattern, c.Block)) ++     
  arule("MatchExpr", "Match PExpr MatchCases",
      c => Match(c.PExpr, c.MatchCases)) ++
  arule("MatchCases", "MatchCases MatchCase", 
      c => c.MatchCases[Vector[MatchCase]] :+ c.MatchCase) ++
  arule("MatchCases", "", c => Vector[MatchCase]()) ++
  arule("MatchCase", "Case Pattern DoubleArrow Block", 
      c => MatchCase(c.Pattern, c.Block))    

val g_context =
  arule("STContext", "Context OptContextParam Block",
      CS.and(
        CS.Indent("Context", "OptContextParam"),
        CS.Indent("Context", "Block")),
      c => ContextControl(c.OptContextParam, c.Block)) ++
  arule("ContextExpr", "Context OptContextParam Block",
      c => ContextControl(c.OptContextParam, c.Block)) ++
  arule("OptContextParam", "", c => None) ++
  arule("OptContextParam", "Le PExpr Gr", c => Some(c.PExpr[Any]))
      
val g_controlflow = 
  g_do ++ g_if ++ g_while ++ g_for ++ g_match ++ g_context ++ g_timeit ++
  arule("STControlFlow", "STDo", _.STDo[Any]) ++  
  arule("STControlFlow", "STIf", _.STIf[Any]) ++
  arule("STControlFlow", "STWhile", _.STWhile[Any]) ++
  arule("STControlFlow", "STFor", _.STFor[Any]) ++
  arule("STControlFlow", "STMatch", _.STMatch[Any]) ++
  arule("STControlFlow", "STContext", _.STContext[Any]) ++
  arule("STControlFlow", "STTimeit", _.STTimeit[Any]) ++
  arule("ControlFlowExpr", "DoExpr", _.DoExpr[Any]) ++  
  arule("ControlFlowExpr", "IfExpr", _.IfExpr[Any]) ++
  arule("ControlFlowExpr", "WhileExpr", _.WhileExpr[Any]) ++
  arule("ControlFlowExpr", "ForExpr", _.ForExpr[Any]) ++
  arule("ControlFlowExpr", "MatchExpr", _.MatchExpr[Any]) ++
  arule("ControlFlowExpr", "ContextExpr", _.ContextExpr[Any]) ++
  arule("ControlFlowExpr", "TimeitExpr", _.TimeitExpr[Any])

val g_pattern = 
  arule("AtomicPattern", "Underscore", c => PAny) ++
  arule("AtomicPattern", "Nil", c => PNil) ++
  arule("AtomicPattern", "Name", c => mkNamePattern(c.text("Name"), None)) ++  
  arule("AtomicPattern", "Int", c => PInt(c.Int[Integer].value)) ++
  arule("AtomicPattern", "QuotationMark_1 StringLiteral QuotationMark_2", 
    c => PString(mkStringLiteral(c, c.span("QuotationMark_1"), c.span("QuotationMark_2")).value)) ++
  arule("AtomicPattern", "ScriptTrue", c => PBool(true)) ++
  arule("AtomicPattern", "ScriptFalse", c => PBool(false)) ++
  arule("AtomicPattern", "Apostrophe PatternTerm Apostrophe", c => PLogicTerm(c.PatternTerm)) ++
  arule("AtomicPattern", "Apostrophe Colon PatternType Apostrophe", c => PLogicType(c.PatternType)) ++
  arule("AtomicPattern", "RoundBracketOpen PatternList RoundBracketClose", c => mkTuplePattern(c.PatternList, true)) ++
  arule("AtomicPattern", "SquareBracketOpen PatternList SquareBracketClose", c => mkTuplePattern(c.PatternList, false)) ++  
  arule("ConstrPattern", "AtomicPattern", _.AtomicPattern[Any]) ++
  arule("ConstrPattern", "Name AtomicPattern", c => mkNamePattern(c.text("Name"), Some(c.AtomicPattern))) ++
  arule("PrependPattern", "ConstrPattern Prepend PrependPattern", c => PPrepend(c.ConstrPattern, c.PrependPattern)) ++
  arule("PrependPattern", "AppendPattern", _.AppendPattern[Any]) ++
  arule("AppendPattern", "AppendPattern Append ConstrPattern", c => PAppend(c.AppendPattern, c.ConstrPattern)) ++
  arule("AppendPattern", "ConstrPattern", _.ConstrPattern[Any]) ++
  arule("ScriptValuePrimitiveType", "Underscore", c => TyAny) ++
  arule("ScriptValuePrimitiveType", "TyNil", c => TyNil) ++
  arule("ScriptValuePrimitiveType", "TyContext", c => TyContext) ++
  arule("ScriptValuePrimitiveType", "TyTheorem", c => TyTheorem) ++
  arule("ScriptValuePrimitiveType", "TyTerm", c => TyTerm) ++
  arule("ScriptValuePrimitiveType", "TyType", c => TyType) ++
  arule("ScriptValuePrimitiveType", "TyBoolean", c => TyBoolean) ++
  arule("ScriptValuePrimitiveType", "TyInteger", c => TyInteger) ++
  arule("ScriptValuePrimitiveType", "TyString", c => TyString) ++
  arule("ScriptValuePrimitiveType", "TyTuple", c => TyTuple) ++
  arule("ScriptValuePrimitiveType", "TyMap", c => TyMap) ++
  arule("ScriptValuePrimitiveType", "TySet", c => TySet) ++
  arule("ScriptValuePrimitiveType", "TyFunction", c => TyFunction) ++
  arule("ScriptValuePrimitiveType", "Name", c => mkTyCustom(c.text("Name"))) ++
  arule("ScriptValueType", "ScriptValuePrimitiveType", c => c.ScriptValuePrimitiveType[Any]) ++
  arule("ScriptValueType", "ScriptValueType Bar ScriptValuePrimitiveType", c => TyUnion(c.ScriptValueType, c.ScriptValuePrimitiveType)) ++
  arule("ScriptValueType", "ScriptValuePrimitiveType QuestionMark", c => TyOption(c.ScriptValuePrimitiveType)) ++
  arule("AsPattern", "PrependPattern", _.PrependPattern[Any]) ++
  arule("AsPattern", "Pattern As IndexedName", c => PAs(c.Pattern, c.text("IndexedName"))) ++
  arule("IfPattern", "AsPattern", _.AsPattern[Any]) ++
  arule("IfPattern", "Pattern If Expr", c => PIf(c.Pattern, c.Expr)) ++
  arule("ArgumentPattern", "IfPattern", _.IfPattern[Any]) ++
  arule("TypePattern", "ArgumentPattern", _.ArgumentPattern[Any]) ++
  arule("TypePattern", "TypePattern Colon ScriptValueType", c => PType(c.TypePattern, c.ScriptValueType)) ++
  arule("Pattern", "TypePattern", _.TypePattern[Any]) ++
  arule("OptPattern", "", c => None) ++
  arule("OptPattern", "Pattern", c => Some(c.Pattern[Any])) ++
  arule("PatternList", "", c => Vector[Pattern]()) ++
  arule("PatternList", "PatternList1", _.PatternList1[Any]) ++
  arule("PatternList1", "Comma Pattern", c => Vector[Pattern](PNil, c.Pattern)) ++
  arule("PatternList1", "Comma", c => Vector[Pattern](PNil, PNil)) ++  
  arule("PatternList1", "Pattern", c => Vector[Pattern](c.Pattern)) ++
  arule("PatternList1", "PatternList1 Comma Pattern", c => c.PatternList1[Vector[Pattern]] :+ c.Pattern) ++
  arule("PatternList1", "PatternList1 Comma", c => c.PatternList1[Vector[Pattern]] :+ PNil)

val g_comment =
  arule("Comment", "CommentText", c => Comment(c.text("CommentText"))) ++
  arule("CommentText", "Hash", c => null) ++
  arule("CommentText", "CommentText_0 AnyToken", CS.Indent("CommentText_0", "AnyToken"), c => null) ++
  arule("ST", "Comment", c => STComment(c.Comment))

val g_show =
  arule("ST", "Show PExpr",
    CS.Indent("Show", "PExpr"),
    c => STShow(c.PExpr))

val g_fail =
  arule("ST", "Fail",
    c => STFail(None)) ++
  arule("ST", "Fail PExpr",
    CS.Indent("Fail", "PExpr"),
    c => STFail(Some(c.PExpr[Expr])))

val g_val = 
  arule("ST", "Val Pattern Eq Block",
    CS.and(
      CS.Indent("Val", "Pattern"),
      CS.SameLine("Pattern", "Eq"),
      CS.or(CS.Line("Eq", "Block"), CS.Indent("Val", "Block"))),
    c => STVal(c.Pattern, c.Block)) ++
  arule("ST", "Val IdList", 
    CS.Indent("Val", "IdList"),
    c => STValIntro(c.IdList)) ++
  arule("IdList", "IndexedName", c => List[Id](Id(c.text("IndexedName")))) ++
  arule("IdList", "IdList IndexedName", c => c.IdList[List[Id]] :+ Id(c.text("IndexedName")))

val g_assign = 
  arule("ST", "Pattern Eq Block",
      CS.and(
          CS.SameLine("Pattern", "Eq"),
          CS.Protrude("Pattern"),
          CS.or(CS.Line("Eq", "Block"), CS.Indent("Pattern", "Block"))),
      c => STAssign(c.Pattern, c.Block))
  
def mkSTDef(cases : Vector[DefCase], memoize : Boolean, contextParam : Option[Expr]) : STDef = {
  var result : Map[String, Vector[DefCase]] = Map()
  for (c <- cases) {
    result.get(c.name) match {
      case None => result = result + (c.name -> Vector(c))
      case Some(cs) => result = result + (c.name -> (cs :+ c))
    }
  }
  STDef(result, memoize, contextParam)
}

val g_def =
  arule("ST", "Def OptContextParam DefCases",
      CS.and(
        CS.Indent("Def", "OptContextParam"),
        CS.Indent("Def", "DefCases")),
      c => mkSTDef(c.DefCases, false, c.OptContextParam)) ++
  arule("ST", "Def OptContextParam IndexedName ArgumentPattern DefType Eq Block", 
      CS.and(
        CS.SameLine("Def", "IndexedName"),
        CS.Indent("Def", "OptContextParam"),
        CS.Indent("Def", "ArgumentPattern"),
        CS.Indent("Def", "DefType"),
        CS.Indent("Def", "Eq"),
        CS.Indent("Def", "Block"), 
        CS.not(CS.NullSpan("Block")),
        CS.not(CS.SameLine("Def", "Block"))),
      c => mkSTDef(Vector(DefCase(c.text("IndexedName"), c.ArgumentPattern, c.DefType, c.Block)), false, c.OptContextParam)) ++
  arule("ST", "Table OptContextParam DefCases",
      CS.and(
        CS.Indent("Table", "OptContextParam"),
        CS.Indent("Table", "DefCases")),
      c => mkSTDef(c.DefCases, true, c.OptContextParam)) ++
  arule("ST", "Table OptContextParam IndexedName ArgumentPattern DefType Eq Block", 
      CS.and(
        CS.SameLine("Table", "IndexedName"),
        CS.Indent("Table", "OptContextParam"),
        CS.Indent("Table", "ArgumentPattern"),
        CS.Indent("Table", "DefType"),
        CS.Indent("Table", "Eq"),
        CS.Indent("Table", "Block"), 
        CS.not(CS.NullSpan("Block")),
        CS.not(CS.SameLine("Table", "Block"))),
      c => mkSTDef(Vector(DefCase(c.text("IndexedName"), c.ArgumentPattern, c.DefType, c.Block)), true, c.OptContextParam)) ++
  arule("DefCases", "", c => Vector[DefCase]()) ++
  arule("DefCases", "DefCases_0 DefCase", 
      CS.Align("DefCases_0", "DefCase"),
      c => c.DefCases_0[Vector[DefCase]] :+ c.DefCase) ++
  arule("DefCase", "IndexedName ArgumentPattern DefType Eq Block",
      CS.and(
          CS.Indent("IndexedName", "ArgumentPattern"),
          CS.Indent("IndexedName", "DefType"),
          CS.Indent("IndexedName", "Eq"),
          CS.Indent("IndexedName", "Block")),
      c => DefCase(c.text("IndexedName"), c.ArgumentPattern, c.DefType, c.Block)) ++
  arule("DefType", "", c => None) ++
  arule("DefType", "Colon ScriptValueType", c => Some(c.ScriptValueType[Any]))

val g_datatype =
  arule("ST", "Datatype DatatypeCases", 
    CS.Indent("Datatype", "DatatypeCases"),
    c => STDatatype(c.DatatypeCases)) ++
  arule("ST", "Datatype IndexedName DatatypeConstrs",
    CS.and(
      CS.SameLine("Datatype", "IndexedName"),
      CS.Indent("Datatype", "DatatypeConstrs")),
    c => STDatatype(Vector(DatatypeCase(c.text("IndexedName"), c.DatatypeConstrs)))) ++
  arule("DatatypeConstrs", "", c => Vector()) ++
  arule("DatatypeConstrs", "DatatypeConstrs_0 DatatypeConstr",
    CS.Align("DatatypeConstrs_0", "DatatypeConstr"),
    c => c.DatatypeConstrs_0[Vector[DatatypeConstr]] :+ c.DatatypeConstr[DatatypeConstr]) ++
  arule("DatatypeConstr", "IndexedName", 
    c => DatatypeConstr(c.text("IndexedName"), None)) ++
  arule("DatatypeConstr", "IndexedName Pattern", CS.Indent("IndexedName", "Pattern"),
    c => DatatypeConstr(c.text("IndexedName"), Some(c.Pattern))) ++
  arule("DatatypeCases", "", c => Vector()) ++
  arule("DatatypeCases", "DatatypeCases_0 DatatypeCase", 
    CS.Align("DatatypeCases_0", "DatatypeCase"),
    c => c.DatatypeCases_0[Vector[DatatypeCase]] :+ c.DatatypeCase[DatatypeCase]) ++
  arule("DatatypeCase", "IndexedName DatatypeConstrs",
    CS.Indent("IndexedName", "DatatypeConstrs"),
    c => DatatypeCase(c.text("IndexedName"), c.DatatypeConstrs))
      
val g_return =
  arule("ST", "Return PExpr", CS.Indent("Return", "PExpr"), 
    c => STReturn(Some(c.PExpr[Expr]))) ++
  arule("ST", "Return", c => STReturn(None))
    
val g_assume =
  arule("ST", "Assume OptAssign PrimitiveExpr", 
    CS.and(
      CS.Indent("Assume", "OptAssign"),
      CS.Indent("Assume", "PrimitiveExpr")),
    c => STAssume(c.OptAssign, c.PrimitiveExpr))

val g_let = 
  arule("ST", "Let OptAssign PrimitiveExpr",
    CS.and(
      CS.Indent("Let", "OptAssign"),
      CS.Indent("Let", "PrimitiveExpr")),
    c => STLet(c.OptAssign, c.PrimitiveExpr))

val g_choose = 
  arule("ST", "Choose OptAssign PrimitiveExpr Block",
    CS.and(
      CS.Indent("Choose", "OptAssign"),
      CS.Indent("Choose", "PrimitiveExpr"),
      CS.Indent("Choose", "Block")),
    c => STChoose(c.OptAssign, 
                  c.PrimitiveExpr,
                  c.Block)) 

val g_theorem = 
  arule("TheoremOptAssign", "Theorem OptAssign", CS.Indent("Theorem", "OptAssign"), c => c.OptAssign[Any]) ++
  arule("ST", "TheoremOptAssign PrimitiveExpr Block",
    CS.and(
      CS.Indent("TheoremOptAssign", "PrimitiveExpr"),
      CS.Indent("TheoremOptAssign", "Block")),
    c => STTheorem(c.TheoremOptAssign,
                   c.PrimitiveExpr,
                   c.Block)) ++
  arule("ST", "TheoremOptAssign Block",
    CS.and(
      CS.Indent("TheoremOptAssign", "Block"),
      CS.not(CS.SameLine("TheoremOptAssign", "Block"))),
    c => STTheorem(c.TheoremOptAssign,
                   ParseTree.NilExpr,
                   c.Block)) ++
  arule("ST", "TheoremOptAssign PrimitiveExpr By PExpr",
    CS.and(
      CS.Indent("TheoremOptAssign", "PrimitiveExpr"),
      CS.ifThenElse(CS.Line("TheoremOptAssign", "By"),
        CS.Indent("TheoremOptAssign", "PExpr"),
        CS.and(Subalign("TheoremOptAssign", "By"), CS.Indent("By", "PExpr")))),
    c => STTheoremBy(c.TheoremOptAssign,
                     c.PrimitiveExpr,
                     c.PExpr)) ++
  arule("ST", "TheoremOptAssign PrimitiveExpr Dot",
    CS.and(
      CS.Indent("TheoremOptAssign", "PrimitiveExpr"),
      CS.SameLine("PrimitiveExpr", "Dot")),
    c => STTheoremBy(c.TheoremOptAssign,
                     c.PrimitiveExpr,
                     ParseTree.NilExpr)) 

val g_logic_statements = 
  arule("OptAssign", "", c => None) ++
  arule("OptAssign", "IndexedName Colon", c => Some(c.text("IndexedName"))) ++
  g_assume ++ g_let ++ g_choose ++ g_theorem

val g_test = 
  arule("ST", "Assert PExpr", CS.Indent("Assert", "PExpr"), c => STAssert(c.PExpr)) ++
  arule("ST", "Failure Block", CS.Indent("Failure", "Block"), c => STFailure(c.Block))

val g_statement = 
  g_val ++ g_assign ++ g_def ++ g_datatype ++ g_return ++ g_show ++ g_fail ++
  g_logic_statements ++ g_comment ++ g_test ++
  arule("Statement", "Expr", 
    CS.or(CS.Protrude("Expr"), CS.not(CS.First("Expr"))),
    c => STExpr(c.Expr)) ++
  arule("Statement", "ST", _.ST[Any]) ++
  arule("Statement", "STControlFlow", c => STControlFlow(c.STControlFlow)) ++ 
  arule("Statements", "", c => Vector[Statement]()) ++
  arule("Statements", "Statements_0 Statement", CS.Align("Statements_0", "Statement"),
      c => c.Statements_0[Vector[Statement]] :+ c.Statement) ++
  arule("Block", "Statements", c => Block(c.Statements)) 

val g_header = 
  arule("ST", "Theory Namespace AliasList Extends NamespaceList", 
    CS.and(
      CS.Indent("Theory", "Namespace"),
      CS.Indent("Theory", "AliasList"),
      CS.ifThenElse(CS.Line("Theory", "Extends"),
        CS.Indent("Theory", "NamespaceList"),
        CS.and(CS.Align("Theory", "Extends"), CS.Indent("Extends", "NamespaceList")))),
    c => STTheory(Namespace(c.text("Namespace")), c.AliasList[List[(Id, Namespace)]].reverse, c.NamespaceList[List[Namespace]].reverse)) ++
  arule("ST", "Theory Namespace AliasList", 
    CS.and(CS.Indent("Theory", "Namespace"), CS.Indent("Theory", "AliasList")),
    c => STTheory(Namespace(c.text("Namespace")), c.AliasList[List[(Id, Namespace)]].reverse, List[Namespace]())) ++
  arule("NamespaceList", "", c => List[Namespace]()) ++
  arule("NamespaceList", "NamespaceList Namespace",
    c => Namespace(c.text("Namespace")) :: c.NamespaceList[List[Namespace]]) ++
  arule("AliasList", "", c => List[(Id, Namespace)]()) ++
  arule("AliasList", "AliasList_0 Alias", 
    CS.Align("AliasList_0", "Alias"),
    c => c.Alias[(Id, Namespace)] :: c.AliasList_0[List[(Id, Namespace)]]) ++
  arule("Alias", "IndexedName Eq Namespace", 
    c => (Id(c.text("IndexedName")), Namespace(c.text("Namespace"))))

val g_prog = 
  Syntax.grammar ++
  g_literals ++
  g_pattern ++
  g_expr ++
  g_statement ++
  g_controlflow ++
  g_header ++
  arule("ValueQuotedType", "PExpr", _.PExpr[Any]) ++
  arule("PatternQuotedType", "Pattern", _.Pattern[Any]) ++
  arule("ValueQuotedTerm", "PExpr", _.PExpr[Any]) ++
  arule("PatternQuotedTerm", "Pattern", _.Pattern[Any]) ++
  arule("Prog", "Block", _.Block[Any])

}