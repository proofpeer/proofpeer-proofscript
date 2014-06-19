package proofpeer.proofscript.frontend

import proofpeer.indent._
import proofpeer.indent.API._
import proofpeer.indent.APIConversions._
import Derivation.Context  
import proofpeer.indent.{Constraints => CS}
import ParseTree._
import proofpeer.proofscript.logic.{Preterm, Syntax, Namespace}

class ProofScriptGrammar(annotate : (Any, Option[Span]) => Any) {
  
def ltokenrule(nonterminal : String, c1 : Char, c2 : Char) : Grammar = 
  tokenrule(nonterminal, Range.interval(c1, c2)) ++ lexical(nonterminal, LexicalPriority(0, None))
  
def ltokenrule(nonterminal : String, c : Char) : Grammar = 
  ltokenrule(nonterminal, c, c)

def ltokenrule(nonterminal : String, i : Int) : Grammar = 
  tokenrule(nonterminal, Range.interval(i, i)) ++ lexical(nonterminal, LexicalPriority(0, None))

def ltokenrule(nonterminal : String, r : Range) : Grammar = 
  tokenrule(nonterminal, r) ++ lexical(nonterminal, LexicalPriority(0, None))


def lexrule(n : Nonterminal, rhs : String) : Grammar = {
  API.lexrule(n, rhs, LexicalPriority(0, None))
}

def litrule(n : Nonterminal, lit : String) : Grammar = {
  API.lexrule(n, literal(lit), LexicalPriority(0, Some(2)))
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

val g_string_literals = 
  ltokenrule("HexDigit", 'a', 'f') ++
  ltokenrule("HexDigit", 'A', 'F') ++
  ltokenrule("HexDigit", '0', '9') ++
  ltokenrule("QuotationMark", '"') ++
  ltokenrule("LowerU", 'u') ++
  ltokenrule("UpperU", 'U') ++
  ltokenrule("StringCharacter", 
    Range.add(
      Range.singleton(0x21), 
      Range.interval(0x23, 0x5B),
      Range.interval(0x5D, 0x7E),
      Range.interval(0xA0, Int.MaxValue))) ++
  lexrule("StringCharacter", literal("\\n")) ++
  lexrule("StringCharacter", literal("\\\\")) ++ 
  lexrule("StringCharacter", literal("\\\"")) ++ 
  lexrule("StringCharacter", "Backslash LowerU HexDigit_1 HexDigit_2 HexDigit_3 HexDigit_4") ++
  lexrule("StringCharacter", "Backslash UpperU HexDigit_1 HexDigit_2 HexDigit_3 HexDigit_4 HexDigit_5 HexDigit_6 HexDigit_7 HexDigit_8") ++
  lexrule("StringLiteral", "") ++
  rule("StringLiteral", "StringLiteral StringCharacter") 

val g_literals =
  g_string_literals ++
  ltokenrule("Plus", '+') ++  
  ltokenrule("Minus", '-') ++
  ltokenrule("Times", '*') ++
  ltokenrule("Slash", '/') ++
  ltokenrule("Le", '<') ++
  ltokenrule("Gr", '>') ++
  ltokenrule("Leq", 0x2264) ++
  lexrule("Leq", literal("<=")) ++
  ltokenrule("Geq", 0x2265) ++
  lexrule("Geq", literal(">=")) ++
  ltokenrule("SquareBracketOpen", '[') ++
  ltokenrule("SquareBracketClose", ']') ++
  ltokenrule("DoubleArrow", 0x21D2) ++
  lexrule("DoubleArrow", literal("=>")) ++
  lexrule("ScriptEq", literal("==")) ++
  lexrule("ScriptNotEq", literal("<>")) ++ 
  ltokenrule("ScriptNotEq", 0x2260) ++
  ltokenrule("Apostrophe", 0x27) ++
  lexrule("Prepend", literal("<+")) ++
  lexrule("Append", literal("+>")) ++
  lexrule("Concat", literal("++")) ++
  litrule("Val", "val") ++
  litrule("Def", "def") ++
  litrule("Mod", "mod") ++
  litrule("ScriptOr", "or") ++
  litrule("ScriptAnd", "and") ++
  litrule("ScriptNot", "not") ++
  litrule("ScriptTrue", "true") ++
  litrule("ScriptFalse", "false") ++
  litrule("Lazy", "lazy") ++
  litrule("If", "if") ++
  litrule("Then", "then") ++
  litrule("Else", "else") ++
  litrule("While", "while") ++
  litrule("Do", "do") ++
  litrule("For", "for") ++
  litrule("In", "in") ++
  litrule("Match", "match") ++
  litrule("Case", "case") ++
  litrule("Return", "return") ++
  litrule("Assume", "assume") ++
  litrule("Let", "let") ++
  litrule("Choose", "choose") ++
  litrule("From", "from") ++
  litrule("Theory", "theory") ++
  litrule("Extends", "extends") ++
  litrule("Context", "context") ++
  litrule("Show", "show") ++
  litrule("Fail", "fail") ++
  litrule("Nil", "nil") ++
  litrule("To", "to") ++
  litrule("Downto", "downto") ++
  litrule("Theorem", "theorem")

def arule(n : Nonterminal, rhs : String, constraints : Constraints.Constraint[IndexedSymbol],
          action : Derivation.Context => Any) : Grammar = 
{
  def annotatedAction(c : Derivation.Context) : Any = {     
    annotate(action(c), c._span)
  }
  rule(n, rhs, constraints, annotatedAction)
}

def annotateUnop(b : UnaryOperator, span : Option[Span]) : UnaryOperator = 
  annotate(b, span).asInstanceOf[UnaryOperator]

def annotateBinop(b : BinaryOperator, span : Option[Span]) : BinaryOperator = 
  annotate(b, span).asInstanceOf[BinaryOperator]

def arule(n : Nonterminal, rhs : String, action : Derivation.Context => Any) : Grammar = 
  arule(n, rhs, Constraints.Unconstrained[IndexedSymbol], action)

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

def mkStringLiteral(escapedCodes : Vector[Int]) : StringLiteral = {
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
  arule("PrimitiveExpr", "Name", c => mkId(Syntax.parseName(c.Name.text))) ++
  arule("Int", "Digits", c => Integer(BigInt(c.Digits.text, 10))) ++
  arule("Int", "Minus Digits", c => Integer(-BigInt(c.Digits.text, 10))) ++  
  arule("PrimitiveExpr", "Digits", c => Integer(BigInt(c.Digits.text, 10))) ++
  arule("PrimitiveExpr", "RoundBracketOpen ExprList RoundBracketClose", c => mkTuple(c.ExprList.resultAs[Vector[Expr]], true)) ++
  arule("PrimitiveExpr", "SquareBracketOpen ExprList SquareBracketClose", c => mkTuple(c.ExprList.resultAs[Vector[Expr]], false)) ++
  arule("PrimitiveExpr", "ScriptTrue", c => Bool(true)) ++  
  arule("PrimitiveExpr", "ScriptFalse", c => Bool(false)) ++  
  arule("PrimitiveExpr", "Nil",  c => NilExpr) ++
  arule("PrimitiveExpr", "Apostrophe ValueTerm Apostrophe", c => LogicTerm(c.ValueTerm.resultAs[Preterm])) ++
  arule("PrimitiveExpr", "QuotationMark StringLiteral QuotationMark", c => mkStringLiteral(c.StringLiteral.codes)) ++
  arule("OrExpr", "OrExpr ScriptOr AndExpr", 
      c => BinaryOperation(annotateBinop(Or, c.ScriptOr.span), c.OrExpr.resultAs[Expr], c.AndExpr.resultAs[Expr])) ++
  arule("OrExpr", "AndExpr", _.AndExpr.result) ++
  arule("AndExpr", "AndExpr ScriptAnd NotExpr", 
      c => BinaryOperation(annotateBinop(And, c.ScriptAnd.span), c.AndExpr.resultAs[Expr], c.NotExpr.resultAs[Expr])) ++
  arule("AndExpr", "NotExpr", _.NotExpr.result) ++
  arule("NotExpr", "ScriptNot NotExpr", 
      c => UnaryOperation(annotateUnop(Not, c.ScriptNot.span), c.NotExpr.resultAs[Expr])) ++
  arule("NotExpr", "CmpExpr", _.CmpExpr.result) ++
  arule("CmpExpr", "CmpExpr CmpOp GeneralArithExpr", { c =>
    val operator = c.CmpOp.resultAs[CmpOperator]
    val operand = c.GeneralArithExpr.resultAs[Expr]
    c.CmpExpr.resultAs[Expr] match {
      case op : CmpOperation =>
        CmpOperation(op.operators :+ operator, op.operands :+ operand)
      case e =>
        CmpOperation(Vector(operator), Vector(e, operand))
    }
  }) ++
  arule("CmpExpr", "GeneralArithExpr", _.GeneralArithExpr.result) ++
  arule("CmpOp", "Le", c => Le) ++
  arule("CmpOp", "Gr", c => Gr) ++
  arule("CmpOp", "Leq", c => Leq) ++
  arule("CmpOp", "Geq", c => Geq) ++
  arule("CmpOp", "ScriptEq", c => Eq) ++
  arule("CmpOp", "ScriptNotEq", c => NEq) ++
  arule("GeneralArithExpr", "ConcatExpr", _.ConcatExpr.result) ++
  arule("ConcatExpr", "PrependConcatExpr", _.PrependConcatExpr.result) ++
  arule("ConcatExpr", "ConcatExpr Append ArithExpr", c => BinaryOperation(annotateBinop(Append, c.Append.span), c.ConcatExpr.resultAs[Expr], c.ArithExpr.resultAs[Expr])) ++
  arule("PrependConcatExpr", "PrependExpr", _.PrependExpr.result) ++ 
  arule("PrependConcatExpr", "PrependConcatExpr Concat ArithExpr", c => BinaryOperation(annotateBinop(Concat, c.Concat.span), c.PrependConcatExpr.resultAs[Expr], c.ArithExpr.resultAs[Expr])) ++
  arule("PrependExpr", "ArithExpr Prepend PrependExpr", c => BinaryOperation(annotateBinop(Prepend, c.Prepend.span), c.ArithExpr.resultAs[Expr], c.PrependExpr.resultAs[Expr])) ++
  arule("PrependExpr", "ArithExpr", _.ArithExpr.result) ++
  arule("ArithExpr", "RangeExpr", _.RangeExpr.result) ++
  arule("RangeExpr", "AddExpr", _.AddExpr.result) ++
  arule("RangeExpr", "AddExpr_1 To AddExpr_2", 
    c => BinaryOperation(annotateBinop(RangeTo, c.To.span), c.AddExpr_1.resultAs[Expr], c.AddExpr_2.resultAs[Expr])) ++
  arule("RangeExpr", "AddExpr_1 Downto AddExpr_2", 
    c => BinaryOperation(annotateBinop(RangeDownto, c.Downto.span), c.AddExpr_1.resultAs[Expr], c.AddExpr_2.resultAs[Expr])) ++
  arule("AddExpr", "AddExpr Plus NegExpr", 
      c => BinaryOperation(annotateBinop(Add, c.Plus.span), c.AddExpr.resultAs[Expr], c.NegExpr.resultAs[Expr])) ++
  arule("AddExpr", "AddExpr Minus NegExpr", 
      c => BinaryOperation(annotateBinop(Sub, c.Minus.span), c.AddExpr.resultAs[Expr], c.NegExpr.resultAs[Expr])) ++  
  arule("AddExpr", "NegExpr", _.NegExpr.result) ++
  arule("NegExpr", "Minus NegExpr", 
      c => UnaryOperation(annotateUnop(Neg, c.Minus.span), c.NegExpr.resultAs[Expr])) ++  
  arule("NegExpr", "MultExpr", _.MultExpr.result) ++  
  arule("MultExpr", "MultExpr Times BasicExpr", 
      c => BinaryOperation(annotateBinop(Mul, c.Times.span), c.MultExpr.resultAs[Expr], c.BasicExpr.resultAs[Expr])) ++
  arule("MultExpr", "MultExpr Slash BasicExpr", 
      c => BinaryOperation(annotateBinop(Div, c.Slash.span), c.MultExpr.resultAs[Expr], c.BasicExpr.resultAs[Expr])) ++
  arule("MultExpr", "MultExpr Mod BasicExpr", 
      c => BinaryOperation(annotateBinop(Mod, c.Mod.span), c.MultExpr.resultAs[Expr], c.BasicExpr.resultAs[Expr])) ++
  arule("MultExpr", "BasicExpr", _.BasicExpr.result) ++
  arule("BasicExpr", "AppExpr", _.AppExpr.result) ++
  arule("AppExpr", "PrimitiveExpr", _.PrimitiveExpr.result) ++
  arule("AppExpr", "AppExpr PrimitiveExpr", c => App(c.AppExpr.resultAs[Expr], c.PrimitiveExpr.resultAs[Expr])) ++
  arule("LazyExpr", "OrExpr", _.OrExpr.result) ++
  arule("LazyExpr", "Lazy LazyExpr", c => Lazy(c.LazyExpr.resultAs[Expr])) ++ 
  arule("FunExpr", "Pattern DoubleArrow Block", c => Fun(c.Pattern.resultAs[Pattern], c.Block.resultAs[Block])) ++
  arule("FunExpr", "LazyExpr", _.LazyExpr.result) ++
  arule("Expr", "FunExpr", _.FunExpr.result) ++
  arule("ExprList", "", c => Vector[Expr]()) ++
  arule("ExprList", "ExprList1", _.ExprList1.result) ++
  arule("ExprList1", "PExpr", c => Vector[Expr](c.PExpr.resultAs[Expr])) ++
  arule("ExprList1", "Comma PExpr", c => Vector[Expr](NilExpr, c.PExpr.resultAs[Expr])) ++
  arule("ExprList1", "Comma", c => Vector[Expr](NilExpr, NilExpr)) ++
  arule("ExprList1", "ExprList1 Comma PExpr", c => c.ExprList1.resultAs[Vector[Expr]] :+ c.PExpr.resultAs[Expr]) ++
  arule("ExprList1", "ExprList1 Comma", c => c.ExprList1.resultAs[Vector[Expr]] :+ NilExpr) ++
  arule("PExpr", "Expr", _.Expr.result) ++
  arule("PExpr", "ControlFlowExpr", c => ControlFlowExpr(c.ControlFlowExpr.resultAs[ControlFlow]))
  
val g_do = 
  arule("STDo", "Do Block",
      CS.Indent("Do", "Block"),
      c => Do(c.Block.resultAs[Block], false)) ++
  arule("DoExpr", "Do Block",
      c => Do(c.Block.resultAs[Block], false)) ++
  arule("STDo", "Do Times Block",
      CS.and(CS.Indent("Do", "Times"), CS.Indent("Do", "Block")),
      c => Do(c.Block.resultAs[Block], true)) ++
  arule("DoExpr", "Do Times Block",
      c => Do(c.Block.resultAs[Block], true))
  
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
      c => If(c.PExpr.resultAs[Expr], c.Block_1.resultAs[Block], c.Block_2.resultAs[Block])) ++
  arule("STIf", "If PExpr Then Block",
      CS.and(
          CS.Indent("If", "PExpr"), 
          CS.ifThenElse(CS.Line("If", "Then"), 
              CS.Indent("If", "Block"), 
              CS.and(
                  Subalign("If", "Then"),
                  CS.Indent("Then", "Block")))),
      c => If(c.PExpr.resultAs[Expr], c.Block.resultAs[Block], Block(Vector()))) ++
  arule("IfExpr", "If PExpr Then Block_1 Else Block_2", 
      c => If(c.PExpr.resultAs[Expr], c.Block_1.resultAs[Block], c.Block_2.resultAs[Block])) ++
  arule("IfExpr", "If PExpr Then Block",
      c => If(c.PExpr.resultAs[Expr], c.Block.resultAs[Block], Block(Vector())))
    
val g_while = 
  arule("STWhile", "While PExpr Do Block",
      CS.and(
        CS.Indent("While", "PExpr"),
        CS.ifThenElse(CS.Line("While", "Do"),
            CS.Indent("While", "Block"),
            CS.and(Subalign("While", "Do"), CS.Indent("Do", "Block")))),
      c => While(c.PExpr.resultAs[Expr], c.Block.resultAs[Block])) ++
  arule("WhileExpr", "While PExpr Do Block",
      c => While(c.PExpr.resultAs[Expr], c.Block.resultAs[Block]))
      
val g_for = 
  arule("STFor", "For Pattern In PExpr Do Block",
      CS.and(
          CS.Indent("For", "Pattern"),
          CS.Indent("For", "In"),
          CS.Indent("For", "PExpr"),
          CS.ifThenElse(CS.Line("For", "Do"),
              CS.Indent("For", "Block"),
              CS.and(Subalign("For", "Do"), CS.Indent("Do", "Block")))),              
      c => For(c.Pattern.resultAs[Pattern], c.PExpr.resultAs[Expr], c.Block.resultAs[Block])) ++
  arule("ForExpr", "For Pattern In PExpr Do Block",
      c => For(c.Pattern.resultAs[Pattern], c.PExpr.resultAs[Expr], c.Block.resultAs[Block]))

val g_match = 
  arule("STMatch", "Match PExpr STMatchCases",
      CS.and(
          CS.Indent("Match", "PExpr"),
          Subalign("Match", "STMatchCases")),
      c => Match(c.PExpr.resultAs[Expr], c.STMatchCases.resultAs[Vector[MatchCase]])) ++
  arule("STMatchCases", "STMatchCases STMatchCase", 
      CS.or(CS.Align("STMatchCases", "STMatchCase"), CS.Line("STMatchCases", "STMatchCase")),
      c => c.STMatchCases.resultAs[Vector[MatchCase]] :+ c.STMatchCase.resultAs[MatchCase]) ++
  arule("STMatchCases", "", c => Vector[MatchCase]()) ++
  arule("STMatchCase", "Case Pattern DoubleArrow Block", 
      CS.and(
        CS.Indent("Case", "Pattern"),
        CS.SameLine("Pattern", "DoubleArrow"),
        CS.Indent("Case", "Block")),
      c => MatchCase(c.Pattern.resultAs[Pattern], c.Block.resultAs[Block])) ++     
  arule("MatchExpr", "Match PExpr MatchCases",
      c => Match(c.PExpr.resultAs[Expr], c.MatchCases.resultAs[Vector[MatchCase]])) ++
  arule("MatchCases", "MatchCases MatchCase", 
      c => c.MatchCases.resultAs[Vector[MatchCase]] :+ c.MatchCase.resultAs[MatchCase]) ++
  arule("MatchCases", "", c => Vector[MatchCase]()) ++
  arule("MatchCase", "Case Pattern DoubleArrow Block", 
      c => MatchCase(c.Pattern.resultAs[Pattern], c.Block.resultAs[Block]))    

val g_context =
  arule("STContext", "Context OptContextParam Block",
      CS.and(
        CS.Indent("Context", "OptContextParam"),
        CS.Indent("Context", "Block")),
      c => ContextControl(c.OptContextParam.resultAs[Option[Expr]], c.Block.resultAs[Block])) ++
  arule("ContextExpr", "Context OptContextParam Block",
      c => ContextControl(c.OptContextParam.resultAs[Option[Expr]], c.Block.resultAs[Block])) ++
  arule("OptContextParam", "", c => None) ++
  arule("OptContextParam", "Le PExpr Gr", c => Some(c.PExpr.resultAs[Expr]))
      
val g_controlflow = 
  g_do ++ g_if ++ g_while ++ g_for ++ g_match ++ g_context ++
  arule("STControlFlow", "STDo", _.STDo.result) ++  
  arule("STControlFlow", "STIf", _.STIf.result) ++
  arule("STControlFlow", "STWhile", _.STWhile.result) ++
  arule("STControlFlow", "STFor", _.STFor.result) ++
  arule("STControlFlow", "STMatch", _.STMatch.result) ++
  arule("STControlFlow", "STContext", _.STContext.result) ++
  arule("ControlFlowExpr", "DoExpr", _.DoExpr.result) ++  
  arule("ControlFlowExpr", "IfExpr", _.IfExpr.result) ++
  arule("ControlFlowExpr", "WhileExpr", _.WhileExpr.result) ++
  arule("ControlFlowExpr", "ForExpr", _.ForExpr.result) ++
  arule("ControlFlowExpr", "MatchExpr", _.MatchExpr.result) ++
  arule("ControlFlowExpr", "ContextExpr", _.ContextExpr.result)

val g_pattern = 
  arule("AtomicPattern", "Underscore", c => PAny) ++
  arule("AtomicPattern", "Nil", c => PNil) ++
  arule("AtomicPattern", "Id", c => PId(c.Id.text)) ++
  arule("AtomicPattern", "Int", c => PInt(c.Int.resultAs[Integer].value)) ++
  arule("AtomicPattern", "QuotationMark StringLiteral QuotationMark", 
    c => PString(mkStringLiteral(c.StringLiteral.codes).value)) ++
  arule("AtomicPattern", "ScriptTrue", c => PBool(true)) ++
  arule("AtomicPattern", "ScriptFalse", c => PBool(false)) ++
  arule("AtomicPattern", "Apostrophe PatternTerm Apostrophe", c => PLogic(c.PatternTerm.resultAs[Preterm])) ++
  arule("AtomicPattern", "RoundBracketOpen PatternList RoundBracketClose", c => mkTuplePattern(c.PatternList.resultAs[Vector[Pattern]], true)) ++
  arule("AtomicPattern", "SquareBracketOpen PatternList SquareBracketClose", c => mkTuplePattern(c.PatternList.resultAs[Vector[Pattern]], false)) ++  
  arule("PrependPattern", "AtomicPattern Prepend PrependPattern", c => PPrepend(c.AtomicPattern.resultAs[Pattern], c.PrependPattern.resultAs[Pattern])) ++
  arule("PrependPattern", "AppendPattern", _.AppendPattern.result) ++
  arule("AppendPattern", "AppendPattern Append AtomicPattern", c => PAppend(c.AppendPattern.resultAs[Pattern], c.AtomicPattern.resultAs[Pattern])) ++
  arule("AppendPattern", "AtomicPattern", _.AtomicPattern.result) ++
  arule("IfPattern", "PrependPattern", _.PrependPattern.result) ++
  arule("IfPattern", "IfPattern If Expr", c => PIf(c.IfPattern.resultAs[Pattern], c.Expr.resultAs[Expr])) ++
  arule("Pattern", "IfPattern", _.IfPattern.result) ++
  arule("OptPattern", "", c => None) ++
  arule("OptPattern", "Pattern", c => Some(c.Pattern.resultAs[Pattern])) ++
  arule("PatternList", "", c => Vector[Pattern]()) ++
  arule("PatternList", "PatternList1", _.PatternList1.result) ++
  arule("PatternList1", "Comma Pattern", c => Vector[Pattern](PNil, c.Pattern.resultAs[Pattern])) ++
  arule("PatternList1", "Comma", c => Vector[Pattern](PNil, PNil)) ++  
  arule("PatternList1", "Pattern", c => Vector[Pattern](c.Pattern.resultAs[Pattern])) ++
  arule("PatternList1", "PatternList1 Comma Pattern", c => c.PatternList1.resultAs[Vector[Pattern]] :+ c.Pattern.resultAs[Pattern]) ++
  arule("PatternList1", "PatternList1 Comma", c => c.PatternList1.resultAs[Vector[Pattern]] :+ PNil)

val g_show =
  arule("ST", "Show PExpr",
    CS.Indent("Show", "PExpr"),
    c => STShow(c.PExpr.resultAs[Expr]))

val g_fail =
  arule("ST", "Fail",
    c => STFail(None)) ++
  arule("ST", "Fail PExpr",
    CS.Indent("Fail", "PExpr"),
    c => STFail(Some(c.PExpr.resultAs[Expr])))

val g_val = 
  arule("ST", "Val Pattern Eq Block",
    CS.and(
      CS.Indent("Val", "Pattern"),
      CS.SameLine("Pattern", "Eq"),
      CS.or(CS.Line("Eq", "Block"), CS.Indent("Val", "Block"))),
    c => STVal(c.Pattern.resultAs[Pattern], c.Block.resultAs[Block])) ++
  arule("ST", "Val IdList", 
    CS.Indent("Val", "IdList"),
    c => STValIntro(c.IdList.resultAs[List[Id]])) ++
  arule("IdList", "Id", c => List[Id](Id(c.Id.text))) ++
  arule("IdList", "IdList Id", c => c.IdList.resultAs[List[Id]] :+ Id(c.Id.text))


val g_assign = 
  arule("ST", "Pattern Eq Block",
      CS.and(
          CS.SameLine("Pattern", "Eq"),
          CS.Protrude("Pattern"),
          CS.or(CS.Line("Eq", "Block"), CS.Indent("Pattern", "Block"))),
      c => STAssign(c.Pattern.resultAs[Pattern], c.Block.resultAs[Block]))
  
def mkSTDef(cases : Vector[DefCase]) : STDef = {
  var result : Map[String, Vector[DefCase]] = Map()
  for (c <- cases) {
    result.get(c.name) match {
      case None => result = result + (c.name -> Vector(c))
      case Some(cs) => result = result + (c.name -> (cs :+ c))
    }
  }
  STDef(result)
}

val g_def =
  arule("ST", "Def DefCases",
      CS.Indent("Def", "DefCases"),
      c => mkSTDef(c.DefCases.resultAs[Vector[DefCase]])) ++
  arule("DefCases", "", c => Vector[DefCase]()) ++
  arule("DefCases", "DefCases DefCase", 
      CS.Align("DefCases", "DefCase"),
      c => c.DefCases.resultAs[Vector[DefCase]] :+ c.DefCase.resultAs[DefCase]) ++
  arule("DefCase", "Id Pattern Eq Block",
      CS.and(
          CS.Indent("Id", "Pattern"),
          CS.or(CS.SameLine("Pattern", "Eq"), CS.SameLine("Id", "Eq")),
          CS.Indent("Id", "Block")),
      c => DefCase(c.Id.text, c.Pattern.resultAs[Pattern], c.Block.resultAs[Block]))
      
val g_return =
  arule("ST", "Return PExpr", CS.Indent("Return", "PExpr"), c => STReturn(c.PExpr.resultAs[Expr]))
    
val g_assume =
  arule("ST", "Assume OptAssign PExpr", 
    CS.and(
      CS.Indent("Assume", "OptAssign"),
      CS.Indent("Assume", "PExpr")),
    c => STAssume(c.OptAssign.resultAs[Option[String]], c.PExpr.resultAs[Expr]))

val g_let = 
  arule("ST", "Let OptAssign PExpr",
    CS.and(
      CS.Indent("Let", "OptAssign"),
      CS.Indent("Let", "PExpr")),
    c => STLet(c.OptAssign.resultAs[Option[String]], c.PExpr.resultAs[Expr]))

val g_choose = 
  arule("ST", "Choose OptAssign PExpr_1 From PExpr_2",
    CS.and(
      CS.Indent("Choose", "OptAssign"),
      CS.Indent("Choose", "PExpr_1"),
      CS.ifThenElse(CS.Line("Choose", "From"),
        CS.Indent("Choose", "PExpr_2"),
        CS.and(Subalign("Choose", "From"), CS.Indent("From", "PExpr_2")))),
    c => STChoose(c.OptAssign.resultAs[Option[String]], 
                  c.PExpr_1.resultAs[Expr],
                  c.PExpr_2.resultAs[Expr])) 

val g_theorem = 
  arule("ST", "Theorem OptAssign Expr Block",
    CS.and(
      CS.Indent("Theorem", "OptAssign"),
      CS.Indent("Theorem", "Expr"),
      CS.Indent("Theorem", "Block"),
      CS.Indent("Block", "Expr")),
    c => STTheorem(c.OptAssign.resultAs[Option[String]],
                   c.Expr.resultAs[Expr],
                   c.Block.resultAs[Block]))


val g_logic_statements = 
  arule("OptAssign", "", c => None) ++
  arule("OptAssign", "Id Eq", c => Some(c.Id.text)) ++
  g_assume ++ g_let ++ g_choose ++ g_theorem

val g_statement = 
  g_val ++ g_assign ++ g_def ++ g_return ++ g_show ++ g_fail ++
  g_logic_statements ++
  arule("Statement", "Expr", 
    CS.or(CS.Protrude("Expr"), CS.not(CS.First("Expr"))),
    c => STExpr(c.Expr.resultAs[Expr])) ++
  arule("Statement", "ST", _.ST.result) ++
  arule("Statement", "STControlFlow", c => STControlFlow(c.STControlFlow.resultAs[ControlFlow])) ++ 
  arule("Statements", "", c => Vector[Statement]()) ++
  arule("Statements", "Statements Statement", CS.Align("Statements", "Statement"),
      c => c.Statements.resultAs[Vector[Statement]] :+ c.Statement.resultAs[Statement]) ++
  arule("Block", "Statements", c => Block(c.Statements.resultAs[Vector[Statement]])) 

val g_header = 
  arule("ST", "Theory Namespace AliasList Extends NamespaceList", 
    CS.and(
      CS.Indent("Theory", "Namespace"),
      CS.ifThenElse(CS.Line("Theory", "Extends"),
        CS.Indent("Theory", "NamespaceList"),
        CS.and(CS.Align("Theory", "Extends"), CS.Indent("Extends", "NamespaceList")))),
    c => STTheory(Namespace(c.Namespace.text), c.AliasList.resultAs[List[(Id, Namespace)]].reverse, c.NamespaceList.resultAs[List[Namespace]].reverse)) ++
  arule("NamespaceList", "", c => List[Namespace]()) ++
  arule("NamespaceList", "NamespaceList Namespace",
    c => (Namespace(c.Namespace.text)) :: c.NamespaceList.resultAs[List[Namespace]]) ++
  arule("AliasList", "", c => List[(Id, Namespace)]()) ++
  arule("AliasList", "AliasList Alias", 
    CS.Align("AliasList", "Alias"),
    c => c.Alias.resultAs[(Id, Namespace)] :: c.AliasList.resultAs[List[(Id, Namespace)]]) ++
  arule("Alias", "Id Eq Namespace", 
    c => (Id(c.Id.text), Namespace(c.Namespace.text)))

val g_prog = 
  Syntax.grammar ++
  g_literals ++
  g_pattern ++
  g_expr ++
  g_statement ++
  g_controlflow ++
  g_header ++
  arule("ValueQuotedTerm", "PExpr", _.PExpr.result) ++
  arule("PatternQuotedTerm", "Pattern", _.Pattern.result) ++
  arule("Prog", "Block", _.Block.result)

}