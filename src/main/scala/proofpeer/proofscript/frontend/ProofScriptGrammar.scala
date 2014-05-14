package proofpeer.proofscript.frontend

import proofpeer.indent._
import proofpeer.indent.API._
import proofpeer.indent.APIConversions._
import Derivation.Context  
import proofpeer.indent.{Constraints => CS}
import ParseTree._

class ProofScriptGrammar(annotate : (Any, Option[Span]) => Any) {
  
def ltokenrule(nonterminal : String, c1 : Char, c2 : Char) : Grammar = 
  tokenrule(nonterminal, Range.interval(c1, c2)) ++ lexical(nonterminal)
  
def ltokenrule(nonterminal : String, c : Char) : Grammar = ltokenrule(nonterminal, c, c)

def ltokenrule(nonterminal : String, i : Int) : Grammar = 
  tokenrule(nonterminal, Range.interval(i, i)) ++ lexical(nonterminal)
  
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

val g_literals =
  ltokenrule("Plus", '+') ++  
  ltokenrule("Minus", '-') ++
  ltokenrule("Times", '*') ++
  ltokenrule("Slash", '/') ++
  ltokenrule("Le", '<') ++
  ltokenrule("Gr", '>') ++
  ltokenrule("Leq", 0x2264) ++
  ltokenrule("Geq", 0x2265) ++
  ltokenrule("DoubleArrow", 0x21D2) ++
  ltokenrule("AssignEq", 0x2254) ++
  ltokenrule("Apostrophe", 0x27) ++
  lexrule("Val", literal("val")) ++
  lexrule("Def", literal("def")) ++
  lexrule("Mod", literal("mod")) ++
  lexrule("ScriptOr", literal("or")) ++
  lexrule("ScriptAnd", literal("and")) ++
  lexrule("ScriptNot", literal("not")) ++
  lexrule("ScriptTrue", literal("true")) ++
  lexrule("ScriptFalse", literal("false")) ++
  lexrule("Lazy", literal("lazy")) ++
  lexrule("If", literal("if")) ++
  lexrule("Then", literal("then")) ++
  lexrule("Else", literal("else")) ++
  lexrule("While", literal("while")) ++
  lexrule("Do", literal("do")) ++
  lexrule("For", literal("for")) ++
  lexrule("In", literal("in")) ++
  lexrule("Match", literal("match")) ++
  lexrule("Case", literal("case")) ++
  lexrule("Return", literal("return")) 
  
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
  
val g_expr =
  arule("PrimitiveExpr", "Id", c => Id(c.Id.text)) ++
  arule("Int", "Digits", c => Integer(BigInt(c.Digits.text, 10))) ++
  arule("Int", "Minus Digits", c => Integer(-BigInt(c.Digits.text, 10))) ++  
  arule("PrimitiveExpr", "Digits", c => Integer(BigInt(c.Digits.text, 10))) ++
  arule("PrimitiveExpr", "RoundBracketOpen Expr RoundBracketClose", c => c.Expr.resultAs[Expr]) ++
  arule("PrimitiveExpr", "RoundBracketOpen ControlFlowExpr RoundBracketClose", 
      c => ControlFlowExpr(c.ControlFlowExpr.resultAs[ControlFlow])) ++
  arule("PrimitiveExpr", "ScriptTrue", c => Bool(true)) ++  
  arule("PrimitiveExpr", "ScriptFalse", c => Bool(false)) ++  
  arule("PrimitiveExpr", "Apostrophe PrefixTerm Apostrophe", c => LogicTerm(c.PrefixTerm.resultAs[proofpeer.proofscript.logic.Preterm])) ++
  arule("OrExpr", "OrExpr ScriptOr AndExpr", 
      c => BinaryOperation(annotateBinop(Or, c.ScriptOr.span), c.OrExpr.resultAs[Expr], c.AndExpr.resultAs[Expr])) ++
  arule("OrExpr", "AndExpr", _.AndExpr.result) ++
  arule("AndExpr", "AndExpr ScriptAnd NotExpr", 
      c => BinaryOperation(annotateBinop(And, c.ScriptAnd.span), c.AndExpr.resultAs[Expr], c.NotExpr.resultAs[Expr])) ++
  arule("AndExpr", "NotExpr", _.NotExpr.result) ++
  arule("NotExpr", "ScriptNot NotExpr", 
      c => UnaryOperation(annotateUnop(Not, c.ScriptNot.span), c.NotExpr.resultAs[Expr])) ++
  arule("NotExpr", "CmpExpr", _.CmpExpr.result) ++
  arule("CmpExpr", "CmpExpr CmpOp AddExpr", { c =>
    val operator = c.CmpOp.resultAs[CmpOperator]
    val operand = c.AddExpr.resultAs[Expr]
    c.CmpExpr.resultAs[Expr] match {
      case op : CmpOperation =>
        CmpOperation(op.operators :+ operator, op.operands :+ operand)
      case e =>
        CmpOperation(Vector(operator), Vector(e, operand))
    }
  }) ++
  arule("CmpExpr", "AddExpr", _.AddExpr.result) ++
  arule("CmpOp", "Le", c => Le) ++
  arule("CmpOp", "Gr", c => Gr) ++
  arule("CmpOp", "Leq", c => Leq) ++
  arule("CmpOp", "Geq", c => Geq) ++
  arule("CmpOp", "Eq", c => Eq) ++
  arule("CmpOp", "NotEq", c => NEq) ++
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
  arule("ExprList", "Expr", c => Vector[Expr](c.Expr.resultAs[Expr])) ++
  arule("ExprList", "ExprList Comma Expr", c => c.ExprList.resultAs[Vector[Expr]] :+ c.Expr.resultAs[Expr])
  
val g_do = 
  arule("STDo", "Do Block",
      CS.Indent("Do", "Block"),
      c => Do(c.Block.resultAs[Block])) ++
  arule("DoExpr", "Do Block",
      c => Do(c.Block.resultAs[Block]))      
  
val g_if =
  arule("STIf", "If Expr Then Block_1 Else Block_2", 
      CS.and(
          CS.Indent("If", "Expr"), 
          CS.ifThenElse(CS.Line("If", "Then"), 
              CS.and(
                  CS.Indent("If", "Block_1"),
                  CS.or(CS.Line("Then", "Else"), CS.Align("If", "Else"))),
              CS.and(
                  CS.Align("If", "Then"),
                  CS.Indent("Then", "Block_1"),
                  CS.Align("Then", "Else"))), 
          CS.ifThenElse(CS.Line("If", "Else"), 
              CS.Indent("If", "Block_2"), 
              CS.Indent("Else", "Block_2"))),
      c => If(c.Expr.resultAs[Expr], c.Block_1.resultAs[Block], c.Block_2.resultAs[Block])) ++
  arule("STIf", "If Expr Then Block",
      CS.and(
          CS.Indent("If", "Expr"), 
          CS.ifThenElse(CS.Line("If", "Then"), 
              CS.Indent("If", "Block"), 
              CS.and(
                  CS.Align("If", "Then"),
                  CS.Indent("Then", "Block")))),
      c => If(c.Expr.resultAs[Expr], c.Block.resultAs[Block], Block(Vector()))) ++
  arule("IfExpr", "If Expr Then Block_1 Else Block_2", 
      c => If(c.Expr.resultAs[Expr], c.Block_1.resultAs[Block], c.Block_2.resultAs[Block])) ++
  arule("IfExpr", "If Expr Then Block",
      c => If(c.Expr.resultAs[Expr], c.Block.resultAs[Block], Block(Vector())))
    
val g_while = 
  arule("STWhile", "While Expr Do Block",
      CS.and(
        CS.Indent("While", "Expr"),
        CS.ifThenElse(CS.Line("While", "Do"),
            CS.Indent("While", "Block"),
            CS.and(CS.Align("While", "Do"), CS.Indent("Do", "Block")))),
      c => While(c.Expr.resultAs[Expr], c.Block.resultAs[Block])) ++
  arule("WhileExpr", "While Expr Do Block",
      c => While(c.Expr.resultAs[Expr], c.Block.resultAs[Block]))
      
val g_for = 
  arule("STFor", "For Pattern In Expr Do Block",
      CS.and(
          CS.Indent("For", "Pattern"),
          CS.Indent("For", "In"),
          CS.Indent("For", "Expr"),
          CS.ifThenElse(CS.Line("For", "Do"),
              CS.Indent("For", "Block"),
              CS.and(CS.Align("For", "Do"), CS.Indent("Do", "Block")))),              
      c => For(c.Pattern.resultAs[Pattern], c.Expr.resultAs[Expr], c.Block.resultAs[Block])) ++
  arule("ForExpr", "For Pattern In Expr Do Block",
      c => For(c.Pattern.resultAs[Pattern], c.Expr.resultAs[Expr], c.Block.resultAs[Block]))

val g_match = 
  arule("STMatch", "Match Expr STMatchCases",
      CS.and(
          CS.Indent("Match", "Expr"),
          CS.or(CS.Line("Match", "STMatchCases"), CS.Align("Match", "STMatchCases"))),
      c => Match(c.Expr.resultAs[Expr], c.STMatchCases.resultAs[Vector[MatchCase]])) ++
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
  arule("MatchExpr", "Match Expr MatchCases",
      c => Match(c.Expr.resultAs[Expr], c.MatchCases.resultAs[Vector[MatchCase]])) ++
  arule("MatchCases", "MatchCases MatchCase", 
      c => c.MatchCases.resultAs[Vector[MatchCase]] :+ c.MatchCase.resultAs[MatchCase]) ++
  arule("MatchCases", "", c => Vector[MatchCase]()) ++
  arule("MatchCase", "Case Pattern DoubleArrow Block", 
      c => MatchCase(c.Pattern.resultAs[Pattern], c.Block.resultAs[Block]))      
      
val g_controlflow = 
  g_do ++ g_if ++ g_while ++ g_for ++ g_match ++
  arule("STControlFlow", "STDo", _.STDo.result) ++  
  arule("STControlFlow", "STIf", _.STIf.result) ++
  arule("STControlFlow", "STWhile", _.STWhile.result) ++
  arule("STControlFlow", "STFor", _.STFor.result) ++
  arule("STControlFlow", "STMatch", _.STMatch.result) ++
  arule("ControlFlowExpr", "DoExpr", _.DoExpr.result) ++  
  arule("ControlFlowExpr", "IfExpr", _.IfExpr.result) ++
  arule("ControlFlowExpr", "WhileExpr", _.WhileExpr.result) ++
  arule("ControlFlowExpr", "ForExpr", _.ForExpr.result) ++
  arule("ControlFlowExpr", "MatchExpr", _.MatchExpr.result) 

val g_pattern = 
  arule("Pattern", "Underscore", c => PAny) ++
  arule("Pattern", "Id", c => PId(c.Id.text)) ++
  arule("Pattern", "Int", c => PInt(c.Int.resultAs[Integer].value)) ++
  arule("Pattern", "ScriptTrue", c => PBool(true)) ++
  arule("Pattern", "ScriptFalse", c => PBool(false)) ++
  arule("OptPattern", "", c => None) ++
  arule("OptPattern", "Pattern", c => Some(c.Pattern.resultAs[Pattern]))

val g_val = 
  arule("ST", "Val Pattern AssignEq Block",
      CS.and(
          CS.Indent("Val", "Pattern"),
          CS.SameLine("Pattern", "AssignEq"),
          CS.or(CS.Line("AssignEq", "Block"), CS.Indent("Val", "Block"))),
      c => STVal(c.Pattern.resultAs[Pattern], c.Block.resultAs[Block]))

val g_assign = 
  arule("ST", "Pattern AssignEq Block",
      CS.and(
          CS.SameLine("Pattern", "AssignEq"),
          CS.Protrude("Pattern"),
          CS.or(CS.Line("AssignEq", "Block"), CS.Indent("Pattern", "Block"))),
      c => STAssign(c.Pattern.resultAs[Pattern], c.Block.resultAs[Block]))
  
val g_def =
  arule("ST", "Def DefCases",
      CS.Indent("Def", "DefCases"),
      c => STDef(c.DefCases.resultAs[Vector[DefCase]])) ++
  arule("DefCases", "", c => Vector[DefCase]()) ++
  arule("DefCases", "DefCases DefCase", 
      CS.Align("DefCases", "DefCase"),
      c => c.DefCases.resultAs[Vector[DefCase]] :+ c.DefCase.resultAs[DefCase]) ++
  arule("DefCase", "Id OptPattern AssignEq Block",
      CS.and(
          CS.Indent("Id", "OptPattern"),
          CS.or(CS.SameLine("OptPattern", "AssignEq"), CS.SameLine("Id", "AssignEq")),
          CS.Indent("Id", "Block")),
      c => DefCase(c.Id.text, c.OptPattern.resultAs[Option[Pattern]], c.Block.resultAs[Block]))
      
val g_return =
  arule("ST", "Return Expr", CS.Indent("Return", "Expr"), c => STReturn(c.Expr.resultAs[Expr]))
    
val g_statement = 
  g_val ++ g_assign ++ g_def ++ g_return ++ 
  arule("Statement", "ST", _.ST.result) ++
  arule("Statement", "STControlFlow", c => STControlFlow(c.STControlFlow.resultAs[ControlFlow])) ++ 
  arule("Statements", "", c => Vector[Statement]()) ++
  arule("Statements", "Statements Statement", CS.Align("Statements", "Statement"),
      c => c.Statements.resultAs[Vector[Statement]] :+ c.Statement.resultAs[Statement]) ++
  arule("Block", "Statements", c => Block(c.Statements.resultAs[Vector[Statement]])) ++
  arule("Block", "Statements Expr", 
      CS.and(
          CS.Align("Statements", "Expr"), 
          CS.or(CS.Protrude("Expr"), CS.not(CS.First("Expr")))),
      c => Block(c.Statements.resultAs[Vector[Statement]] :+ STExpr(c.Expr.resultAs[Expr])))

val g_prog = 
  proofpeer.proofscript.logic.Syntax.grammar ++
  g_literals ++
  g_pattern ++
  g_expr ++
  g_statement ++
  g_controlflow ++
  arule("PrefixQuotedTerm", "Block", _.Block.result) ++
  arule("Prog", "Block", _.Block.result)

}