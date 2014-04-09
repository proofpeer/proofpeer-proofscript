package proofpeer.proofscript.frontend

import proofpeer.indent._
import proofpeer.indent.API._
import proofpeer.indent.APIConversions._
import Derivation.Context  
import proofpeer.indent.{Constraints => CS}
import ParseTree._

class ScriptGrammar(annotate : (Any, Option[Span]) => Any) {
  
def ltokenrule(nonterminal : String, c1 : Char, c2 : Char) : Grammar = 
  tokenrule(nonterminal, Range.interval(c1, c2)) ++ lexical(nonterminal)
  
def ltokenrule(nonterminal : String, c : Char) : Grammar = ltokenrule(nonterminal, c, c)

def ltokenrule(nonterminal : String, i : Int) : Grammar = 
  tokenrule(nonterminal, Range.interval(i, i)) ++ lexical(nonterminal)
  

val g_literals = 
  ltokenrule("LowerLetter", 'a', 'z') ++
  ltokenrule("UpperLetter", 'A', 'Z') ++
  lexrule("Letter", "UpperLetter") ++
  lexrule("Letter", "LowerLetter") ++  
  ltokenrule("Comma", ',') ++
  ltokenrule("Underscore", '_') ++ 
  ltokenrule("Plus", '+') ++  
  ltokenrule("Minus", '-') ++
  ltokenrule("Times", '*') ++
  ltokenrule("Slash", '/') ++
  ltokenrule("Le", '<') ++
  ltokenrule("Gr", '>') ++
  ltokenrule("Eq", '=') ++
  ltokenrule("ExclamationMark", '!') ++
  ltokenrule("QuestionMark", '?') ++
  lexrule("Leq", "Le Eq") ++
  lexrule("Geq", "Gr Eq") ++
  lexrule("NEquals", "ExclamationMark Eq") ++
  lexrule("Equals", "Eq_1 Eq_2") ++
  ltokenrule("RoundBracketOpen", '(') ++
  ltokenrule("RoundBracketClose", ')') ++  
  ltokenrule("Digit", '0', '9') ++
  lexrule("Arrow", "Eq Gr") ++
  lexrule("Nat", "Nat Digit") ++
  lexrule("Nat", "Digit") ++
  lexrule("Id", "Id Digit") ++
  lexrule("Id", "Id Letter") ++
  lexrule("Id", "Id Underscore Letter") ++
  lexrule("Id", "Id Underscore Digit") ++
  lexrule("Id", "LowerLetter") ++
  lexrule("Val", literal("val")) ++
  lexrule("Def", literal("def")) ++
  lexrule("Mod", literal("mod")) ++
  lexrule("Or", literal("or")) ++
  lexrule("And", literal("and")) ++
  lexrule("Not", literal("not")) ++
  lexrule("True", literal("true")) ++
  lexrule("False", literal("false")) ++
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
  arule("Int", "Nat", c => Integer(BigInt(c.Nat.text, 10))) ++
  arule("Int", "Minus Nat", c => Integer(-BigInt(c.Nat.text, 10))) ++  
  arule("PrimitiveExpr", "Nat", c => Integer(BigInt(c.Nat.text, 10))) ++
  arule("PrimitiveExpr", "RoundBracketOpen Expr RoundBracketClose", c => c.Expr.resultAs[Expr]) ++
  arule("PrimitiveExpr", "RoundBracketOpen ControlFlowExpr RoundBracketClose", 
      c => ControlFlowExpr(c.ControlFlowExpr.resultAs[ControlFlow])) ++
  arule("PrimitiveExpr", "True", c => Bool(true)) ++  
  arule("PrimitiveExpr", "False", c => Bool(false)) ++  
  arule("OrExpr", "OrExpr Or AndExpr", 
      c => BinaryOperation(annotateBinop(Or, c.Or.span), c.OrExpr.resultAs[Expr], c.AndExpr.resultAs[Expr])) ++
  arule("OrExpr", "AndExpr", _.AndExpr.result) ++
  arule("AndExpr", "AndExpr And NotExpr", 
      c => BinaryOperation(annotateBinop(And, c.And.span), c.AndExpr.resultAs[Expr], c.NotExpr.resultAs[Expr])) ++
  arule("AndExpr", "NotExpr", _.NotExpr.result) ++
  arule("NotExpr", "Not NotExpr", 
      c => UnaryOperation(annotateUnop(Not, c.Not.span), c.NotExpr.resultAs[Expr])) ++
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
  arule("CmpOp", "Equals", c => Eq) ++
  arule("CmpOp", "NEquals", c => NEq) ++
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
  arule("FunExpr", "Pattern Arrow Block", c => Fun(c.Pattern.resultAs[Pattern], c.Block.resultAs[Block])) ++
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
  arule("STMatchCase", "Case Pattern Arrow Block", 
      CS.and(
        CS.Indent("Case", "Pattern"),
        CS.SameLine("Pattern", "Arrow"),
        CS.Indent("Case", "Block")),
      c => MatchCase(c.Pattern.resultAs[Pattern], c.Block.resultAs[Block])) ++     
  arule("MatchExpr", "Match Expr MatchCases",
      c => Match(c.Expr.resultAs[Expr], c.MatchCases.resultAs[Vector[MatchCase]])) ++
  arule("MatchCases", "MatchCases MatchCase", 
      c => c.MatchCases.resultAs[Vector[MatchCase]] :+ c.MatchCase.resultAs[MatchCase]) ++
  arule("MatchCases", "", c => Vector[MatchCase]()) ++
  arule("MatchCase", "Case Pattern Arrow Block", 
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
  arule("Pattern", "True", c => PBool(true)) ++
  arule("Pattern", "False", c => PBool(false)) ++
  arule("OptPattern", "", c => None) ++
  arule("OptPattern", "Pattern", c => Some(c.Pattern.resultAs[Pattern]))

val g_val = 
  arule("ST", "Val Pattern Eq Block",
      CS.and(
          CS.Indent("Val", "Pattern"),
          CS.SameLine("Pattern", "Eq"),
          CS.or(CS.Line("Eq", "Block"), CS.Indent("Val", "Block"))),
      c => STVal(c.Pattern.resultAs[Pattern], c.Block.resultAs[Block]))

val g_assign = 
  arule("ST", "Pattern Eq Block",
      CS.and(
          CS.SameLine("Pattern", "Eq"),
          CS.Protrude("Pattern"),
          CS.or(CS.Line("Eq", "Block"), CS.Indent("Pattern", "Block"))),
      c => STAssign(c.Pattern.resultAs[Pattern], c.Block.resultAs[Block]))
  
val g_def =
  arule("ST", "Def DefCases",
      CS.Indent("Def", "DefCases"),
      c => STDef(c.DefCases.resultAs[Vector[DefCase]])) ++
  arule("DefCases", "", c => Vector[DefCase]()) ++
  arule("DefCases", "DefCases DefCase", 
      CS.Align("DefCases", "DefCase"),
      c => c.DefCases.resultAs[Vector[DefCase]] :+ c.DefCase.resultAs[DefCase]) ++
  arule("DefCase", "Id OptPattern Eq Block",
      CS.and(
          CS.Indent("Id", "OptPattern"),
          CS.or(CS.SameLine("OptPattern", "Eq"), CS.SameLine("Id", "Eq")),
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
  g_literals ++
  g_pattern ++
  g_expr ++
  g_statement ++
  g_controlflow ++
  arule("Prog", "Block", _.Block.result)

}