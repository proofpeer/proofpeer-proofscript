package proofpeer.proofscript.compiler

sealed trait ParseTree {
  lazy val (freeVars, introVars) : (Set[String], Set[String]) = calcVars
  protected def calcVars : (Set[String], Set[String]) 
}

object ParseTree {
  
  sealed trait Expr extends ParseTree {
    protected def calcFreeVars : Set[String]
    protected def calcVars = (calcFreeVars, Set())
  }
  
  case class Bool(value : Boolean) extends Expr {
    protected def calcFreeVars = Set()
  }
  
  case class Integer(value : BigInt) extends Expr {
    protected def calcFreeVars = Set()
  }
  
  case class Id(name : String) extends Expr {
    protected def calcFreeVars = Set(name)
  }
  
  case class UnaryOperation(op : UnaryOperator, expr : Expr) extends Expr {
    protected def calcFreeVars = expr.freeVars
  }
  
  case class BinaryOperation(op : BinaryOperator, left : Expr, right : Expr) extends Expr {
    protected def calcFreeVars = left.freeVars ++ right.freeVars
  }
  
  case class CmpOperation(operators : Vector[CmpOperator], operands : Vector[Expr]) extends Expr {
    protected def calcFreeVars = operands.foldLeft(Set[String]())((x, y) => x ++ y.freeVars)   
  }
    
  case class App(f : Expr, g : Expr) extends Expr {
    protected def calcFreeVars = f.freeVars ++ g.freeVars
  }
  
  case class Fun(param : Pattern, body : Block) extends Expr {
    protected def calcFreeVars = body.freeVars -- param.freeVars
  }
  
  case class Lazy(expr : Expr) extends Expr {
    protected def calcFreeVars = expr.freeVars
  }
  
  case class ControlFlowExpr(controlflow : ControlFlow) extends Expr {
    protected def calcFreeVars = controlflow.freeVars
  }
  
  sealed trait ControlFlow extends ParseTree {
    protected def calcFreeVars : Set[String]
    protected def calcVars = (calcFreeVars, Set())    
  }

  case class Do(block : Block) extends ControlFlow {
    protected def calcFreeVars = block.freeVars
  }
  
  case class If(cond : Expr, thenCase : Block, elseCase : Block) extends ControlFlow {
    protected def calcFreeVars = cond.freeVars ++ thenCase.freeVars ++ elseCase.freeVars
  }
  
  case class While(cond : Expr, body : Block) extends ControlFlow {
    protected def calcFreeVars = cond.freeVars ++ body.freeVars
  }
  
  case class For(pat : Pattern, coll : Expr, body : Block) extends ControlFlow {
    protected def calcFreeVars = pat.freeVars ++ coll.freeVars ++ (body.freeVars -- pat.introVars)    
  }
  
  case class MatchCase(pat : Pattern, body : Block) extends ParseTree {
    protected def calcVars : (Set[String], Set[String]) = {
      val frees : Set[String] = pat.freeVars ++ (body.freeVars -- pat.introVars)
      (frees, Set())
    }
  }
  
  case class Match(expr : Expr, cases : Vector[MatchCase]) extends ControlFlow {
    protected def calcFreeVars = cases.foldLeft(expr.freeVars)((fvars, mc) => fvars ++ mc.freeVars) 
  }

  sealed trait Operator 
 
  sealed trait UnaryOperator extends Operator 
  case object Neg extends UnaryOperator
  case object Not extends UnaryOperator

  sealed trait BinaryOperator extends Operator
  case object Add extends BinaryOperator
  case object Sub extends BinaryOperator
  case object Mul extends BinaryOperator
  case object Div extends BinaryOperator
  case object Mod extends BinaryOperator
  case object And extends BinaryOperator
  case object Or extends BinaryOperator
  
  sealed trait CmpOperator extends Operator
  case object Eq extends CmpOperator
  case object NEq extends CmpOperator
  case object Le extends CmpOperator
  case object Leq extends CmpOperator
  case object Gr extends CmpOperator
  case object Geq extends CmpOperator  
  
  sealed trait Pattern extends ParseTree
  
  case object PAny extends Pattern {
    protected def calcVars = (Set(), Set())
  }
  
  case class PId(name : String) extends Pattern {
    protected def calcVars = (Set(), Set(name))
  }
  
  case class PInt(value : BigInt) extends Pattern {
    protected def calcVars = (Set(), Set())   
  }
  
  case class PBool(value : Boolean) extends Pattern {
    protected def calcVars = (Set(), Set())      
  }
  
  sealed trait Statement extends ParseTree
  
  case class STExpr(expr : Expr) extends Statement {
    protected def calcVars = (expr.freeVars, Set())
  }
  
  case class STControlFlow(controlflow : ControlFlow) extends Statement {
    protected def calcVars = (controlflow.freeVars, Set())    
  }
  
  case class STVal(pat : Pattern, body : Block) extends Statement {
    protected def calcVars = (pat.freeVars ++ body.freeVars, pat.introVars)
  }

  case class STAssign(pat : Pattern, body : Block) extends Statement {
    protected def calcVars = (pat.freeVars ++ body.freeVars, Set())
  }
  
  case class STDef(cases : Vector[DefCase]) extends Statement {
    protected def calcVars = {
      var names = Set[String]()
      var frees = Set[String]()
      for (c <- cases) {
        names = names + c.name
        frees = frees ++ c.freeVars
      }
      (frees -- names, Set())
    }
  }
    
  case class DefCase(name : String, param : Option[Pattern], body : Block) extends ParseTree {
    protected def calcVars = {
      param match {
        case None => (body.freeVars, Set())
        case Some(param) => (param.freeVars ++ (body.freeVars -- param.introVars), Set())
      }
    }
  }
  
  case class STReturn(exprs : Vector[Expr]) extends Statement {
    protected def calcVars = (exprs.foldLeft(Set[String]())((frees, e) => frees ++ e.freeVars), Set())
  }

  case class STYield(exprs : Vector[Expr]) extends Statement {
    protected def calcVars = (exprs.foldLeft(Set[String]())((frees, e) => frees ++ e.freeVars), Set())
  }
    
  case class Block(statements : Vector[Statement]) extends ParseTree {
    protected def calcVars : (Set[String], Set[String]) = {
      var frees : Set[String] = Set()
      var intros : Set[String] = Set()
      for (st <- statements.reverseIterator) {
        val free = st.freeVars
        val intro = st.introVars
        frees = (frees -- intro) ++ free
        intros = intros ++ intro
      }
      (frees, intros)
    }
  }
  
}

object Parser {
  
import proofpeer.indent._
import proofpeer.indent.API._
import proofpeer.indent.APIConversions._
import Derivation.Context  
import proofpeer.indent.{Constraints => CS}

def ltokenrule(nonterminal : String, c1 : Char, c2 : Char) : Grammar = 
  tokenrule(nonterminal, Range.interval(c1, c2)) ++ lexical(nonterminal)
  
def ltokenrule(nonterminal : String, c : Char) : Grammar = ltokenrule(nonterminal, c, c)

import ParseTree._

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
  lexrule("Return", literal("return")) ++
  lexrule("Yield", literal("yield"))
  
val g_expr =
  rule("PrimitiveExpr", "Id", c => Id(c.Id.text)) ++
  rule("Int", "Nat", c => Integer(BigInt(c.Nat.text, 10))) ++
  rule("Int", "Minus Nat", c => Integer(-BigInt(c.Nat.text, 10))) ++  
  rule("PrimitiveExpr", "Nat", c => Integer(BigInt(c.Nat.text, 10))) ++
  rule("PrimitiveExpr", "RoundBracketOpen Expr RoundBracketClose", c => c.Expr.resultAs[Expr]) ++
  rule("PrimitiveExpr", "RoundBracketOpen ControlFlowExpr RoundBracketClose", 
      c => ControlFlowExpr(c.ControlFlowExpr.resultAs[ControlFlow])) ++
  rule("PrimitiveExpr", "True", c => Bool(true)) ++  
  rule("PrimitiveExpr", "False", c => Bool(false)) ++  
  rule("OrExpr", "OrExpr Or AndExpr", 
      c => BinaryOperation(Or, c.OrExpr.resultAs[Expr], c.AndExpr.resultAs[Expr])) ++
  rule("OrExpr", "AndExpr", _.AndExpr.result) ++
  rule("AndExpr", "AndExpr And NotExpr", 
      c => BinaryOperation(And, c.AndExpr.resultAs[Expr], c.NotExpr.resultAs[Expr])) ++
  rule("AndExpr", "NotExpr", _.NotExpr.result) ++
  rule("NotExpr", "Not NotExpr", c => UnaryOperation(Not, c.NotExpr.resultAs[Expr])) ++
  rule("NotExpr", "CmpExpr", _.CmpExpr.result) ++
  rule("CmpExpr", "CmpExpr CmpOp AddExpr", { c =>
    val operator = c.CmpOp.resultAs[CmpOperator]
    val operand = c.AddExpr.resultAs[Expr]
    c.CmpExpr.resultAs[Expr] match {
      case op : CmpOperation =>
        CmpOperation(op.operators :+ operator, op.operands :+ operand)
      case e =>
        CmpOperation(Vector(operator), Vector(e, operand))
    }
  }) ++
  rule("CmpExpr", "AddExpr", _.AddExpr.result) ++
  rule("CmpOp", "Le", c => Le) ++
  rule("CmpOp", "Gr", c => Gr) ++
  rule("CmpOp", "Leq", c => Leq) ++
  rule("CmpOp", "Geq", c => Geq) ++
  rule("CmpOp", "Equals", c => Eq) ++
  rule("CmpOp", "NEquals", c => NEq) ++
  rule("AddExpr", "AddExpr Plus NegExpr", c => BinaryOperation(Add, c.AddExpr.resultAs[Expr], c.NegExpr.resultAs[Expr])) ++
  rule("AddExpr", "AddExpr Minus NegExpr", c => BinaryOperation(Sub, c.AddExpr.resultAs[Expr], c.NegExpr.resultAs[Expr])) ++  
  rule("AddExpr", "NegExpr", _.NegExpr.result) ++
  rule("NegExpr", "Minus NegExpr", c => UnaryOperation(Neg, c.NegExpr.resultAs[Expr])) ++  
  rule("NegExpr", "MultExpr", _.MultExpr.result) ++  
  rule("MultExpr", "MultExpr Times BasicExpr", c => BinaryOperation(Mul, c.MultExpr.resultAs[Expr], c.BasicExpr.resultAs[Expr])) ++
  rule("MultExpr", "MultExpr Slash BasicExpr", c => BinaryOperation(Div, c.MultExpr.resultAs[Expr], c.BasicExpr.resultAs[Expr])) ++
  rule("MultExpr", "MultExpr Mod BasicExpr", c => BinaryOperation(Mod, c.MultExpr.resultAs[Expr], c.BasicExpr.resultAs[Expr])) ++
  rule("MultExpr", "BasicExpr", _.BasicExpr.result) ++
  rule("BasicExpr", "AppExpr", _.AppExpr.result) ++
  rule("AppExpr", "PrimitiveExpr", _.PrimitiveExpr.result) ++
  rule("AppExpr", "AppExpr PrimitiveExpr", c => App(c.AppExpr.resultAs[Expr], c.PrimitiveExpr.resultAs[Expr])) ++
  rule("LazyExpr", "OrExpr", _.OrExpr.result) ++
  rule("LazyExpr", "Lazy LazyExpr", c => Lazy(c.LazyExpr.resultAs[Expr])) ++ 
  rule("FunExpr", "Pattern Arrow Block", c => Fun(c.Pattern.resultAs[Pattern], c.Block.resultAs[Block])) ++
  rule("FunExpr", "LazyExpr", _.LazyExpr.result) ++
  rule("Expr", "FunExpr", _.FunExpr.result) ++
  rule("ExprList", "", c => Vector[Expr]()) ++
  rule("ExprList", "Expr", c => Vector[Expr](c.Expr.resultAs[Expr])) ++
  rule("ExprList", "ExprList Comma Expr", c => c.ExprList.resultAs[Vector[Expr]] :+ c.Expr.resultAs[Expr])
  
val g_do = 
  rule("STDo", "Do Block",
      CS.Indent("Do", "Block"),
      c => Do(c.Block.resultAs[Block])) ++
  rule("DoExpr", "Do Block",
      c => Do(c.Block.resultAs[Block]))      
  
val g_if =
  rule("STIf", "If Expr Then Block_1 Else Block_2", 
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
  rule("STIf", "If Expr Then Block",
      CS.and(
          CS.Indent("If", "Expr"), 
          CS.ifThenElse(CS.Line("If", "Then"), 
              CS.Indent("If", "Block"), 
              CS.and(
                  CS.Align("If", "Then"),
                  CS.Indent("Then", "Block")))),
      c => If(c.Expr.resultAs[Expr], c.Block.resultAs[Block], Block(Vector()))) ++
  rule("IfExpr", "If Expr Then Block_1 Else Block_2", 
      c => If(c.Expr.resultAs[Expr], c.Block_1.resultAs[Block], c.Block_2.resultAs[Block])) ++
  rule("IfExpr", "If Expr Then Block",
      c => If(c.Expr.resultAs[Expr], c.Block.resultAs[Block], Block(Vector())))
    
val g_while = 
  rule("STWhile", "While Expr Do Block",
      CS.and(
        CS.Indent("While", "Expr"),
        CS.ifThenElse(CS.Line("While", "Do"),
            CS.Indent("While", "Block"),
            CS.and(CS.Align("While", "Do"), CS.Indent("Do", "Block")))),
      c => While(c.Expr.resultAs[Expr], c.Block.resultAs[Block])) ++
  rule("WhileExpr", "While Expr Do Block",
      c => While(c.Expr.resultAs[Expr], c.Block.resultAs[Block]))
      
val g_for = 
  rule("STFor", "For Pattern In Expr Do Block",
      CS.and(
          CS.Indent("For", "Pattern"),
          CS.Indent("For", "In"),
          CS.Indent("For", "Expr"),
          CS.ifThenElse(CS.Line("For", "Do"),
              CS.Indent("For", "Block"),
              CS.and(CS.Align("For", "Do"), CS.Indent("Do", "Block")))),              
      c => For(c.Pattern.resultAs[Pattern], c.Expr.resultAs[Expr], c.Block.resultAs[Block])) ++
  rule("ForExpr", "For Pattern In Expr Do Block",
      c => For(c.Pattern.resultAs[Pattern], c.Expr.resultAs[Expr], c.Block.resultAs[Block]))

val g_match = 
  rule("STMatch", "Match Expr STMatchCases",
      CS.and(
          CS.Indent("Match", "Expr"),
          CS.or(CS.Line("Match", "STMatchCases"), CS.Align("Match", "STMatchCases"))),
      c => Match(c.Expr.resultAs[Expr], c.STMatchCases.resultAs[Vector[MatchCase]])) ++
  rule("STMatchCases", "STMatchCases STMatchCase", 
      CS.or(CS.Align("STMatchCases", "STMatchCase"), CS.Line("STMatchCases", "STMatchCase")),
      c => c.STMatchCases.resultAs[Vector[MatchCase]] :+ c.STMatchCase.resultAs[MatchCase]) ++
  rule("STMatchCases", "", c => Vector[MatchCase]()) ++
  rule("STMatchCase", "Case Pattern Arrow Block", 
      CS.and(
        CS.Indent("Case", "Pattern"),
        CS.SameLine("Pattern", "Arrow"),
        CS.Indent("Case", "Block")),
      c => MatchCase(c.Pattern.resultAs[Pattern], c.Block.resultAs[Block])) ++     
  rule("MatchExpr", "Match Expr MatchCases",
      c => Match(c.Expr.resultAs[Expr], c.MatchCases.resultAs[Vector[MatchCase]])) ++
  rule("MatchCases", "MatchCases MatchCase", 
      c => c.MatchCases.resultAs[Vector[MatchCase]] :+ c.MatchCase.resultAs[MatchCase]) ++
  rule("MatchCases", "", c => Vector[MatchCase]()) ++
  rule("MatchCase", "Case Pattern Arrow Block", 
      c => MatchCase(c.Pattern.resultAs[Pattern], c.Block.resultAs[Block]))      
      
val g_controlflow = 
  g_do ++ g_if ++ g_while ++ g_for ++ g_match ++
  rule("STControlFlow", "STDo", _.STDo.result) ++  
  rule("STControlFlow", "STIf", _.STIf.result) ++
  rule("STControlFlow", "STWhile", _.STWhile.result) ++
  rule("STControlFlow", "STFor", _.STFor.result) ++
  rule("STControlFlow", "STMatch", _.STMatch.result) ++
  rule("ControlFlowExpr", "DoExpr", _.DoExpr.result) ++  
  rule("ControlFlowExpr", "IfExpr", _.IfExpr.result) ++
  rule("ControlFlowExpr", "WhileExpr", _.WhileExpr.result) ++
  rule("ControlFlowExpr", "ForExpr", _.ForExpr.result) ++
  rule("ControlFlowExpr", "MatchExpr", _.MatchExpr.result) 
  
  
val g_pattern = 
  rule("Pattern", "Underscore", c => PAny) ++
  rule("Pattern", "Id", c => PId(c.Id.text)) ++
  rule("Pattern", "Int", c => PInt(c.Int.resultAs[Integer].value)) ++
  rule("Pattern", "True", c => PBool(true)) ++
  rule("Pattern", "False", c => PBool(false)) ++
  rule("OptPattern", "", c => None) ++
  rule("OptPattern", "Pattern", c => Some(c.Pattern.resultAs[Pattern]))

val g_val = 
  rule("ST", "Val Pattern Eq Block",
      CS.and(
          CS.Indent("Val", "Pattern"),
          CS.SameLine("Pattern", "Eq"),
          CS.or(CS.Line("Eq", "Block"), CS.Indent("Val", "Block"))),
      c => STVal(c.Pattern.resultAs[Pattern], c.Block.resultAs[Block]))

val g_assign = 
  rule("ST", "Pattern Eq Block",
      CS.and(
          CS.SameLine("Pattern", "Eq"),
          CS.Protrude("Pattern"),
          CS.or(CS.Line("Eq", "Block"), CS.Indent("Pattern", "Block"))),
      c => STAssign(c.Pattern.resultAs[Pattern], c.Block.resultAs[Block]))
  
val g_def =
  rule("ST", "Def DefCases",
      CS.Indent("Def", "DefCases"),
      c => STDef(c.DefCases.resultAs[Vector[DefCase]])) ++
  rule("DefCases", "", c => Vector[DefCase]()) ++
  rule("DefCases", "DefCases DefCase", 
      CS.Align("DefCases", "DefCase"),
      c => c.DefCases.resultAs[Vector[DefCase]] :+ c.DefCase.resultAs[DefCase]) ++
  rule("DefCase", "Id OptPattern Eq Block",
      CS.and(
          CS.Indent("Id", "OptPattern"),
          CS.or(CS.SameLine("OptPattern", "Eq"), CS.SameLine("Id", "Eq")),
          CS.Indent("Id", "Block")),
      c => DefCase(c.Id.text, c.OptPattern.resultAs[Option[Pattern]], c.Block.resultAs[Block]))
      
val g_return =
  rule("ST", "Return ExprList", CS.Indent("Return", "ExprList"), c => STReturn(c.ExprList.resultAs[Vector[Expr]]))
  
val g_yield = 
  rule("ST", "Yield ExprList", CS.Indent("Yield", "ExprList"), c => STYield(c.ExprList.resultAs[Vector[Expr]]))  
  
val g_statement = 
  g_val ++ g_assign ++ g_def ++ g_return ++ g_yield ++
  rule("Statement", "Expr", CS.Protrude("Expr"), c => STExpr(c.Expr.resultAs[Expr])) ++
  rule("Statement", "ST", _.ST.result) ++
  rule("Statement", "STControlFlow", c => STControlFlow(c.STControlFlow.resultAs[ControlFlow])) ++ 
  rule("Block", "", c => Block(Vector())) ++
  rule("Block", "Expr", CS.or(CS.Protrude("Expr"), CS.not(CS.First("Expr"))), 
      c => Block(Vector(STExpr(c.Expr.resultAs[Expr])))) ++
  rule("Block", "STControlFlow", c => Block(Vector(STControlFlow(c.STControlFlow.resultAs[ControlFlow])))) ++   
  rule("Block", "ST", c => Block(Vector(c.ST.resultAs[Statement]))) ++
  rule("Block", "Block1 Statement", CS.Align("Block1", "Statement"), 
    c => {
      val statements = c.Block1.resultAs[Block].statements
      val statement = c.Statement.resultAs[Statement]
      Block(statements :+ statement)
    }) ++
  rule("Block1", "Statement", c => Block(Vector(c.Statement.resultAs[Statement]))) ++
  rule("Block1", "Block1 Statement", CS.Align("Block1", "Statement"), 
    c => {
      val statements = c.Block1.resultAs[Block].statements
      val statement = c.Statement.resultAs[Statement]
      Block(statements :+ statement)
    }) 

val g_prog = 
  g_literals ++
  g_pattern ++
  g_expr ++
  g_statement ++
  g_controlflow ++
  rule("Prog", "Block", _.Block.result)
 
def parse(prog : String) {
  if (!g_prog.info.wellformed) {
    println("grammar errors:\n"+g_prog.info.errors)
    return
  }
  println("term: '"+prog+"'")
  val d = UnicodeDocument.fromString(prog)
  val g = g_prog.parser.parse(d, "Prog", 0)
  g match {
    case None => 
      println("Does not parse.")
    case Some((v, i)) => 
      if (v.isUnique && i == d.size) {
        println("Parsed successfully.")
        val result = Derivation.computeParseResult(g_prog, d, t => null, v)
        println("Result:\n"+result.result)
      } else if (i < d.size) {
        println("Parse error at token "+i)
      } else {
        println("Parsed successfully, but ambiguous parse tree.")       
      }
  }  
  println()
} 

def main(args : Array[String]) {
  parse("x - y == 10 < y <= z - 4")
  
  parse("not 2 * (x + 4) + y mod 7 or 2 and 3")
  
  parse("not x or y")
  
  parse("not not x or y")
  
  parse("- x + y")
  
  parse("- - x + y")
  
  parse("- x * y")
  
  parse("true or false")
  
  parse("f x")
  
  parse("f x y")
  
  parse("c * f x")
  
  parse("(c * f) x y z * d")
  
  parse("lazy lazy x + y")
  
  parse("3 * (x => _ => x + 10)")
  
  parse("""
3 * 4
  f x
 g y
h z
""")

  parse("""
if x < y then 1 - x else y * 3 
""")

  parse("""
if true then
    1
else
    2
""")

  parse("""
if true then
    1
else 
    if false then x else y
""")

  parse("""
if true then
  if false then
    1
  else
    2
""")

  parse("""
def 
  u = 10
  f x = 
    13  
    42
    return    
  v = u + 1
""")

  parse("""
val x = ((10 + 5) -
   y)
""")

  parse("""
match x 
case 1 => 2
case 2 => 3
case y => y + 2
      """)
      
  parse("match x case 1 => 2 case x => x * x")

  parse("val x = match x case 1 => 2 case x => x * x")
  
  parse("""
  def f = 10
  val u = 20
  u - f""")
  
  parse("""
  def 
    f = 10
  val 
    u = 20
  u - f""")
  
  parse("""
val x = 3 * (do
  def f = 10
  val u = 20
  u - f)""")

  
  parse("match x case 1 => match y case 2 => x*y")

  parse("match x case 1 => (match y) case 2 => x*y")

  parse("match x case 1 => (match y case 2 => x*y)")
  
  parse("""
      10
      yield
      yield 11, 12, 13
      yield 14
      return 15
""")

  parse("val x = return 1, 2, 3")
   
}
   
}