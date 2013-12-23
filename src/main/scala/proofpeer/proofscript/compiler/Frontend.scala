package proofpeer.proofscript.compiler

sealed trait ParseTree {
  lazy val freeVars : Set[String] = calcFreeVars
  protected def calcFreeVars : Set[String]   
}

object ParseTree {
  
  sealed trait Expr extends ParseTree
  
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
  case class If(cond : Expr, thenCase : Expr, elseCase : Expr) extends Expr {
    protected def calcFreeVars = cond.freeVars ++ thenCase.freeVars ++ elseCase.freeVars
  }
  case class App(f : Expr, args : List[Expr]) extends Expr {
    protected def calcFreeVars = args.foldLeft(f.freeVars)(_ ++ _.freeVars)
  }
  case class Fun(params : List[String], body : Expr) extends Expr {
    protected def calcFreeVars = body.freeVars -- params.toSet
  }
  case class Lazy(expr : Expr) extends Expr {
    protected def calcFreeVars = expr.freeVars
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
}

object Parser {
  
import proofpeer.indent._
import proofpeer.indent.API._
import proofpeer.indent.APIConversions._

def ltokenrule(nonterminal : String, c1 : Char, c2 : Char) : Grammar = 
  tokenrule(nonterminal, Range.interval(c1, c2)) ++ lexical(nonterminal)
  
def ltokenrule(nonterminal : String, c : Char) : Grammar = ltokenrule(nonterminal, c, c)

import ParseTree._

val g_literals = 
  ltokenrule("LowerLetter", 'a', 'z') ++
  ltokenrule("UpperLetter", 'A', 'Z') ++
  lexrule("Letter", "UpperLetter") ++
  lexrule("Letter", "LowerLetter") ++  
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
  lexrule("False", literal("false")) 
  

import Derivation.Context  
  
val g_expr =
  rule("PrimitiveExpr", "Id", c => Id(c.Id.text)) ++
  rule("Int", "Nat", c => Integer(BigInt(c.Nat.text, 10))) ++
  rule("Int", "Minus Nat", c => Integer(-BigInt(c.Nat.text, 10))) ++  
  rule("PrimitiveExpr", "Nat", c => Integer(BigInt(c.Nat.text, 10))) ++
  rule("PrimitiveExpr", "RoundBracketOpen Expr RoundBracketClose", c => c.Expr.result) ++
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
  rule("BasicExpr", "PrimitiveExpr", _.PrimitiveExpr.result) ++
  rule("Expr", "OrExpr", _.OrExpr.result) 
  
val g_prog = 
  g_literals ++
  g_expr ++
  rule("Prog", "Expr", c => c.Expr.result)
 
  
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
        println("Ambiguous parse tree:\n"+Derivation.visualize(g_prog, v))       
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
}
  
  
}