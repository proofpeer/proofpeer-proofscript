package proofpeer.proofscript.frontend

import proofpeer.indent.Span
import proofpeer.proofscript.logic.Preterm

trait Source {}

trait SourcePosition {
  def source : Source
  def span : Option[Span]
}

trait TracksSourcePosition {
  var sourcePosition : SourcePosition = null
}

sealed trait ParseTree extends TracksSourcePosition {
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

  case class LogicTerm(tm : Preterm) extends Expr {
    protected def calcFreeVars = {
      var fs : Set[String] = Set()
      for (q <- Preterm.listQuotes(tm)) {
        q.quoted match {
          case p : ParseTree => fs = fs ++ p.freeVars
          case _ => 
        }
      }
      fs
    }  
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

  sealed trait Operator extends TracksSourcePosition
 
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

  case class PLogic(tm : Preterm) extends Pattern {
    protected def calcVars = {
      var frees : Set[String] = Set()
      var intros : Set[String] = Set()
      for (q <- Preterm.listQuotes(tm)) {
        q.quoted match {
          case p : ParseTree => 
            frees = frees ++ p.freeVars
            intros = intros ++ p.introVars
          case _ => 
        }
      }
      (frees, intros)
    }
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
  
  case class STReturn(expr : Expr) extends Statement {
    protected def calcVars = (expr.freeVars, Set())
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