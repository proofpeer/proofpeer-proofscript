package proofpeer.proofscript.frontend

import proofpeer.indent.Span
import proofpeer.proofscript.logic.{Preterm, Namespace, Name}

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

  def mkId(name : Name) : Expr = {
    if (name.namespace.isDefined)
      QualifiedId(name.namespace.get, name.name.toString)
    else 
      Id(name.name.toString)
  }
  
  sealed trait Expr extends ParseTree {
    protected def calcFreeVars : Set[String]
    protected def calcVars = (calcFreeVars, Set())
  }

  case object NilExpr extends Expr {
    protected def calcFreeVars = Set()
  }
  
  case class Bool(value : Boolean) extends Expr {
    protected def calcFreeVars = Set()
  }
  
  case class Integer(value : BigInt) extends Expr {
    protected def calcFreeVars = Set()
  }

  case class StringLiteral(value : Vector[Int]) extends Expr {
    protected def calcFreeVars = Set()
  }
  
  case class QualifiedId(namespace : Namespace, name : String) extends Expr {
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

  case class Tuple(elements : Vector[Expr]) extends Expr {
    protected def calcFreeVars = elements.foldLeft(Set[String]())((x, y) => x ++ y.freeVars)
  }
    
  case class App(f : Expr, g : Expr) extends Expr {
    protected def calcFreeVars = f.freeVars ++ g.freeVars
  }
  
  case class Fun(param : Pattern, body : Block) extends Expr {
    protected def calcFreeVars = body.freeVars -- param.introVars ++ param.freeVars
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

  case class Do(block : Block, star : Boolean) extends ControlFlow {
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

  case class ContextControl(ctx : Option[Expr], body : Block) extends ControlFlow {
    protected def calcFreeVars = 
      if (ctx.isDefined) ctx.get.freeVars ++ body.freeVars else body.freeVars
  }

  sealed trait Operator extends TracksSourcePosition
 
  sealed trait UnaryOperator extends Operator 
  case object Neg extends UnaryOperator
  case object Not extends UnaryOperator

  sealed trait BinaryOperator extends Operator
  case object RangeTo extends BinaryOperator
  case object RangeDownto extends BinaryOperator
  case object Add extends BinaryOperator
  case object Sub extends BinaryOperator
  case object Mul extends BinaryOperator
  case object Div extends BinaryOperator
  case object Mod extends BinaryOperator
  case object And extends BinaryOperator
  case object Or extends BinaryOperator
  case object Prepend extends BinaryOperator
  case object Append extends BinaryOperator
  case object Concat extends BinaryOperator
  
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

  case class PString(value : Vector[Int]) extends Pattern {
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

  case class PTuple(elements : Vector[Pattern]) extends Pattern {
    protected def calcVars = {
      var frees : Set[String] = Set()
      var intros : Set[String] = Set()
      for (e <- elements) {
        frees = frees ++ e.freeVars
        intros = intros ++ e.introVars
      }
      (frees, intros)      
    }
  }

  case class PPrepend(x : Pattern, xs : Pattern) extends Pattern {
    protected def calcVars = {
      (x.freeVars ++ xs.freeVars, x.introVars ++ xs.introVars)
    }
  }

  case class PAppend(xs : Pattern, x : Pattern) extends Pattern {
    protected def calcVars = {
      (xs.freeVars ++ x.freeVars, xs.introVars ++ x.introVars)
    }
  }

  case class PIf(pat : Pattern, expr : Expr) extends Pattern {
    protected def calcVars = {
      val patIntros = pat.introVars
      (expr.freeVars -- patIntros, patIntros)
    }
  }

  case object PNil extends Pattern {
    protected def calcVars = (Set(), Set())
  }
  
  sealed trait Statement extends ParseTree
  
  case class STExpr(expr : Expr) extends Statement {
    protected def calcVars = (expr.freeVars, Set())
  }
  
  case class STControlFlow(controlflow : ControlFlow) extends Statement {
    protected def calcVars = (controlflow.freeVars, Set())    
  }

  case class STShow(expr : Expr) extends Statement {
    protected def calcVars = (expr.freeVars, Set())
  }

  case class STFail(expr : Option[Expr]) extends Statement {
    protected def calcVars = (if (expr.isDefined) expr.get.freeVars else Set(), Set())
  }
  
  case class STVal(pat : Pattern, body : Block) extends Statement {
    protected def calcVars = (pat.freeVars ++ body.freeVars, pat.introVars)
  }

  case class STValIntro(ids : List[Id]) extends Statement {
    protected def calcVars = (Set(), ids.map(_.name).toSet)
  }


  case class STAssign(pat : Pattern, body : Block) extends Statement {
    protected def calcVars = (pat.freeVars ++ body.freeVars, Set())
  }
  
  case class STDef(cases : Map[String, Vector[DefCase]]) extends Statement {
    protected def calcVars = {
      var names = Set[String]()
      var frees = Set[String]()
      for ((name, cs) <- cases) {
        names = names + name
        for (c <- cs) frees = frees ++ c.freeVars
      }
      (frees -- names, names)
    }
  }
    
  case class DefCase(name : String, param : Pattern, body : Block) extends ParseTree {
    protected def calcVars = (param.freeVars ++ (body.freeVars -- param.introVars), Set(name))
  }
  
  case class STReturn(expr : Expr) extends Statement {
    protected def calcVars = (expr.freeVars, Set())
  }

  case class STAssume(thm_name : Option[String], tm : Expr) extends Statement {
    protected def calcVars = 
      (tm.freeVars, 
       if (thm_name.isDefined) Set(thm_name.get) else Set())
  }
  
  case class STLet(result_name : Option[String], tm : Expr) extends Statement {
    protected def calcVars = 
      (tm.freeVars, 
       if (result_name.isDefined) Set(result_name.get) else Set())
  }

  case class STChoose(thm_name : Option[String], tm : Expr, thm : Expr) extends Statement {
    protected def calcVars = 
      (tm.freeVars ++ thm.freeVars, 
       if (thm_name.isDefined) Set(thm_name.get) else Set())
  }

  case class STTheory(namespace : Namespace, aliases : List[(Id, Namespace)], parents : List[Namespace]) extends Statement {
    protected def calcVars = (Set(), Set())
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