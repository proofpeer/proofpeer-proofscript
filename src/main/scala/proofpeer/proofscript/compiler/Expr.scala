package proofpeer.proofscript.compiler

sealed trait Expr {
  lazy val freeVars : Set[String] = calcFreeVars
  protected def calcFreeVars : Set[String] 
}

object Expr {
  case class Integer(value : BigInt) extends Expr {
    protected def calcFreeVars = Set()
  }
  case class Var(name : String) extends Expr {
    protected def calcFreeVars = Set(name)
  }
  case class UnaryOperation(op : UnaryOperator, expr : Expr) extends Expr {
    protected def calcFreeVars = expr.freeVars
  }
  case class BinaryOperation(op : BinaryOperator, left : Expr, right : Expr) extends Expr {
    protected def calcFreeVars = left.freeVars ++ right.freeVars
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
  case class Definition(name : String, expr : Expr) 
  case class Let(definition : Definition, body : Expr) extends Expr {
    protected def calcFreeVars = definition.expr.freeVars ++ (body.freeVars - definition.name)
  }
  case class LetRec(definitions : List[Definition], body : Expr) extends Expr {
    protected def calcFreeVars : Set[String] = {
      val names = definitions.map(_.name).toSet
      definitions.foldLeft(body.freeVars)(_ ++ _.expr.freeVars) -- names
    }
  }
  case class Lazy(expr : Expr) extends Expr {
    protected def calcFreeVars = expr.freeVars
  }
 
  sealed trait UnaryOperator 
  case object Neg extends UnaryOperator
  case object Not extends UnaryOperator

  sealed trait BinaryOperator
  case object Add extends BinaryOperator
  case object Sub extends BinaryOperator
  case object Mul extends BinaryOperator
  case object Div extends BinaryOperator
  case object Mod extends BinaryOperator
  case object Eq extends BinaryOperator
  case object NEq extends BinaryOperator
  case object Le extends BinaryOperator
  case object Leq extends BinaryOperator
  case object Gr extends BinaryOperator
  case object Geq extends BinaryOperator  
}

