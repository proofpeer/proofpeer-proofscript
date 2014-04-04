package proofpeer.proofscript.compiler

import proofpeer.proofscript.vm._

class Compiler(builder : CodeBuilder) {
  
  import Expr._
  import Instruction._
  import Value._
  
  sealed trait Address { def z : Long }
  case class Local(z : Long) extends Address
  case class Global(z : Long) extends Address
  
  type Env = Map[String, Address]
  
  def compile(expr : Expr) : CodeBlock = {
    val code = builder.allocCodeBlock("Main")
    compile(true, Map(), 0, code, expr)
    code += HALT
    code
  }
  
  def getvar(evaluated : Boolean, env : Env, stacklevel : Long, code : CodeBlock, name : String) {
    env(name) match {
      case Local(z) => code += PUSHLOC(stacklevel - z)
      case Global(z) => code += PUSHGLOB(z)
    }
    if (evaluated) code += EVAL
  }
  
  def slide(code : CodeBlock, q : Long, m : Long) {
    if (code.size > 0) {
      code.instruction(code.size - 1) match {
        case SLIDE(p, n) if n <= m && n + p >= m =>
          code.replace(code.size - 1, SLIDE(q + p, n))
          return
        case _ =>
      }
    }
    code += SLIDE(q, m)
  }
  
  def captureGlobalVec(env : Env, stacklevel : Long, code : CodeBlock, expr : Expr) : Env = {
    val freeVars = expr.freeVars.toList
    var sl = stacklevel
    var funenv = env
    for (v <- freeVars) {
      getvar(false, env, sl, code, v)
      funenv = funenv + (v -> Global(sl - stacklevel))
      sl = sl + 1
    }
    code += LOADINT(INT(sl-stacklevel))
    code += MKVEC
    funenv
  }
  
  /**
   * compile does result in an INT or a ref to a value 
   * if evaluated is true, then the value may not be a closure
   */
  def compile(evaluated : Boolean, env : Env, stacklevel : Long, code : CodeBlock, expr : Expr) {
    expr match {
      case Integer(value) => 
        if (value.isValidLong)
          code += LOADINT(INT(value.toLong))
        else
          code += LOADINTEGER(INTEGER(value))
      case UnaryOperation(op, expr) =>
        compile(true, env, stacklevel, code, expr)
        op match {
          case Neg => code += NEG
          case Not => code += NOT
        }
      case BinaryOperation(op, left, right) =>
        compile(true, env, stacklevel, code, right)
        compile(true, env, stacklevel+1, code, left)
        op match {
          case Add => code += ADD
          case Sub => code += SUB
          case Mul => code += MUL
          case Div => code += DIV
          case Mod => code += MOD
          case Eq => code += EQ
          case NEq => code += NEQ
          case Le => code += LE
          case Leq => code += LEQ
          case Gr => code += GR
          case Geq => code += GEQ
        }
      case If(cond, thenExpr, elseExpr) =>
        compile(true, env, stacklevel, code, cond)
        var A : CodePointer = null
        var B : CodePointer = null
        code += JUMPZ(A)
        val jump_A = code.size - 1
        compile(evaluated, env, stacklevel, code, thenExpr)
        code += JUMP(B)
        val jump_B = code.size - 1
        A = code.ptr(code.size)
        compile(evaluated, env, stacklevel, code, elseExpr)
        B = code.ptr(code.size)
        code.replace(jump_A, JUMPZ(A))
        code.replace(jump_B, JUMP(B))
      case Var(name) =>
        getvar(evaluated, env, stacklevel, code, name)
      case Let(Definition(name, expr), body) =>
        compile(false, env, stacklevel, code, expr)
        compile(evaluated, env + (name -> Local(stacklevel+1)), stacklevel+1, code, body)
        slide(code, 1, 1)
      case Fun(params, body) =>
        var funenv = captureGlobalVec(env, stacklevel, code, expr)
        val funcode = builder.allocCodeBlock()
        code += MKFUNVAL(funcode.ptr(0))
        var i = 0
        for (x <- params) {
          funenv = funenv + (x -> Local(-i))
          i = i + 1
        }
        val k = params.length
        funcode += TARG(k)
        compile(false, funenv, 0, funcode, body)
        funcode += RETURN(k)        
      case App(f, args) =>
        var A : CodePointer = null
        code += MARK(A)
        val mark_A = code.size - 1
        var sl = stacklevel + 3
        for (arg <- args.reverse) {
          compile(false, env, sl, code, arg)
          sl = sl + 1
        }
        compile(true, env, sl, code, f)
        code += APPLY
        A = code.ptr(code.size)
        code.replace(mark_A, MARK(A))
        if (evaluated) code += EVAL
      case LetRec(definitions, body) =>
        val n = definitions.length
        code += ALLOC(n)
        var newenv = env
        var i = 0
        for (definition <- definitions) {
          i = i + 1
          newenv = newenv + (definition.name -> Local(stacklevel + i))
        }
        for (definition <- definitions) {
          compile(false, newenv, stacklevel + n, code, definition.expr)
          code += REWRITE(i)
          i = i - 1
        }
        compile(evaluated, newenv, stacklevel + n, code, body)
        code += SLIDE(n, 1)
      case Lazy(body : Expr) =>
        if (evaluated) {
          compile(true, env, stacklevel, code, body)
        } else {
          var closenv = captureGlobalVec(env, stacklevel, code, expr)
          val closcode = builder.allocCodeBlock()
          code += MKCLOS(closcode.ptr(0))
          compile(true, closenv, 0, closcode, body)
          closcode += UPDATE                 
        }
      case _ => throw new RuntimeException("cannot compile: " + expr)       
    }
  }

}

object Compiler {
  
  def compile(expr : Expr) : (ProgramStore, CodeBlock) = {
    val ps = new SimpleProgramStore()
    val compiler = new Compiler(ps)
    val codeblock = compiler.compile(expr)
    ps.goto(codeblock.ptr(0))
    (ps, codeblock)
  }
  
  def run(expr : Expr) : Value = {
    val (programStore, codeBlock) = compile(expr)
    val vm = new SimpleVM(programStore, 1000)
    vm.run
    if (vm.stack.SP != 0) 
      throw new RuntimeException("Wrong VM result state, SP = " + vm.stack.SP)
    else 
      vm.resolve(0)
  }
  
  def check(expr : Expr, expectedValue : Value) {
    val value = run(expr)
    if (value == expectedValue) {
      println("OK: expr = "+expr)
      println("    value = "+value)
    } else {
      println("FAIL: expr = " + expr)
      println("      value = " + value)
      println("      expected value = " + expectedValue)
    }
  }
  
  def crash(expr : Expr) {
    var value : Value = null
    var crashed : Boolean = false
    try {
      value = run(expr)
    } catch {
      case c: Crash => 
        crashed = true
    }
    if (crashed) {
      println("OK (crash): expr = "+expr)
    } else {
      println("FAIL (no crash): expr = " + expr)
      println("      value = " + value)
    }    
  }
  
  def bin(op : Expr.BinaryOperator, left : Expr, right : Expr) : Expr =
    Expr.BinaryOperation(op, left, right)    
    
  def un(op : Expr.UnaryOperator, expr : Expr) : Expr =
    Expr.UnaryOperation(op, expr)
    
  def let(name : String, expr : Expr, body : Expr) : Expr =
    Expr.Let(Expr.Definition(name, expr), body)
  
  def mainl(args : Array[String]) {
    import Expr._
    import Value._
    import scala.language.implicitConversions
    implicit def int2expr(i : Long) : Expr = Integer(i)
    implicit def str2expr(name : String) : Expr = Var(name)    
    check(42, INT(42))
    check(bin(Add, 2, If(3, bin(Sub, 4, 5), 0)), INT(1))
    check(let("a", 19, let("b", bin(Mul, "a", "a"), bin(Sub, "a", "b"))), INT(-342))
    check(let("a", 17, let("f", Fun(List("b"), bin(Add, "a", "b")), App("f", List(42)))), INT(59))
    val f = Definition("f", Fun(List("x", "y"), If(bin(Leq, "y", 1), "x", 
        App("f", List(bin(Mul, "x", "y"), bin(Sub, "y", 1))))))
    val g = Definition("g", Fun(List("x"), App("f", List(1, "x")))) 
    check(LetRec(List(f, g), App("g", List(10))), INT(3628800))
    check(LetRec(List(g, f), App("g", List(10))), INT(3628800))
    check(Lazy(23), INT(23))
    check(Lazy(Lazy(23)), INT(23)) 
    val a = Definition("a", "b")
    val la = Definition("a", Lazy("b"))
    val b = Definition("b", 10)
    check(LetRec(List(b, a), "a"), INT(10))
    crash(LetRec(List(a, b), "a"))
    check(LetRec(List(la, b), "a"), INT(10))
  }
    
}


