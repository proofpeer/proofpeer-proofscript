package proofpeer.proofscript.vm

sealed trait StackElement 

trait Reference extends StackElement

trait CodePointer extends StackElement {
  def predecessor : CodePointer
  def successor : CodePointer
}

final class StackPointer(val sp : Long) extends StackElement

sealed abstract class Value 
object Value {
  case class INT(value : Long) extends Value with StackElement
  case class INTEGER(value : BigInt) extends Value
  case class CLOSURE(cp : CodePointer, gp : Reference) extends Value
  case class FUNCTION(cp : CodePointer, ap : Reference, gp : Reference) extends Value
  case class VECTOR(elements: Array[StackElement]) extends Value
}

trait Heap {
  def alloc(value : Value) : Reference
  def resolve(reference : Reference) : Value
  def update(reference : Reference, value : Value)
}

trait Stack {
  var SP : Long
  var FP : Long 
  
  def get(sp : Long) : StackElement
  def set(sp : Long, e : StackElement)
    
  def push(e : StackElement) { 
    SP = SP + 1
    set(SP, e)
  }
  
  def pop() : StackElement = {
    val r = get(SP)
    SP = SP - 1
    r
  } 
  
  def slide(q : Long, m : Long) {
    var i = SP - m - q + 1
    val j = i + m
    while (i < j) {
      set(i, get(i + q))
      i = i + 1
    }
    SP = SP - q
  }
  
  def size = SP + 1
  
}

trait ProgramStore {

  // set the CP to cp
  def goto(cp : CodePointer) { goto(cp, 0) }
  
  // set the CP to (cp + i)
  def goto(cp : CodePointer, i : Long)
  
  // reads the instruction at CP and increments CP
  def read() : Instruction
  
  // the current CP
  def CP : CodePointer

}

sealed abstract class Instruction {
  def execute(vm : RunVM) : Boolean 
}

final class Crash() extends RuntimeException("VM crashed")

trait VM {
  
  val stack : Stack
  val heap : Heap
  val programStore : ProgramStore
  var GP : Reference  
  
  final def resolve(delta : Long) : Value = {
    stack.get(stack.SP - delta) match {
      case e : Value.INT => e
      case r : Reference => heap.resolve(r)
      case _ => crash()
    }
  }
    
  final def pop() : Value = {
    stack.pop() match {
      case e : Value.INT => e
      case r : Reference => heap.resolve(r)
      case _ => crash()
    }
  }
    
  final def push(value : Value) = {
    value match {
      case i : Value.INT => stack.push(i)
      case _ => stack.push(heap.alloc(value))
    }
  }
  
  final def crash[T]() : T = {
    throw new Crash()
  }  

}

object Instruction {
  
  case object HALT extends Instruction {
    def execute(vm : RunVM) : Boolean = false
  }
  
  case object CRASH extends Instruction {
    def execute(vm : RunVM) : Boolean = vm.crash()
  }
  
  sealed case class LOADINT(i : Value.INT) extends Instruction {
    def execute(vm : RunVM) : Boolean = {
      vm.instrLOADINT(i)
      true
    }
  }
  
  sealed case class LOADINTEGER(i : Value.INTEGER) extends Instruction {
    def execute(vm : RunVM) : Boolean = {
      vm.instrLOADINTEGER(i)
      true
    }    
  }
    
  case object NEG extends Instruction {
    def execute(vm : RunVM) : Boolean = {
      vm.instrNEG()
      true
    }            
  }
  
  case object ADD extends Instruction {
    def execute(vm : RunVM) : Boolean = {
      vm.instrADD()
      true
    }               
  } 
  
  case object SUB extends Instruction {
    def execute(vm : RunVM) : Boolean = {
      vm.instrSUB()
      true
    }               
  } 
  
  case object MUL extends Instruction {
    def execute(vm : RunVM) : Boolean = {
      vm.instrMUL()
      true
    }               
  } 
  
  case object DIV extends Instruction {
    def execute(vm : RunVM) : Boolean = {
      vm.instrDIV()
      true
    }               
  } 
  
  case object MOD extends Instruction {
    def execute(vm : RunVM) : Boolean = {
      vm.instrMOD()
      true
    }               
  } 
  
  case object NOT extends Instruction {
    def execute(vm : RunVM) : Boolean = {
      vm.instrNOT()
      true
    }               
  } 

  case object AND extends Instruction {
    def execute(vm : RunVM) : Boolean = {
      vm.instrAND()
      true
    }               
  } 
  
  case object OR extends Instruction {
    def execute(vm : RunVM) : Boolean = {
      vm.instrOR()
      true
    }               
  } 
  
  case object EQUIV extends Instruction {
    def execute(vm : RunVM) : Boolean = {
      vm.instrEQUIV()
      true
    }               
  } 

  case object NEQUIV extends Instruction {
    def execute(vm : RunVM) : Boolean = {
      vm.instrNEQUIV()
      true
    }               
  } 
    
  case object EQ extends Instruction {
    def execute(vm : RunVM) : Boolean = {
      vm.instrEQ()
      true
    }               
  } 
  
  case object NEQ extends Instruction {
    def execute(vm : RunVM) : Boolean = {
      vm.instrNEQ()
      true
    }               
  } 
    
  case object LE extends Instruction {
    def execute(vm : RunVM) : Boolean = {
      vm.instrLE()
      true
    }               
  } 
  
  case object LEQ extends Instruction {
    def execute(vm : RunVM) : Boolean = {
      vm.instrLEQ()
      true
    }               
  } 
  
  case object GR extends Instruction {
    def execute(vm : RunVM) : Boolean = {
      vm.instrGR()
      true
    }               
  } 
  
  case object GEQ extends Instruction {
    def execute(vm : RunVM) : Boolean = {
      vm.instrGEQ()
      true
    }               
  } 
  
  case class JUMP(cp : CodePointer) extends Instruction {
    def execute(vm : RunVM) : Boolean = {
      vm.instrJUMP(cp)
      true
    }               
  } 
  
  case class JUMPZ(cp : CodePointer) extends Instruction {
    def execute(vm : RunVM) : Boolean = {
      vm.instrJUMPZ(cp)
      true
    }               
  } 
  
  case class JUMPI(cp : CodePointer) extends Instruction {
    def execute(vm : RunVM) : Boolean = {
      vm.instrJUMPI(cp)
      true
    }               
  } 
  
  case class PUSHLOC(n : Long) extends Instruction {
    def execute(vm : RunVM) : Boolean = {
      vm.instrPUSHLOC(n)
      true
    }
  }
  
  case class PUSHGLOB(n : Long) extends Instruction {
    def execute(vm : RunVM) : Boolean = {
      vm.instrPUSHGLOB(n)
      true
    }
  }
  
  // q is the number of elements to delete, m the number of elements to preserve on top
  // currently only m == 1 is used
  case class SLIDE(q : Long, m : Long) extends Instruction {
    def execute(vm : RunVM) : Boolean = {
      vm.instrSLIDE(q, m)
      true
    }
  }
  
  case object EVAL extends Instruction {
    def execute(vm : RunVM) : Boolean = {
        vm.instrEVAL()
        true
    }
  }
  
  case object MKVEC extends Instruction {
    def execute(vm : RunVM) : Boolean = {
      vm.instrMKVEC()
      true
    }
  }
  
  case class MKFUNVAL(cp : CodePointer) extends Instruction {
    def execute(vm : RunVM) : Boolean = {
      vm.instrMKFUNVAL(cp)
      true
    }
  }
  
  case class TARG(k : Long) extends Instruction {
    def execute(vm : RunVM) : Boolean = {
      vm.instrTARG(k)
      true
    }
  }
  
  case class RETURN(k : Long) extends Instruction {
    def execute(vm : RunVM) : Boolean = {
      vm.instrRETURN(k)
      true
    }
  }
  
  case class MARK(cp : CodePointer) extends Instruction {
    def execute(vm : RunVM) : Boolean = {
      vm.instrMARK(cp)
      true
    }
  }
  
  case object APPLY extends Instruction {
    def execute(vm : RunVM) : Boolean = {
      vm.instrAPPLY()
      true
    }    
  }
  
  case class ALLOC(n : Long) extends Instruction {
    def execute(vm : RunVM) : Boolean = {
      vm.instrALLOC(n)
      true
    }
  }

  case class REWRITE(j : Long) extends Instruction {
    def execute(vm : RunVM) : Boolean = {
      vm.instrREWRITE(j)
      true
    }
  }
  
  case class MKCLOS(cp : CodePointer) extends Instruction {
    def execute(vm : RunVM) : Boolean = {
      vm.instrMKCLOS(cp)
      true
    }    
  } 
  
  case object UPDATE extends Instruction {
    def execute(vm : RunVM) : Boolean = {
      vm.instrUPDATE()
      true
    }        
  }
  
}

trait RunVM extends VM {
  
  def run() {
    var instr : Instruction = null
    do {
      instr = programStore.read()
      //println("instruction = "+instr)
    } while (instr.execute(this))
  }
  
  import Value._
    
  private def pushi(i : BigInt) {
    if (i.isValidLong) 
      push(INT(i.toLong))
    else
      push(INTEGER(i))
  }
  
  private def popi() : BigInt = {
    pop() match {
      case INT(x) => x
      case INTEGER(x) => x
      case _ => crash()
    }
  }
  
  private def popb() : Boolean = {
    pop() match {
      case INT(x) => x != 0
      case INTEGER(x) => x != 0
      case _ => crash()
    }
  }
  
  private def pushb(b : Boolean) = {
    push(INT(if (b) 1 else 0))
  }
  
  final def instrNEG() {
    pushi(-popi())
  }
  
  final def instrADD() {
    pushi(popi() + popi())
  }
  
  final def instrSUB() {
    pushi(popi() - popi())
  }

  final def instrMUL() {
    pushi(popi() * popi())
  }
  
  final def instrDIV() {
    val x = popi()
    val y = popi()
    if (y == 0) crash() else pushi(x / y)
  }

  final def instrMOD() {
    val x = popi()
    val y = popi()
    if (y == 0) crash() else pushi(x % y)
  }
  
  final def instrNOT() {
    pushb(!popb())
  }
  
  final def instrAND() {
    val u = popb()
    val v = popb()
    pushb(u && v)
  }
  
  final def instrOR() {
    val u = popb()
    val v = popb()
    pushb(u || v)
  }  
  
  final def instrEQUIV() {
    pushb(popb() == popb())
  }
  
  final def instrNEQUIV() {
    pushb(popb() != popb())
  }
      
  final def instrLOADINT(i : INT) {
    push(i)
  }

  final def instrLOADINTEGER(i : INTEGER) {
    pushi(i.value)
  }
  
  final def instrJUMP(cp : CodePointer) {
    programStore.goto(cp)
  }
  
  final def instrJUMPZ(cp : CodePointer) {
    if (popi() == 0) programStore.goto(cp)
  }
  
  final def instrJUMPI(cp : CodePointer) {
    val x = popi()
    if (x.isValidLong) programStore.goto(cp, x.toLong)
    else crash()
  }
  
  final def instrEQ() {
    pushb(popi() == popi())
  }

  final def instrNEQ() {
    pushb(popi() != popi())
  }
  
  final def instrLE() {
    pushb(popi() < popi())
  }

  final def instrLEQ() {
    pushb(popi() <= popi())
  }

  final def instrGR() {
    pushb(popi() > popi())
  }
  
  final def instrGEQ() {
    pushb(popi() >= popi())
  }
  
  final def instrPUSHLOC(n : Long) {
    if (n < 0 || n > stack.SP)
      crash()
    else
      stack.push(stack.get(stack.SP - n))
  }
  
  final def instrPUSHGLOB(n : Long) {
    heap.resolve(GP) match {
      case VECTOR(elems) if n >= 0 && n < elems.length =>
        stack.push(elems(n.toInt))
      case _ => 
        crash()
    }   
  }
  
  final def instrSLIDE(q : Long, m : Long) {
    if (q < 0 || m < 0 || q + m > stack.size)
      crash()
    else {
      stack.slide(q, m)
    }
  }
    
  final def instrMKVEC() {
    val n = popi()
    if (n > stack.size)
      crash()
    else {
      var i = n.toInt
      val arr : Array[StackElement] = new Array(i)
      while (i > 0) {
        i = i - 1
        arr(i) = stack.pop()
      }
      stack.push(heap.alloc(Value.VECTOR(arr)))
    } 
  }
  
  private val empty_AP = VECTOR(Array())
  
  final def instrMKFUNVAL(cp : CodePointer) {
    resolve(0) match {
      case VECTOR(_) =>
        val gp = stack.pop().asInstanceOf[Reference]
        val ap = heap.alloc(empty_AP)
        val f = FUNCTION(cp, ap, gp)
        stack.push(heap.alloc(f))
      case _ => 
        crash()
    } 
  }
  
  final def microWRAP() {
    val ap : Reference = 
      stack.pop() match {
        case r : Reference => r
        case _ => crash()
      }
    val cp = programStore.CP.predecessor
    val f = FUNCTION(cp, ap, GP)
    stack.push(heap.alloc(f))
  }
  
  final def microPOPENV() {
    val result = stack.pop()
    stack.SP = stack.FP
    val cp = stack.pop().asInstanceOf[CodePointer]
    stack.FP = stack.pop().asInstanceOf[StackPointer].sp
    GP = stack.pop().asInstanceOf[Reference]
    stack.push(result)
    programStore.goto(cp) 
  }
  
  final def instrTARG(k : Long) {
    val n = stack.SP - stack.FP
    if (n < k) {
      pushi(n)
      instrMKVEC()
      microWRAP()
      microPOPENV()
    }
  }
  
  final def instrRETURN(k : Long) {
    val n = stack.SP - stack.FP - 1
    if (n <= k)
      microPOPENV()
    else {
      instrSLIDE(k, 1)
      instrEVAL()
      instrAPPLY()
    } 
      
  }
  
  final def instrMARK(cp : CodePointer) {
    stack.push(GP)
    stack.push(new StackPointer(stack.FP))
    stack.push(cp)
    stack.FP = stack.SP
  }
  
  final def instrAPPLY() {
    pop() match {
      case FUNCTION(cp, ap, gp) =>
        heap.resolve(ap) match {
          case VECTOR(args) =>
            for (arg <- args) stack.push(arg)
            GP = gp
            programStore.goto(cp)
          case _ => crash()
        }
      case _ => crash()  
    }
  }
    
  final def instrALLOC(n : Long) {
    var m = n
    while (m > 0) {
      stack.push(heap.alloc(CLOSURE(null, null)))
      m = m - 1
    }
  }
  
  final def instrREWRITE(j : Long) {
    val sp = stack.SP - j
    val value = pop()
    stack.get(sp) match {
      case r : Reference =>
        heap.update(r, value)
      case _ => crash()
    }
  }
  
  final def instrEVAL() {
    resolve(0) match {
      case CLOSURE(cp, gp) => 
        if (cp != null && gp != null) {
          instrMARK(programStore.CP)
          GP = gp
          programStore.goto(cp)
        } else
          crash()
      case _ =>
    }
  }  
  
  final def instrMKCLOS(cp : CodePointer) {
    resolve(0) match {
      case VECTOR(_) =>
        val gp = stack.pop().asInstanceOf[Reference]
        val c = CLOSURE(cp, gp)
        stack.push(heap.alloc(c))
      case _ => 
        crash()
    }     
  }
  
  final def instrUPDATE() {
    microPOPENV()
    instrREWRITE(1)
  }
  
}



