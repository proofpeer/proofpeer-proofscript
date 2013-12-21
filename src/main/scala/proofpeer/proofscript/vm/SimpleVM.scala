package proofpeer.proofscript.vm

final class SimpleReference(var value : Value) extends Reference

final class SimpleCodePointer(val codeblock : Int, val index : Long) extends CodePointer {
  def predecessor : CodePointer = new SimpleCodePointer(codeblock, index - 1)
  def successor : CodePointer = new SimpleCodePointer(codeblock, index + 1)
}

final class SimpleHeap extends Heap {
  def alloc(value : Value) : Reference = new SimpleReference(value)
  def resolve(reference : Reference) : Value = reference.asInstanceOf[SimpleReference].value
  def update(reference : Reference, value : Value) {
    val s : SimpleReference = reference.asInstanceOf[SimpleReference]
    s.value = value
  }
}

final class SimpleStack(initialSize : Int) extends Stack {
  
  private var _sp : Long = -1
  private var _fp : Long = -1  
  private var stack : Array[StackElement] = new Array(initialSize)
  
  def SP : Long = _sp
  def SP_= (sp : Long) {
    _sp = sp
    if (sp >= stack.length) {
      var size : Int = sp.asInstanceOf[Int]
      size = (size+2) * 2
      val newstack : Array[StackElement] = new Array(size)
      val oldsize = stack.size
      var i = 0
      while (i < oldsize) { 
        newstack(i) = stack(i)
        i = i + 1
      }
    }
  }

  def FP : Long = _fp
  def FP_= (fp : Long) {
    if (fp > _sp) throw new RuntimeException("FP > SP is not allowed")
    else _fp = fp
  }
  
  def get(sp : Long) : StackElement = {
    if (sp <= _sp) 
      stack(sp.toInt)
    else
      throw new RuntimeException("Invalid stack access (get) at " + sp + " > SP = " + _sp)
  }
  
  def set(sp : Long, e : StackElement) {
    if (sp <= _sp) 
      stack(sp.toInt) = e
    else
      throw new RuntimeException("Invalid stack access (set) at " + sp + " > SP = " + _sp)    
  }
  
}

class CodeBlock(val id : Int, val description : Option[String]) {
  
  private var _instructions : Vector[Instruction] = Vector()
    
  def += (instr : Instruction) {
    _instructions = _instructions :+ instr
  }
  
  def ++=(instructions : Vector[Instruction]) {
    for (instr <- instructions) this += instr
  }  

  def replace(index : Long, instruction : Instruction) {
    _instructions = _instructions.patch(index.toInt, List(instruction), 1)
  }  
  
  def ptr(index : Long) : CodePointer = new SimpleCodePointer(id, index)
    
  def instruction(index : Long) : Instruction = _instructions(index.toInt)
    
  def size : Long = _instructions.size
  
}

trait CodeBuilder {
  
  def allocCodeBlock(description : Option[String]) : CodeBlock 

  def allocCodeBlock() : CodeBlock = allocCodeBlock(None)
  
  def allocCodeBlock(description : String) : CodeBlock = allocCodeBlock(Some(description))
  
}

final class SimpleProgramStore extends ProgramStore with CodeBuilder {
  
  private var codeblocks : Vector[CodeBlock] = Vector()
  
  def allocCodeBlock(description : Option[String]) : CodeBlock = {
    val id = codeblocks.size
    val cb = new CodeBlock(id, description)
    codeblocks = codeblocks :+ cb 
    cb
  }
  
  private var currentCodeBlock : CodeBlock = null
  private var currentIndex : Long = -1
  
  def goto(cp : CodePointer, i : Long) {
    val scp : SimpleCodePointer = cp.asInstanceOf[SimpleCodePointer]
    if (currentCodeBlock == null || currentCodeBlock.id != scp.codeblock)
      currentCodeBlock = codeblocks(scp.codeblock)
    currentIndex = scp.index + i
  }
  
  def read() : Instruction = {
    val instr = currentCodeBlock.instruction(currentIndex)
    currentIndex = currentIndex + 1
    instr    
  }
  
  def CP : CodePointer = currentCodeBlock.ptr(currentIndex)

}

class SimpleVM(ps : ProgramStore, val initialStackSize : Int) extends RunVM {
  
  val stack = new SimpleStack(initialStackSize)
  
  val heap = new SimpleHeap()
  
  val programStore = ps
  
  var GP = heap.alloc(Value.VECTOR(Array()))
  
}

object SimpleVM {
  
  def create() : SimpleVM = new SimpleVM(new SimpleProgramStore(), 1000)
  
}