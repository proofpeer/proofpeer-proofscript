package proofpeer.proofscript.naiveinterpreter

import proofpeer.proofscript.logic._
import proofpeer.proofscript.frontend._
import proofpeer.general.Bytes

object ExecutionEnvironment {

  type OutputItem = (SourcePosition, OutputKind, String)

  trait Theory {
    def namespace : Namespace
    def source : Source
    def content : String
    def contentKey : Bytes
    def faults : Vector[Fault]
    def isFaulty : Boolean = !faults.isEmpty
  }

  /** For a rooted theory it is guaranteed that the theory and all of its ancestors are rooted, and
    * form a DAG with \root as its only node without a parent. */
  trait RootedTheory extends Theory {
    def parents : Set[Namespace]
    def aliases : Aliases
    def compileKey : Bytes
    def proofscriptVersion : String
  }

  /** All parents of a compiled theory must be compiled. */
  trait CompiledTheory extends RootedTheory {
    def state : State
  }
  
}

trait ExecutionEnvironment {  

  import ExecutionEnvironment._

  def kernel : Kernel

  def lookupTheory(namespace : Namespace) : Option[Theory]

  def addFaults(namespace : Namespace, faults : Vector[Fault]) : Theory

  def finishedRooting(namespace : Namespace, parents : Set[Namespace], aliases : Aliases, proofscriptVersion : Option[String]) : RootedTheory

  def finishedCompiling(namespace : Namespace, state : State) : CompiledTheory

  def storeOutput(compileKey : Bytes, capturedOutput : Output.Captured)

  def loadOutput(compileKey : Bytes) : Option[Output.Captured]

  def loadOutput(namespace : Namespace) : Option[Output.Captured] = {
    lookupTheory(namespace) match {
      case Some(thy : RootedTheory) => loadOutput(thy.compileKey)
      case _ => None
    }
  }

}
