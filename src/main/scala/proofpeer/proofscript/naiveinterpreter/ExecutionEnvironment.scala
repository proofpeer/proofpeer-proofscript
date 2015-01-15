package proofpeer.proofscript.naiveinterpreter

import proofpeer.proofscript.logic._
import proofpeer.proofscript.frontend._
import proofpeer.general.Bytes

object ExecutionEnvironment {

  final case class Fault(pos : SourcePosition, description : String, trace : Vector[(SourcePosition, SourceLabel)])

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
    def parents : Vector[Namespace]
    def compileKey : Bytes
    def proofscriptVersion : String
  }

  /** All parents of a compiled theory must be compiled. */
  trait CompiledTheory extends RootedTheory {
    def parseTree : ParseTree.Block
    def bytecode : Bytes
  }
  
}

trait ExecutionEnvironment {  

  import ExecutionEnvironment._

  def lookupTheory(namespace : Namespace) : Option[Theory]

  def allTheoriesIn(namespace : Namespace, recursive : Boolean) : Set[Namespace]

  def addFaults(theory : Theory, faults : Vector[Fault]) : Theory

  def finishedRooting(theory : Theory, parents : Vector[Namespace]) : RootedTheory

  def finishedCompiling(theory : RootedTheory, bytecode : Bytes) : CompiledTheory

}