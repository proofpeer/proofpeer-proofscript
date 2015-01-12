package proofpeer.proofscript.naiveinterpreter

import proofpeer.proofscript.logic._
import proofpeer.proofscript.frontend._
import proofpeer.general.Bytes

object ExecutionEnvironment {

  final case class Fault(pos : SourcePosition, description : String, trace : Vector[(SourcePosition, SourceLabel)])

  sealed trait Theory {
    def namespace : Namespace
    def content : String
    def contentKey : Bytes
    def faults : Vector[Fault]
    def isFaulty : Boolean = !faults.isEmpty
  }

  sealed trait ScannedTheory extends Theory {
    def parents : Vector[Namespace]
  }

  sealed trait ParsedTheory extends ScannedTheory {
    def parseTree : ParseTree.Block
    def proofScriptVersion : String
  }

  sealed trait CompiledTheory extends ParsedTheory {
    def bytecode : Bytes
    def compileKey : Bytes
  }
  
}

trait ExecutionEnvironment {  

  import ExecutionEnvironment._

  def lookupTheory(namespace : Namespace) : Option[Theory]

  def addFaults(theory : Theory, faults : Vector[Fault]) : Theory

  def finishedScanning(theory : Theory, parents : Vector[Namespace]) : ScannedTheory

  def finishedParsing(theory : ScannedTheory, parseTree : ParseTree.Block, proofScriptVersion : String) : ParsedTheory

  def finishedCompiling(theory : ParsedTheory, bytecode : Bytes) : CompiledTheory

}