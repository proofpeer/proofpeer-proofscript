package proofpeer.proofscript.naiveinterpreter

import proofpeer.proofscript.logic.Namespace

object LocalInterpreter {

  class ConsoleInterpreterNotificationHandler(ee : ExecutionEnvironment) extends InterpreterNotificationHandler {
    var failed : Int = 0
    def displayErrors(theory : Namespace) {
      for (fault <- ee.lookupTheory(theory).get.faults) {
        println("  * " + fault.description)
      }
    }
    def startCompiling(theory : Namespace) {
      print("start compiling theory '" + theory + "' ...")
    }
    def finishedCompiling(theory : Namespace, success : Boolean)  {
      if (success) {
        println(" done")
      } else {
        failed = failed + 1
        println(" failed:")
        displayErrors(theory)
      }
    } 
    def skippedFaultyTheory(theory : Namespace) {
      println("skipping theory '" + theory + "' because it contains errors:")
      displayErrors(theory)
      failed = failed + 1
    }
    def skippedTheoryWithFaultyParents(theory : Namespace) {
      println("skipping theory '" + theory + "' because one of its ancestor theories failed")
      failed = failed + 1
    }
  }  

  def main(args : Array[String]) {
    println("ProofScript v0.2-SNAPSHOT (c) 2014, 2015 University of Edinburgh")
    val compileDir = new java.io.File("/Users/stevenobua/proofscript.compiled")
    val (ee, allTheories) = LocalExecutionEnvironment.create(compileDir, args)
    val interpreter = new Interpreter(ee)
    val handler = new ConsoleInterpreterNotificationHandler(ee)
    interpreter.compileTheories(allTheories, handler)
    println("")
    if (handler.failed == 0)
      println("All theories compile successfully.")
    else
      println("There are " + handler.failed + " theories which fail to compile.")
  }

}