package proofpeer.proofscript.naiveinterpreter

//import proofpeer.proofscript.frontend._
import proofpeer.proofscript.logic._
import proofpeer.proofscript.frontend.ProofScriptParser


object LocalInterpreter {

  def main(args : Array[String]) {
    println("ProofScript v0.2-SNAPSHOT (c) 2014, 2015 University of Edinburgh")
    val ee = LocalExecutionEnvironment.create(args)
    val allTheories = ee.allTheoriesIn(Namespace("\\"), true)
    val parser = new ProofScriptParser()
    val interpreter = new Interpreter(ee)
    interpreter.rootTheories(allTheories)
    interpreter.compileTheories(allTheories)
    var successful = 0
    var failed = 0
    for (namespace <- allTheories) {
      if (interpreter.theoryIsCompiled(namespace)) {
        successful = successful + 1
        println("Successfully compiled theory " + namespace + ".")
      } else {
        failed = failed + 1
        println("Failure compiling theory " + namespace + ":")
        for (fault <- ee.lookupTheory(namespace).get.faults) {
          println("  * " + fault.description)
        }
      }    
    }
    println("")
    println("Compiling succeeded for " + successful + " theories and failed for " + failed + " theories.")
  }

}