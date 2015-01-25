package proofpeer.proofscript.naiveinterpreter

import proofpeer.proofscript.logic.Namespace

object LocalInterpreter {

  class ConsoleInterpreterNotificationHandler() extends InterpreterNotificationHandler 
  {
    var failed : Int = 0
    var succeeded : Int = 0
    var loaded : Int = 0
    
    var ee : ExecutionEnvironment = null
    var outputAlways : Set[Namespace] = null

    def initialize(_ee : ExecutionEnvironment, _outputAlways : Set[Namespace]) {
      ee = _ee
      outputAlways = _outputAlways
    }
    
    def displayErrors(theory : Namespace) {
      for (fault <- ee.lookupTheory(theory).get.faults) {
        println("  * " + fault.description)
      }
    }

    def displayOutput(theory : Namespace) {
      ee.loadOutput(theory) match {
        case Some(output) if !output.isEmpty =>
          for (item <- output) {
            println("  " + Output.itemToString(item))
          }
        case _ => println("  no output")
      }
    }

    def startCompiling(theory : Namespace) {
      println("start compiling theory '" + theory + "' ...")
    }

    def finishedCompiling(theory : Namespace, success : Boolean)  {
      displayOutput(theory)
      if (success) {
        succeeded = succeeded + 1
        println("successfully compiled theory '" + theory + "'")
      } else {
        failed = failed + 1
        println("failed compiling theory '" + theory + "':")
        displayErrors(theory)
      }
    }

    def skippedFaultyTheory(theory : Namespace) {
      if (outputAlways.contains(theory)) {
        println("compiling theory '" + theory + "' failed:")
        displayOutput(theory)
        println("skipping theory '" + theory + "' because it contains errors:")
        displayErrors(theory)
      } else {
        println("skipping theory '" + theory + "' because it contains errors:")
        displayErrors(theory)
      }
      failed = failed + 1
    }

    def skippedTheoryWithFaultyParents(theory : Namespace) {
      println("skipping theory '" + theory + "' because one of its ancestor theories failed")
      failed = failed + 1
    }

    def loadedTheory(theory : Namespace) {
      loaded = loaded + 1
      if (outputAlways.contains(theory)) {
        println("loaded compiled theory '" + theory + "': ")
        displayOutput(theory)
      }
    }

    def total : Int = loaded + succeeded + failed
  }  

  def main(args : Array[String]) {
    println("ProofScript v0.2-SNAPSHOT (c) 2014, 2015 University of Edinburgh")
    val compileDir = new java.io.File(System.getProperty("java.io.tmpdir"), "proofscript.compiled")
    println("The directory for storing compiled theories is: " + compileDir)
    var loaded = 0
    val bang = args.indexOf("!")
    val (sources : Vector[String], namespaces : Set[Namespace]) = 
      if (bang < 0) 
        (args.toVector, Set())
      else 
        (args.take(bang).toVector, args.drop(bang + 1).map(x => Namespace(x).absolute).toSet)
    val handler = new ConsoleInterpreterNotificationHandler()
    val (ee, allTheories) = LocalExecutionEnvironment.create(compileDir, sources, handler.loadedTheory _)
    val (theoriesToCompile : Set[Namespace], outputAlways : Set[Namespace]) = 
      if (namespaces.isEmpty) 
        (allTheories, Set())
      else {
        val theories = 
          allTheories.filter(t => namespaces.exists(n => n.isAncestorOf(t)))
        (theories, theories)
      }
    val interpreter = new Interpreter(ee)
    handler.initialize(ee, outputAlways)
    interpreter.compileTheories(theoriesToCompile, handler)
    println("")
    if (handler.failed == 0)
      println("All " + handler.total + " theories compile successfully.")
    else
      println("There are " + handler.failed + " out of " + handler.total + " theories which fail to compile.")
  }

}