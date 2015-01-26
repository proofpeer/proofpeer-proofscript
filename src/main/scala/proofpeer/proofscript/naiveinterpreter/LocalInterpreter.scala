package proofpeer.proofscript.naiveinterpreter

import proofpeer.proofscript.logic.Namespace

object LocalInterpreter {

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
    val handler = new ConsoleInterpreterNotificationHandler(print _)
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