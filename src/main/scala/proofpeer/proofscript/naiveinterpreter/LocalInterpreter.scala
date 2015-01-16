package proofpeer.proofscript.naiveinterpreter

//import proofpeer.proofscript.frontend._
import proofpeer.proofscript.logic._


object LocalInterpreter {

  def main(args : Array[String]) {
    println("ProofScript v0.2-SNAPSHOT (c) 2014, 2015 University of Edinburgh")
    val ee = LocalExecutionEnvironment.create(args)
    val allTheories = ee.allTheoriesIn(Namespace("\\"), true)
    val rooting = new Rooting(ee)
    rooting.rootTheories(allTheories)
    for (namespace <- allTheories) {
      if (rooting.theoryIsRooted(namespace))
        println("Successfully rooted theory " + namespace + ".")
      else {
        println("Failure rooting theory " + namespace + ":")
        for (fault <- ee.lookupTheory(namespace).get.faults) {
          println("  * " + fault.description)
        }
      }    
    }
 
  }

}