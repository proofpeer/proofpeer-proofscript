package proofpeer.proofscript.naiveinterpreter

import proofpeer.proofscript.logic.Namespace

class ConsoleInterpreterNotificationHandler(print : String => Unit) extends InterpreterNotificationHandler 
{
  private var _failed : Int = 0
  private var _succeeded : Int = 0
  private var _loaded : Int = 0
  
  private var ee : ExecutionEnvironment = null
  private var outputAlways : Set[Namespace] = null

  private def println(s : String) {
    print(s + "\n")
  }

  def initialize(_ee : ExecutionEnvironment, _outputAlways : Set[Namespace]) {
    ee = _ee
    outputAlways = _outputAlways
  }
  
  def displayErrors(theory : Namespace) {
    for (fault <- ee.lookupTheory(theory).get.faults) {
      print(fault.describe("  "))
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
      _succeeded = _succeeded + 1
      println("successfully compiled theory '" + theory + "'")
    } else {
      _failed = _failed + 1
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
    _failed = _failed + 1
  }

  def skippedTheoryWithFaultyParents(theory : Namespace) {
    println("skipping theory '" + theory + "' because one of its ancestor theories failed")
    _failed = _failed + 1
  }

  def loadedTheory(theory : Namespace) {
    _loaded = _loaded + 1
    if (outputAlways.contains(theory)) {
      println("loaded compiled theory '" + theory + "': ")
      displayOutput(theory)
    }
  }

  def failed : Int = _failed
  
  def succeeded : Int = _succeeded
  
  def loaded : Int = _loaded
  
  def total : Int = _loaded + _succeeded + _failed

}  
