package proofpeer.proofscript.naiveinterpreter

import proofpeer.indent.Span
import proofpeer.proofscript.logic.Namespace

sealed trait OutputKind
object OutputKind {
  case object SHOW extends OutputKind
  case object FAILURE extends OutputKind
}

trait Output {
  def add(namespace : Namespace, location : Option[Span], kind : OutputKind, output : String) 
}

object DefaultOutput extends Output {

  def add(namespace : Namespace, location : Option[Span], kind : OutputKind, output : String) {
    val slocation : String = 
      location match {
        case None => ""
        case Some(span) => ":" + (span.firstRow + 1)
      }
    val skind = 
      kind match {
        case OutputKind.SHOW => "show"
        case OutputKind.FAILURE => "failure intercepted"
      }
    println("** " + skind + " ("+namespace+slocation+"): " + output)
  }

}

object NullOutput extends Output {

  def add(namespace : Namespace, location : Option[Span], kind : OutputKind, output : String) {}

}

object Output {

  type Item = (Namespace, Option[Span], OutputKind, String)

  type Captured = Vector[Item]

}

class DefaultOutputCapture extends Output {

  import Output._

  private var outputs : List[Item] = List()

  def add(namespace : Namespace, location : Option[Span], kind : OutputKind, output : String) {
    outputs = (namespace, location, kind, output) :: outputs
  }

  def export() : Captured = outputs.reverse.toVector

}
