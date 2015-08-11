package proofpeer.proofscript.naiveinterpreter

import proofpeer.proofscript.frontend._

final case class Fault(pos : SourcePosition, description : String, trace : Vector[(SourcePosition, SourceLabel)] = Vector()) {
  def describe(prefix : String) : String = {
    def describePosition(pos : SourcePosition, label : SourceLabel) : String = {
      val labelDescr =
        label match {
          case NoSourceLabel => ""
          case _ => " (" + label +")"
        }
      if (pos == null) "unknown location" + labelDescr
      else {
        val theory = {
            val src = if (pos.source != null) pos.source.toString else "?"
            "in " + src
          }
        pos.span match {
          case None => 
            theory + " at unknown location" + labelDescr
          case Some(span) => 
            theory + " at row "+(span.firstRow + 1)+", column "+(span.leftMostFirst + 1) + labelDescr
        }
      }
    }
    if (trace.isEmpty) {
      val singlepos =
        if (pos != null)
          prefix + "  " + describePosition(pos, NoSourceLabel) + "\n"
        else 
          ""
      prefix + "* " + description + "\n" + singlepos
    } else {
      var output = new StringBuilder()
      output.append(prefix + "* " + description + "\n")
      for (pos <- trace) {
        output.append(prefix + "  "+describePosition(pos._1, pos._2) + "\n")
      }
      output.toString()
    }
  }
}