package proofpeer.proofscript.frontend

object Parser {

import proofpeer.indent._

var currentSource : Source = null

class SourcePos(val span : Option[Span]) extends SourcePosition {
  val src = currentSource
  def source : Source = src
}

def annotate(v : Any, span : Option[Span]) : Any = {
  if (v != null && v.isInstanceOf[TracksSourcePosition]) {
    val w = v.asInstanceOf[TracksSourcePosition]
    w.sourcePosition = new SourcePos(span)
  }
  v
}

val earleyAutomaton : earley.EarleyAutomaton = {
  println("Initializing parser ...")
  val grammar = new ProofScriptGrammar(annotate).g_prog
  if (!grammar.isWellformed) {
    val errors = grammar.errors
    println("The ProofScript grammar contains " + errors.size + " errors: ")
    for (i <- 1 to errors.size) {
      println ("" + i +") " + errors(i - 1))
    }
    println("")
    null
  } else {
    val automaton = new earley.EarleyAutomaton(grammar)
    println("Parser is initialized.")
    automaton
  }
}

val earleyParser : earley.Earley = new earley.Earley(earleyAutomaton)
  
/*def parse(prog : String) {
  println("term: '"+prog+"'")
  val d = UnicodeDocument.fromString(prog)
  val g = g_prog.parser.parse(d, "Prog", 0)
  g match {
    case None => 
      println("Does not parse.")
    case Some((v, i)) => 
      if (v.isUnique && i == d.size) {
        println("Parsed successfully.")
        val result = Derivation.computeParseResult(g_prog, d, t => null, v)
        println("Result:\n"+result.result)
      } else if (i < d.size) {
        println("Parse error at token "+i)
      } else {
        println("Parsed successfully, but ambiguous parse tree.")       
      }
  }  
  println()
} */

sealed trait ParseResult
case class SuccessfulParse(tree : ParseTree.Block) extends ParseResult 
case class AmbiguousParse(pos : SourcePosition) extends ParseResult
case class FailedParse(pos : SourcePosition) extends ParseResult

def sourcepos(document : Document, start : Int, end : Int) : SourcePos = {
  val e = if (end >= document.size) document.size - 1 else end
  val s = if (start >= e) e else start 
  if (s < 0) return new SourcePos(None)
  val (row, col, _) = document.character(s)
  val (_, firstCol, _) = document.character(document.firstPositionInRow(row))
  val span = Span(firstCol, row, col, s, e - s + 1)
  new SourcePos(Some(span))
}

def parseFromSource(source : Source, prog : String) : ParseResult = {
  currentSource = source
  val document = Document.fromString(prog)
  val PROG = earleyAutomaton.idOfTerminal("Prog")
  earleyParser.parse(document, "Prog") match {
    case Right(i) => FailedParse(sourcepos(document, i, i))
    case Left(parsetree) =>
      if (parsetree.hasAmbiguities) {
        val span = parsetree.ambiguities.head.span
        AmbiguousParse(new SourcePos(if (span == null) None else Some(span)))
      } else {
        SuccessfulParse(parsetree.getValue)
      }
  }
}

  
}