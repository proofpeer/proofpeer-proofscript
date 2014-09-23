package proofpeer.proofscript.frontend

import proofpeer.indent._
import proofpeer.indent.APIConversions._
import java.io._


object Parser {

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

  val scriptGrammar = new ProofScriptGrammar(annotate)
  import scriptGrammar._
    
  def parse(prog : String) {
    if (!g_prog.info.wellformed) {
      println("grammar errors:\n"+g_prog.info.errors)
      return
    }
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
  } 

  sealed trait ParseResult
  case class SuccessfulParse(tree : ParseTree.Block) extends ParseResult 
  case class AmbiguousParse(pos : SourcePosition) extends ParseResult
  case class FailedParse(pos : SourcePosition) extends ParseResult

  def parseFromSource(source : Source, prog : String) : ParseResult = {
    currentSource = source
    if (!g_prog.info.wellformed) {
      throw new RuntimeException("ProofScript grammar is not wellformed:\n" + g_prog.info.errors)
    } 
    val document = UnicodeDocument.fromString(prog)
    g_prog.parser.parse(document, "Prog", 0) match {
      case None => FailedParse(new SourcePos(None))
      case Some((v, i)) =>
        if (v.isUnique && i == document.size) {
          val result = Derivation.computeParseResult(g_prog, document, t => null, v)
          SuccessfulParse(result.resultAs[ParseTree.Block])
        } else if (i < document.size) {
          val token = document.getToken(i)
          FailedParse(new SourcePos(Some(token.span)))
        } else {
          AmbiguousParse(new SourcePos(None))
        }
    }
  }

  def printLexicals(g : API.Grammar) {
    import API._
    var numLexicals : Int = 0
    var normallyScoped : Int = 0
    for (ann <- g.annotations) {
      ann match {
        case Lexical(n, LexicalPriority(scope, prio)) =>
          numLexicals += 1
          if (scope == 0) normallyScoped += 1
          println("  lexical " + n + " => " + prio)
      }
    }
    println("number of lexicals: " + numLexicals)
    println("normally scoped: " + normallyScoped)
  }

  def parseFromSourceNew(source : Source, prog : String) {
    val t1 = System.currentTimeMillis
    currentSource = source
    if (!g_prog.info.wellformed) {
      throw new RuntimeException("ProofScript grammar is not wellformed:\n" + g_prog.info.errors)
    } 
    for (rule <- g_prog.rules) {
      for (s <- rule.rhs) {
        if (s.ignore_layout) println("ignore layout of: " + rule.lhs + " -> " + s)
      }
    }
    printLexicals(g_prog)
    val document = UnicodeDocument.fromString(prog)
    println("size of document: " + document.size)
    g_prog.recognizer.parse(document, "Prog", 0) match {
      case None => 
        println("parsing failed")
      case Some((v, i)) =>
        if (v.unique && i == document.size) {
          println("parsing succeeded")
        } else if (i < document.size) {
          println("couldn't parse all of it")
        } else {
          println("amiguous parse")
        }
    }
    val t2 = System.currentTimeMillis
    println("time needed: " + (t2 - t1) + "ms")
    import proofpeer.indent.earley.Recognizer._
    import proofpeer.indent.earley.Measurements._
    println("number of blackboxcalls: " + blackboxCalls)
    println("maxduration: " + maxduration)
    println("totalduration: " + totalduration)
    println("totalFinalvalues: " + totalFinalvalues)
    println("number of item additions: " + numAdditions)
    println("average cost of item additions: " + (addingCost / numAdditions))
  }


  def read(f : File) : String = {
    val source = scala.io.Source.fromFile(f)
    val lines = source.mkString
    source.close()    
    lines
  }

  def chunkify(prog : String) : Vector[String] = {
    import proofpeer.scala.lang._
    val lines = split(prog, "\n")
    var chunks : Vector[String] = Vector()
    var chunk : String = ""
    for (line <- lines) {
      if (line.startsWith(" ") || line == "")
        chunk = chunk + line + "\n"
      else {
        chunks = chunks :+ chunk
        chunk = line
      }
    }
    chunks :+ chunk
  }

  def standard(source : Source, prog : String) {
    val t1 = System.currentTimeMillis
    val result = parseFromSource(source, prog)
    val t2 = System.currentTimeMillis
    println("parsed in " + (t2 - t1) + "ms")    
  }

  def chunkified(source : Source, prog : String) {
    val t1 = System.currentTimeMillis
    val chunks = chunkify(prog)
    for (chunk <- chunks) {
      println("------------------------------------------")
      println(chunk)
      parseFromSource(source, chunk)
    }
    val t2 = System.currentTimeMillis
    println("chunkified and parsed in " + (t2 - t1) + "ms")    
  }

  def main(args : Array[String]) {
    //val f = new File("/Users/stevenobua/myrepos/proofpeer-proofscript/scripts/bootstrap/conversions.thy")
    val f = new File("/Users/stevenobua/myrepos/proofpeer-hollight/proofscript/Lib.thy")
    val source = new proofpeer.proofscript.naiveinterpreter.Interpreter.FileSource(f)
    val prog = read(f)
    //standard(source, prog) // parsed in 262389ms
    parseFromSourceNew(source, prog)
  }

}

