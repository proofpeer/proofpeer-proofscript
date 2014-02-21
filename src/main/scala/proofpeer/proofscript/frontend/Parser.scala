package proofpeer.proofscript.frontend

object Parser {

import proofpeer.indent._
import proofpeer.indent.APIConversions._

class SourcePos(val span : Option[Span]) extends SourcePosition {
  def source : Source = null
}

def annotate(v : Any, span : Option[Span]) : Any = {
  if (v != null && v.isInstanceOf[TracksSourcePosition]) {
    val w = v.asInstanceOf[TracksSourcePosition]
    w.sourcePosition = new SourcePos(span)
  }
  v
}

val scriptGrammar = new ScriptGrammar(annotate)
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

def main(args : Array[String]) {
  parse("x - y == 10 < y <= z - 4")
  
  parse("not 2 * (x + 4) + y mod 7 or 2 and 3")
  
  parse("not x or y")
  
  parse("not not x or y")
  
  parse("- x + y")
  
  parse("- - x + y")
  
  parse("- x * y")
  
  parse("true or false")
  
  parse("f x")
  
  parse("f x y")
  
  parse("c * f x")
  
  parse("(c * f) x y z * d")
  
  parse("lazy lazy x + y")
  
  parse("3 * (x => _ => x + 10)")
  
  parse("""
return 3 * 4
  f x
 g y
h z
""")

  parse("""
if x < y then 1 - x else y * 3 
""")

  parse("""
if true then
    1
else
    2
""")

  parse("""
if true then
    1
else 
    if false then x else y
""")

  parse("""
if true then
  if false then
    1
  else
    2
""")

  parse("""
def 
  u = 10
  f x = 
    val y = 13  
    y = y * 42
    return y + 1   
  v = u + 1
""")

  parse("""
val x = ((10 + 5) -
   y)
""")

  parse("""
match x 
case 1 => 2
case 2 => 3
case y => y + 2
      """)
      
  parse("match x case 1 => 2 case x => x * x")

  parse("val x = match x case 1 => 2 case x => x * x")
  
  parse("""
  def f = 10
  val u = 20
  u - f""")
  
  parse("""
  def 
    f = 10
  val 
    u = 20
  u - f""")
  
  parse("""
val x = 3 * (do
  def f = 10
  val u = 20
  u - f)""")

  
  parse("match x case 1 => match y case 2 => x*y")

  parse("match x case 1 => (match y) case 2 => x*y")

  parse("match x case 1 => (match y case 2 => x*y)")
  
  parse("val x = return 2")
   
}  
  
  
}