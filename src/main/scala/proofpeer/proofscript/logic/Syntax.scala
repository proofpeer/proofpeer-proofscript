package proofpeer.proofscript.logic

import proofpeer.indent._
import proofpeer.indent.API._
import proofpeer.indent.APIConversions._
import Derivation.{Context => ParseContext}  
import proofpeer.indent.{Constraints => CS}
import Utils._
import proofpeer.scala.lang._

object TermSyntax {
  
  def ltokenrule(nonterminal : Nonterminal, c1 : Char, c2 : Char) : Grammar = 
      tokenrule(nonterminal, Range.interval(c1, c2)) ++ lexical(nonterminal)
  
  def ltokenrule(nonterminal : Nonterminal, c : Char) : Grammar = ltokenrule(nonterminal, c, c)
      
  def parseIndexedName(s : String) : IndexedName = {
    val index = s.lastIndexOf("_")
    if (index < 0) {
      IndexedName(s, None)
    } else {
      val prefix = s.substring(0, index)
      val suffix = s.substring(index + 1)
      val c = suffix(0)
      if (c >= '0' && c <= '9') 
        IndexedName(prefix, Some(str2Integer(suffix)))
      else
        IndexedName(s, None)
    }
  }
  
  def parseName(s : String) : Name = {
    val index = s.lastIndexOf("\\")
    if (index < 0) {
      Name(None, parseIndexedName(s))
    } else {
      val namespace = if (index == 0) "\\" else s.substring(0, index)
      val indexedname = parseIndexedName(s.substring(index + 1))
      Name(Some(namespace), indexedname)
    }
  }
   
  val literals = 
    ltokenrule("LowerLetter", 'a', 'z') ++
    ltokenrule("UpperLetter", 'A', 'Z') ++
    lexrule("Letter", "UpperLetter") ++
    lexrule("Letter", "LowerLetter") ++  
    ltokenrule("Digit", '0', '9') ++
    lexrule("Digits", "Digit") ++
    lexrule("Digits", "Digits Digit") ++
    ltokenrule("Underscore", '_') ++ 
    ltokenrule("Backslash", '\\') ++
    ltokenrule("Dot", '.') ++
    lexrule("Id", "Letter") ++
    lexrule("Id", "Id Digit") ++
    lexrule("Id", "Id Letter") ++
    lexrule("Id", "Id Underscore Letter") ++
    lexrule("IndexedName", "Id") ++
    lexrule("IndexedName", "Id Underscore Digits") ++
    lexrule("RelativeName", "IndexedName") ++
    lexrule("RelativeName", "Id Backslash Name") ++
    lexrule("Name", "RelativeName") ++
    lexrule("Name", "Backslash RelativeName") 
    
  val grammar = 
    literals ++
    rule("Term", "Name", c => parseName(c.Name.text))
    
  def parse(g_prog : Grammar, nonterminal : Nonterminal, input : String) {
    if (!g_prog.info.wellformed) {
      println("grammar errors:\n"+g_prog.info.errors)
      return
    }
    println("term: '"+input+"'")
    val d = UnicodeDocument.fromString(input)
    val g = g_prog.parser.parse(d, nonterminal, 0)
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
    val inputs = Array("hello", "hello_there", "hello_", "hello_20", "\\great\\expectations\\hello_10", 
        "thank\\you", "\\cool", "\\hello_23", "123", "\\123", "\\x123", "\\x1_23")
    for (input <- inputs) {
      parse(grammar, "Term", input)
      println("")
    }
  }
  
}