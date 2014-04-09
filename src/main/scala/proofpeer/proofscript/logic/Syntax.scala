package proofpeer.proofscript.logic

import proofpeer.indent._
import proofpeer.indent.API._
import proofpeer.indent.APIConversions._
import Derivation.{Context => ParseContext}  
import proofpeer.indent.{Constraints => CS}
import Utils._
import proofpeer.scala.lang._

sealed trait Pretype
object Pretype {
  case object PTyUniverse extends Pretype
  case object PTyProp extends Pretype
  case class PTyFun(domain : Pretype, range : Pretype) extends Pretype
  case object PTyAny extends Pretype
}

sealed trait Preterm
object Preterm {
  case class PTmTyping(tm : Preterm, ty : Pretype) extends Preterm
  case class PTmName(name : Name) extends Preterm
}

object TermSyntax {
  
  import Preterm._
  import Pretype._
  
  def ltokenrule(nonterminal : Nonterminal, c1 : Char, c2 : Char) : Grammar = 
      tokenrule(nonterminal, Range.interval(c1, c2)) ++ lexical(nonterminal)
  
  def ltokenrule(nonterminal : Nonterminal, c : Char) : Grammar = ltokenrule(nonterminal, c, c)

  def ltokenrule(nonterminal : Nonterminal, r : Range) : Grammar =
      tokenrule(nonterminal, r) ++ lexical(nonterminal)
    
  
  
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
    lexrule("Lambda", "Backslash_0 Backslash_1") ++
    lexrule("Name", "RelativeName") ++
    lexrule("Name", "Backslash RelativeName") ++
    ltokenrule("Le", '<') ++
    ltokenrule("Gr", '>') ++
    ltokenrule("Eq", '=') ++
    ltokenrule("Minus", '-') ++
    ltokenrule("ExclamationMark", '!') ++
    ltokenrule("QuestionMark", '?') ++
    lexrule("Leq", "Le Eq") ++
    lexrule("Geq", "Gr Eq") ++
    ltokenrule("RoundBracketOpen", '(') ++
    ltokenrule("RoundBracketClose", ')') ++  
    ltokenrule("TypeArrow", Range.singleton(0x2192)) ++
    ltokenrule("Colon", ':') ++
    lexrule("DoubleColon", "Colon_0 Colon_1") ++
    ltokenrule("Universe", Range.singleton(0x1D4B0)) ++
    ltokenrule("Prop", Range.singleton(0x1D4AB))
    
  val g_type = 
    rule("AtomicType", "Universe", c => PTyUniverse) ++
    rule("AtomicType", "Prop", c => PTyProp) ++
    rule("AtomicType", "Underscore", c => PTyAny) ++
    rule("AtomicType", "RoundBracketOpen Type RoundBracketClose", _.Type.result) ++
    rule("Type", "AtomicType", _.AtomicType.result) ++
    rule("Type", "AtomicType TypeArrow Type", c => PTyFun(c.AtomicType.resultAs[Pretype], c.Type.resultAs[Pretype]))
    
  val grammar = 
    literals ++
    g_type ++
    rule("AtomicTerm", "Name", c => PTmName(parseName(c.Name.text))) ++
    rule("TypedTerm", "AtomicTerm", _.AtomicTerm.result) ++
    rule("TypedTerm", "TypedTerm Colon Type", c => PTmTyping(c.TypedTerm.resultAs[Preterm], c.Type.resultAs[Pretype])) ++
    rule("Term", "TypedTerm", _.TypedTerm.result)
    
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
        "thank\\you", "\\cool", "\\hello_23", "123", "\\123", "\\x123", "\\x1_23",
        "x:𝒰", "\\x : 𝒰 → 𝒫 → 𝒫", "\\x:(𝒰→𝒫)→𝒫")
    for (input <- inputs) {
      parse(grammar, "Term", input)
      println("")
    }
  }
  
}