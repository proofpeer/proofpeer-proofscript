package proofpeer.proofscript.logic

import proofpeer.indent._
import proofpeer.indent.API._
import proofpeer.indent.APIConversions._
import Derivation.{Context => ParseContext}  
import proofpeer.indent.{Constraints => CS}
import Utils._
import proofpeer.scala.lang._

/* 
Special characters used in syntax
=================================

𝒰
MATHEMATICAL SCRIPT CAPITAL U
Unicode: U+1D4B0 (U+D835 U+DCB0), UTF-8: F0 9D 92 B0

𝒫
MATHEMATICAL SCRIPT CAPITAL P
Unicode: U+1D4AB (U+D835 U+DCAB), UTF-8: F0 9D 92 AB

→
RIGHTWARDS ARROW
Unicode: U+2192, UTF-8: E2 86 92

↦
RIGHTWARDS ARROW FROM BAR
Unicode: U+21A6, UTF-8: E2 86 A6

∀ 
FOR ALL
Unicode: U+2200, UTF-8: E2 88 80

∃
THERE EXISTS
Unicode: U+2203, UTF-8: E2 88 83

∄
THERE DOES NOT EXIST
Unicode: U+2204, UTF-8: E2 88 84

⊤
DOWN TACK
Unicode: U+22A4, UTF-8: E2 8A A4

⊥
UP TACK
Unicode: U+22A5, UTF-8: E2 8A A5

¬
NOT SIGN
Unicode: U+00AC, UTF-8: C2 AC

∧
LOGICAL AND
Unicode: U+2227, UTF-8: E2 88 A7

∨
LOGICAL OR
Unicode: U+2228, UTF-8: E2 88 A8

∈
ELEMENT OF
Unicode: U+2208, UTF-8: E2 88 88

∉
NOT AN ELEMENT OF
Unicode: U+2209, UTF-8: E2 88 89

∁
COMPLEMENT
Unicode: U+2201, UTF-8: E2 88 81

∅
EMPTY SET
Unicode: U+2205, UTF-8: E2 88 85

⋂
N-ARY INTERSECTION
Unicode: U+22C2, UTF-8: E2 8B 82

∩
INTERSECTION
Unicode: U+2229, UTF-8: E2 88 A9

⋃
N-ARY UNION
Unicode: U+22C3, UTF-8: E2 8B 83

∪
UNION
Unicode: U+222A, UTF-8: E2 88 AA

P ∖ Q
SET MINUS
Unicode: U+2216, UTF-8: E2 88 96

⊂
SUBSET OF
Unicode: U+2282, UTF-8: E2 8A 82

⊄
NOT A SUBSET OF
Unicode: U+2284, UTF-8: E2 8A 84

∎
END OF PROOF
Unicode: U+220E, UTF-8: E2 88 8E

≠
NOT EQUAL TO
Unicode: U+2260, UTF-8: E2 89 A0

*/

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
    ltokenrule("Comma", ',') ++
    lexrule("Id", "Letter") ++
    lexrule("Id", "Id Digit") ++
    lexrule("Id", "Id Letter") ++
    lexrule("Id", "Id Underscore Letter") ++
    lexrule("RelativeName", "IndexedName") ++
    lexrule("RelativeName", "Id Backslash Name") ++
    lexrule("Name", "RelativeName") ++
    lexrule("Name", "Backslash RelativeName") ++
    lexrule("IndexedName", "Id") ++
    lexrule("IndexedName", "Id Underscore Digits") ++
    ltokenrule("Eq", '=') ++
    ltokenrule("NotEq", Range.singleton(0x2260)) ++
    ltokenrule("RoundBracketOpen", '(') ++
    ltokenrule("RoundBracketClose", ')') ++  
    ltokenrule("CurlyBracketOpen", '{') ++
    ltokenrule("CurlyBracketClose", '}') ++  
    ltokenrule("Bar", '|') ++      
    ltokenrule("RightArrow", Range.singleton(0x2192)) ++
    ltokenrule("Colon", ':') ++
    ltokenrule("Forall", Range.singleton(0x2200)) ++
    ltokenrule("Exists", Range.singleton(0x2203)) ++
    ltokenrule("NotExists", Range.singleton(0x2204)) ++    
    ltokenrule("Universe", Range.singleton(0x1D4B0)) ++
    ltokenrule("Powerset", Range.singleton(0x1D4AB)) ++
    ltokenrule("MapsTo", Range.singleton(0x21A6)) ++
    ltokenrule("True", Range.singleton(0x22A4)) ++
    ltokenrule("False", Range.singleton(0x22A5)) ++
    ltokenrule("Elem", Range.singleton(0x2208)) ++
    ltokenrule("NotElem", Range.singleton(0x2209)) ++
    ltokenrule("Subset", Range.singleton(0x2282)) ++
    ltokenrule("NotSubset", Range.singleton(0x2284)) ++    
    ltokenrule("Or", Range.singleton(0x2228)) ++
    ltokenrule("And", Range.singleton(0x2227)) ++
    ltokenrule("Not", Range.singleton(0x00AC)) ++
    ltokenrule("EmptySet", Range.singleton(0x2205)) ++
    ltokenrule("SetDiff", Range.singleton(0x2216)) ++
    ltokenrule("SetUnion", Range.singleton(0x222A)) ++
    ltokenrule("SetIntersection", Range.singleton(0x2229)) ++
    ltokenrule("SetBigUnion", Range.singleton(0x22C3)) ++
    ltokenrule("SetBigIntersection", Range.singleton(0x22C2))
      
  val g_type = 
    rule("AtomicType", "Universe", c => PTyUniverse) ++
    rule("AtomicType", "Powerset", c => PTyProp) ++
    rule("AtomicType", "Underscore", c => PTyAny) ++
    rule("AtomicType", "RoundBracketOpen Type RoundBracketClose", _.Type.result) ++
    rule("Type", "AtomicType", _.AtomicType.result) ++
    rule("Type", "AtomicType RightArrow Type", c => PTyFun(c.AtomicType.resultAs[Pretype], c.Type.resultAs[Pretype]))
    
  val grammar = 
    literals ++
    g_type ++
    rule("NameTerm", "IndexedName", c => PTmName(parseName(c.IndexedName.text), PTyAny)) ++
    rule("NameTerm", "Name", c => PTmName(parseName(c.Name.text), Pretype.PTyAny)) ++
    rule("SetComprehensionTerm", "CurlyBracketOpen Term Bar Bindings CurlyBracketClose", 
      c => pTmSetComprehension(c.Bindings.resultAs[List[Binding]], c.Term.resultAs[Preterm], None)) ++
    rule("SetComprehensionTerm", "CurlyBracketOpen Term_1 Bar Bindings Dot Term_2 CurlyBracketClose",  
      c => pTmSetComprehension(c.Bindings.resultAs[List[Binding]], c.Term_1.resultAs[Preterm], Some(c.Term_2.resultAs[Preterm]))) ++ 
    rule("ConcreteSetTerm", "CurlyBracketOpen TermList CurlyBracketClose", c => pTmSet(c.TermList.resultAs[List[Preterm]])) ++
    rule("ConcreteSetTerm", "CurlyBracketOpen CurlyBracketClose", c => pTmConst(Kernel.empty_set)) ++   
    rule("AtomicTerm", "NameTerm", _.NameTerm.result) ++
    rule("AtomicTerm", "RoundBracketOpen TermList RoundBracketClose", c => pTmTuple(c.TermList.resultAs[List[Preterm]])) ++
    rule("AtomicTerm", "SetComprehensionTerm", _.SetComprehensionTerm.result) ++
    rule("AtomicTerm", "ConcreteSetTerm", _.ConcreteSetTerm.result) ++    
    rule("AtomicTerm", "True", c => pTmConst(Kernel.logical_true)) ++
    rule("AtomicTerm", "False", c => pTmConst(Kernel.logical_false)) ++
    rule("AtomicTerm", "EmptySet", c => pTmConst(Kernel.empty_set)) ++
    rule("CombTerm", "AtomicTerm", _.AtomicTerm.result) ++
    rule("CombTerm", "CombTerm AtomicTerm", c => PTmComb(c.CombTerm.resultAs[Preterm], c.AtomicTerm.resultAs[Preterm], None, Pretype.PTyAny)) ++
    rule("Binding", "IndexedName", c => Binding(parseIndexedName(c.IndexedName.text), None)) ++
    rule("Binding", "IndexedName Colon Type", c => Binding(parseIndexedName(c.IndexedName.text), Some(TypeDomain(c.Type.resultAs[Pretype])))) ++    
    rule("Binding", "IndexedName Elem Term", c => Binding(parseIndexedName(c.IndexedName.text), Some(SetDomain(c.Term.resultAs[Preterm])))) ++ 
    rule("Bindings", "Binding", c => List(c.Binding.resultAs[Binding])) ++
    rule("Bindings", "Bindings Comma Binding", c => c.Binding.resultAs[Binding] :: c.Bindings.resultAs[List[Binding]]) ++ 
    rule("SetUnaryOpTerm", "CombTerm", _.CombTerm.result) ++
    rule("SetUnaryOpTerm", "Powerset SetUnaryOpTerm", c => pTmUnaryOp(Kernel.set_power, c.SetUnaryOpTerm.resultAs[Preterm])) ++
    rule("SetUnaryOpTerm", "SetBigUnion SetUnaryOpTerm", c => pTmUnaryOp(Kernel.set_bigunion, c.SetUnaryOpTerm.resultAs[Preterm])) ++
    rule("SetUnaryOpTerm", "SetBigIntersection SetUnaryOpTerm", c => pTmUnaryOp(Kernel.set_bigintersection, c.SetUnaryOpTerm.resultAs[Preterm])) ++
    rule("SetIntersectionTerm", "SetUnaryOpTerm", _.SetUnaryOpTerm.result) ++
    rule("SetIntersectionTerm", "SetIntersectionTerm SetIntersection SetUnaryOpTerm",
      c => pTmBinaryOp(Kernel.set_intersection, c.SetIntersectionTerm.resultAs[Preterm], c.SetUnaryOpTerm.resultAs[Preterm])) ++
    rule("SetUnionTerm", "SetIntersectionTerm", _.SetIntersectionTerm.result) ++
    rule("SetUnionTerm", "SetUnionTerm SetUnion SetIntersectionTerm",
      c => pTmBinaryOp(Kernel.set_union, c.SetUnionTerm.resultAs[Preterm], c.SetIntersectionTerm.resultAs[Preterm])) ++
    rule("SetDiffTerm", "SetUnionTerm", _.SetUnionTerm.result) ++
    rule("SetDiffTerm", "SetDiffTerm SetDiff SetUnionTerm", 
      c => pTmBinaryOp(Kernel.set_difference, c.SetDiffTerm.resultAs[Preterm], c.SetUnionTerm.resultAs[Preterm])) ++
    rule("SetTerm", "SetDiffTerm", _.SetDiffTerm.result) ++
    rule("SetBinaryRelationTerm", "SetTerm", _.SetTerm.result) ++
    rule("SetBinaryRelationTerm", "SetTerm_1 Elem SetTerm_2", 
      c => pTmBinaryOp(Kernel.set_elementOf, c.SetTerm_1.resultAs[Preterm], c.SetTerm_2.resultAs[Preterm])) ++
    rule("SetBinaryRelationTerm", "SetTerm_1 NotElem SetTerm_2", 
      c => pTmUnaryOp(Kernel.logical_not, pTmBinaryOp(Kernel.set_elementOf, c.SetTerm_1.resultAs[Preterm], c.SetTerm_2.resultAs[Preterm]))) ++    
    rule("SetBinaryRelationTerm", "SetTerm_1 Subset SetTerm_2", 
      c => pTmBinaryOp(Kernel.set_subsetOf, c.SetTerm_1.resultAs[Preterm], c.SetTerm_2.resultAs[Preterm])) ++
    rule("SetBinaryRelationTerm", "SetTerm_1 NotSubset SetTerm_2", 
      c => pTmUnaryOp(Kernel.logical_not, pTmBinaryOp(Kernel.set_subsetOf, c.SetTerm_1.resultAs[Preterm], c.SetTerm_2.resultAs[Preterm]))) ++    
    rule("TypedTerm", "SetBinaryRelationTerm", _.SetBinaryRelationTerm.result) ++
    rule("TypedTerm", "TypedTerm Colon Type", c => PTmTyping(c.TypedTerm.resultAs[Preterm], c.Type.resultAs[Pretype])) ++
    rule("EqTerm", "TypedTerm", _.TypedTerm.result) ++
    rule("EqTerm", "TypedTerm_1 Eq TypedTerm_2", c => pTmEquals(c.TypedTerm_1.resultAs[Preterm], c.TypedTerm_2.resultAs[Preterm])) ++
    rule("EqTerm", "TypedTerm_1 NotEq TypedTerm_2", c => pTmUnaryOp(Kernel.logical_not, pTmEquals(c.TypedTerm_1.resultAs[Preterm], c.TypedTerm_2.resultAs[Preterm]))) ++
    rule("NotTerm", "Not NotTerm", c => pTmUnaryOp(Kernel.logical_not, c.NotTerm.resultAs[Preterm])) ++
    rule("NotTerm", "EqTerm", _.EqTerm.result) ++
    rule("AndTerm", "AndTerm And NotTerm", c => pTmBinaryOp(Kernel.logical_and, c.AndTerm.resultAs[Preterm], c.NotTerm.resultAs[Preterm])) ++
    rule("AndTerm", "NotTerm", _.NotTerm.result) ++
    rule("OrTerm", "OrTerm Or AndTerm", c => pTmBinaryOp(Kernel.logical_or, c.OrTerm.resultAs[Preterm], c.AndTerm.resultAs[Preterm])) ++
    rule("OrTerm", "AndTerm", _.AndTerm.result) ++
    rule("ImpliesTerm", "OrTerm RightArrow ImpliesTerm", c => pTmBinaryOp(Kernel.implies, c.OrTerm.resultAs[Preterm], c.ImpliesTerm.resultAs[Preterm])) ++
    rule("ImpliesTerm", "OrTerm", _.OrTerm.result) ++
    rule("PropTerm", "ImpliesTerm", _.ImpliesTerm.result) ++
    rule("AbsTerm", "PropTerm", _.PropTerm.result) ++
    rule("AbsTerm", "Forall Bindings Dot AbsTerm", c => pTmForall(c.Bindings.resultAs[List[Binding]], c.AbsTerm.resultAs[Preterm])) ++
    rule("AbsTerm", "Exists Bindings Dot AbsTerm", c => pTmExists(c.Bindings.resultAs[List[Binding]], c.AbsTerm.resultAs[Preterm])) ++
    rule("AbsTerm", "NotExists Bindings Dot AbsTerm", c => pTmUnaryOp(Kernel.logical_not, pTmExists(c.Bindings.resultAs[List[Binding]], c.AbsTerm.resultAs[Preterm]))) ++
    rule("AbsTerm", "Bindings MapsTo AbsTerm", c => pTmAbs(c.Bindings.resultAs[List[Binding]], c.AbsTerm.resultAs[Preterm])) ++
    rule("TermList", "Term", c => List(c.Term.resultAs[Preterm])) ++
    rule("TermList", "TermList Comma Term", c => c.Term.resultAs[Preterm] :: c.TermList.resultAs[List[Preterm]]) ++
    rule("Term", "AbsTerm", _.AbsTerm.result)
    
  def parse(g_prog : Grammar, nonterminal : Nonterminal, input : String) {
    if (!g_prog.info.wellformed) {
      println("grammar errors:\n"+g_prog.info.errors)
      return
    }
    println("term: '" + input + "'")
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
          println("Parse error at token " + i + ".")
        } else {
          println("Parsed successfully, but ambiguous parse tree.")       
        } 
    }  
    println()
  }   

  def parsePreterm(input : String) : Option[Preterm] = {
    if (!grammar.info.wellformed) Utils.failwith("Syntax.grammar is not wellformed")
    val d = UnicodeDocument.fromString(input)
    grammar.parser.parse(d, "Term", 0) match {
      case None => None
      case Some((v, i)) =>
        if (v.isUnique && i == d.size) {
          val result = Derivation.computeParseResult(grammar, d, t => null, v)
          Some(result.resultAs[Preterm])
        } else None
    }
  }  

  private def containsSpace(s : String) : Boolean = {
    s.indexOf(" ") >= 0
  }

  private def protect(s : String) : String = {
    if (containsSpace(s)) "(" + s + ")" else s
  }

  def printType(ty : Type) : String = {
    ty match {
      case Type.Universe => "𝒰"
      case Type.Prop => "𝒫"
      case Type.Fun(domain, range) => protect(printType(domain)) + " → " + printType(range)
    }  
  }

  def printName(name : IndexedName) : String = {
    if (name.index.isDefined)
      name.name + "_" + name.index.get
    else
      name.name
  }

  def printName(name : Name) : String = {
    if (name.namespace.isDefined)
      name.namespace.get + "\\" + printName(name.name)
    else
      printName(name.name)
  }

  def printTerm(tm : Term) : String = {
    tm match {
      case Term.Comb(Term.PolyConst(Kernel.forall, _), Term.Abs(name, ty, body)) =>
        "∀ " + printName(name) + " : " + printType(ty) + ". " + printTerm(body)
      case Term.Comb(Term.PolyConst(Kernel.exists, _), Term.Abs(name, ty, body)) =>
        "∃ " + printName(name) + " : " + printType(ty) + ". " + printTerm(body)
      case Term.Comb(Term.Comb(Term.PolyConst(Kernel.equals, _), left), right) =>
        protect(printTerm(left)) + " = " + protect(printTerm(right))
      case Term.Comb(Term.Comb(Term.Const(Kernel.funapply), f), x) =>
        protect(printTerm(f)) + " " + protect(printTerm(x))
      case Term.PolyConst(name, alpha) =>
        val ty = 
          name match {
            case Kernel.forall => Type.Fun(Type.Fun(alpha, Type.Prop), Type.Prop)
            case Kernel.exists => Type.Fun(Type.Fun(alpha, Type.Prop), Type.Prop)
            case Kernel.equals => Type.Fun(alpha, Type.Fun(alpha, Type.Prop))
            case _ => Utils.failwith("this is not a polymorphic name: "+name)
          }
        printName(name) + " : " + printType(ty)
      case Term.Const(name : Name) =>
        printName(name)
      case Term.Comb(f, x) =>
        protect(printTerm(f)) + " " + protect(printTerm(x))
      case Term.Abs(name, ty, body) =>
        printName(name) + " : " + printType(ty) + " ↦ " + printTerm(body)
      case Term.Var(name) =>
        printName(name)
    }
  }
    
  def mainl(args : Array[String]) {
    val inputs = Array("hello", "hello_there", "hello_", "hello_20", "\\great\\expectations\\hello_10", 
        "thank\\you", "\\cool", "\\hello_23", "123", "\\123", "\\x123", "\\x1_23",
        "x:𝒰", "\\x : 𝒰 → 𝒫 → 𝒫", "\\x:(𝒰→𝒫)→𝒫", "x : 𝒰 → 𝒫 ↦ x",
        "x : 𝒰 ↦ x", "(x : 𝒰) ↦ x", "x : 𝒰 → 𝒫 ↦ y ↦ z ↦ x z y")
    for (input <- inputs) {
      parse(grammar, "Term", input)
      println("")
    }
  }
  
}