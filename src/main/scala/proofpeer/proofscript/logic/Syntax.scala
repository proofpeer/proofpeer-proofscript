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

ℙ
DOUBLE-STRUCK CAPITAL P
Unicode: U+2119, UTF-8: E2 84 99

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

𝒫
MATHEMATICAL SCRIPT CAPITAL P
Unicode: U+1D4AB (U+D835 U+DCAB), UTF-8: F0 9D 92 AB

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

«
LEFT-POINTING DOUBLE ANGLE QUOTATION MARK
Unicode: U+00AB, UTF-8: C2 AB

»
RIGHT-POINTING DOUBLE ANGLE QUOTATION MARK
Unicode: U+00BB, UTF-8: C2 BB

‹
SINGLE LEFT-POINTING ANGLE QUOTATION MARK
Unicode: U+2039, UTF-8: E2 80 B9

›
SINGLE RIGHT-POINTING ANGLE QUOTATION MARK
Unicode: U+203A, UTF-8: E2 80 BA

*/

object Syntax {
  
  import Preterm._
  import Pretype._
  
  def ltokenrule(nonterminal : Nonterminal, c1 : Char, c2 : Char) : Grammar = 
      tokenrule(nonterminal, Range.interval(c1, c2)) ++ lexical(nonterminal, LexicalPriority(0, None))
  
  def ltokenrule(nonterminal : Nonterminal, c : Char) : Grammar = ltokenrule(nonterminal, c, c)

  def ltokenrule(nonterminal : Nonterminal, r : Range) : Grammar =
      tokenrule(nonterminal, r) ++ lexical(nonterminal, LexicalPriority(0, None))
      
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
      Name(Some(new Namespace(namespace)), indexedname)
    }
  }

  def lexrule(n : Nonterminal, rhs : String) : Grammar = {
    API.lexrule(n, rhs, LexicalPriority(0, None))
  }

  def lexrule(n : Nonterminal, rhs : String, prio : Int) : Grammar = {
    API.lexrule(n, rhs, LexicalPriority(0, Some(prio)))
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
    lexrule("Id", "Letter", 1) ++
    lexrule("Id", "Id Digit") ++
    lexrule("Id", "Id Letter") ++
    lexrule("Id", "Id Underscore Letter") ++
    lexrule("RelativeNamespace", "Id") ++
    lexrule("RelativeNamespace", "RelativeNamespace Backslash Id") ++
    lexrule("AbsoluteNamespace", "Backslash RelativeNamespace") ++
    lexrule("Namespace", "AbsoluteNamespace") ++
    lexrule("Namespace", "RelativeNamespace") ++
    lexrule("RelativeName", "IndexedName") ++
    lexrule("RelativeName", "Id Backslash RelativeName") ++
    lexrule("Name", "RelativeName", 1) ++
    lexrule("Name", "Backslash RelativeName") ++
    lexrule("IndexedName", "Id", 1) ++
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
    ltokenrule("QuoteOpen", Range.singleton(0x2039)) ++
    ltokenrule("QuoteClose", Range.singleton(0x203A)) ++
    ltokenrule("Forall", Range.singleton(0x2200)) ++
    ltokenrule("Exists", Range.singleton(0x2203)) ++
    ltokenrule("NotExists", Range.singleton(0x2204)) ++    
    ltokenrule("Universe", Range.singleton(0x1D4B0)) ++
    ltokenrule("Prop", Range.singleton(0x2119)) ++
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
    rule("AtomicType", "Prop", c => PTyProp) ++
    rule("AtomicType", "Underscore", c => PTyAny) ++
    rule("AtomicType", "RoundBracketOpen Type RoundBracketClose", _.Type.result) ++
    rule("Type", "AtomicType", _.AtomicType.result) ++
    rule("Type", "AtomicType RightArrow Type", c => PTyFun(c.AtomicType.resultAs[Pretype], c.Type.resultAs[Pretype]))
    
  val g_Prefix_term = 
    rule("PrefixNameTerm", "IndexedName", c => PTmName(parseName(c.IndexedName.text), PTyAny)) ++
    rule("PrefixNameTerm", "Name", c => PTmName(parseName(c.Name.text), Pretype.PTyAny)) ++
    rule("PrefixSetComprehensionTerm", "CurlyBracketOpen PrefixTerm Bar PrefixBindings CurlyBracketClose", 
      c => pTmSetComprehension(c.PrefixBindings.resultAs[List[Binding]], c.PrefixTerm.resultAs[Preterm], None)) ++
    rule("PrefixSetComprehensionTerm", "CurlyBracketOpen PrefixTerm_1 Bar PrefixBindings Dot PrefixTerm_2 CurlyBracketClose",  
      c => pTmSetComprehension(c.PrefixBindings.resultAs[List[Binding]], c.PrefixTerm_1.resultAs[Preterm], Some(c.PrefixTerm_2.resultAs[Preterm]))) ++ 
    rule("PrefixConcreteSetTerm", "CurlyBracketOpen PrefixTermList CurlyBracketClose", c => pTmSet(c.PrefixTermList.resultAs[List[Preterm]])) ++
    rule("PrefixConcreteSetTerm", "CurlyBracketOpen CurlyBracketClose", c => pTmConst(Kernel.empty_set)) ++   
    rule("PrefixAtomicTerm", "PrefixNameTerm", _.PrefixNameTerm.result) ++
    rule("PrefixAtomicTerm", "RoundBracketOpen PrefixTermList RoundBracketClose", c => pTmTuple(c.PrefixTermList.resultAs[List[Preterm]])) ++
    rule("PrefixAtomicTerm", "PrefixSetComprehensionTerm", _.PrefixSetComprehensionTerm.result) ++
    rule("PrefixAtomicTerm", "PrefixConcreteSetTerm", _.PrefixConcreteSetTerm.result) ++    
    rule("PrefixAtomicTerm", "True", c => pTmConst(Kernel.logical_true)) ++
    rule("PrefixAtomicTerm", "False", c => pTmConst(Kernel.logical_false)) ++
    rule("PrefixAtomicTerm", "EmptySet", c => pTmConst(Kernel.empty_set)) ++
    rule("PrefixAtomicTerm", "QuoteOpen PrefixQuotedTerm QuoteClose", c => pTmQuote(c.PrefixQuotedTerm.result)) ++
    rule("PrefixCombTerm", "PrefixAtomicTerm", _.PrefixAtomicTerm.result) ++
    rule("PrefixCombTerm", "PrefixCombTerm PrefixAtomicTerm", 
      c => PTmComb(c.PrefixCombTerm.resultAs[Preterm], c.PrefixAtomicTerm.resultAs[Preterm], None, Pretype.PTyAny)) ++
    rule("PrefixPureBinding", "IndexedName", c => Binding(parseIndexedName(c.IndexedName.text), None)) ++
    rule("PrefixAnnotatedBinding", "IndexedName Colon Type", c => Binding(parseIndexedName(c.IndexedName.text), Some(TypeDomain(c.Type.resultAs[Pretype])))) ++    
    rule("PrefixAnnotatedBinding", "IndexedName Elem PrefixTerm", c => Binding(parseIndexedName(c.IndexedName.text), Some(SetDomain(c.PrefixTerm.resultAs[Preterm])))) ++ 
    rule("PrefixBinding", "PrefixPureBinding", _.PrefixPureBinding.result) ++
    rule("PrefixBinding", "PrefixAnnotatedBinding", _.PrefixAnnotatedBinding.result) ++    
    rule("PrefixPureBindings", "PrefixPureBinding", c => List(c.PrefixPureBinding.resultAs[Binding])) ++
    rule("PrefixPureBindings", "PrefixPureBindings PrefixPureBinding", c => c.PrefixPureBinding.resultAs[Binding] :: c.PrefixPureBindings.resultAs[List[Binding]]) ++ 
    rule("PrefixBindings", "PrefixPureBindings", _.PrefixPureBindings.result) ++
    rule("PrefixBindings", "PrefixAnnotatedBinding", c => List(c.PrefixAnnotatedBinding.resultAs[Binding])) ++
    rule("PrefixBindings", "PrefixBindings Comma PrefixBinding", c => c.PrefixBinding.resultAs[Binding] :: c.PrefixBindings.resultAs[List[Binding]]) ++ 
    rule("PrefixSetUnaryOpTerm", "PrefixCombTerm", _.PrefixCombTerm.result) ++
    rule("PrefixSetUnaryOpTerm", "Powerset PrefixSetUnaryOpTerm", c => pTmUnaryOp(Kernel.set_power, c.PrefixSetUnaryOpTerm.resultAs[Preterm])) ++
    rule("PrefixSetUnaryOpTerm", "SetBigUnion PrefixSetUnaryOpTerm", c => pTmUnaryOp(Kernel.set_bigunion, c.PrefixSetUnaryOpTerm.resultAs[Preterm])) ++
    rule("PrefixSetUnaryOpTerm", "SetBigIntersection PrefixSetUnaryOpTerm", c => pTmUnaryOp(Kernel.set_bigintersection, c.PrefixSetUnaryOpTerm.resultAs[Preterm])) ++
    rule("PrefixSetIntersectionTerm", "PrefixSetUnaryOpTerm", _.PrefixSetUnaryOpTerm.result) ++
    rule("PrefixSetIntersectionTerm", "PrefixSetIntersectionTerm SetIntersection PrefixSetUnaryOpTerm",
      c => pTmBinaryOp(Kernel.set_intersection, c.PrefixSetIntersectionTerm.resultAs[Preterm], c.PrefixSetUnaryOpTerm.resultAs[Preterm])) ++
    rule("PrefixSetUnionTerm", "PrefixSetIntersectionTerm", _.PrefixSetIntersectionTerm.result) ++
    rule("PrefixSetUnionTerm", "PrefixSetUnionTerm SetUnion PrefixSetIntersectionTerm",
      c => pTmBinaryOp(Kernel.set_union, c.PrefixSetUnionTerm.resultAs[Preterm], c.PrefixSetIntersectionTerm.resultAs[Preterm])) ++
    rule("PrefixSetDiffTerm", "PrefixSetUnionTerm", _.PrefixSetUnionTerm.result) ++
    rule("PrefixSetDiffTerm", "PrefixSetDiffTerm SetDiff PrefixSetUnionTerm", 
      c => pTmBinaryOp(Kernel.set_difference, c.PrefixSetDiffTerm.resultAs[Preterm], c.PrefixSetUnionTerm.resultAs[Preterm])) ++
    rule("PrefixSetTerm", "PrefixSetDiffTerm", _.PrefixSetDiffTerm.result) ++
    rule("PrefixSetBinaryRelationTerm", "PrefixSetTerm", _.PrefixSetTerm.result) ++
    rule("PrefixSetBinaryRelationTerm", "PrefixSetTerm_1 Elem PrefixSetTerm_2", 
      c => pTmBinaryOp(Kernel.set_elementOf, c.PrefixSetTerm_1.resultAs[Preterm], c.PrefixSetTerm_2.resultAs[Preterm])) ++
    rule("PrefixSetBinaryRelationTerm", "PrefixSetTerm_1 NotElem PrefixSetTerm_2", 
      c => pTmUnaryOp(Kernel.logical_not, pTmBinaryOp(Kernel.set_elementOf, c.PrefixSetTerm_1.resultAs[Preterm], c.PrefixSetTerm_2.resultAs[Preterm]))) ++    
    rule("PrefixSetBinaryRelationTerm", "PrefixSetTerm_1 Subset PrefixSetTerm_2", 
      c => pTmBinaryOp(Kernel.set_subsetOf, c.PrefixSetTerm_1.resultAs[Preterm], c.PrefixSetTerm_2.resultAs[Preterm])) ++
    rule("PrefixSetBinaryRelationTerm", "PrefixSetTerm_1 NotSubset PrefixSetTerm_2", 
      c => pTmUnaryOp(Kernel.logical_not, pTmBinaryOp(Kernel.set_subsetOf, c.PrefixSetTerm_1.resultAs[Preterm], c.PrefixSetTerm_2.resultAs[Preterm]))) ++    
    rule("PrefixTypedTerm", "PrefixSetBinaryRelationTerm", _.PrefixSetBinaryRelationTerm.result) ++
    rule("PrefixTypedTerm", "PrefixTypedTerm Colon Type", c => PTmTyping(c.PrefixTypedTerm.resultAs[Preterm], c.Type.resultAs[Pretype])) ++
    rule("PrefixEqTerm", "PrefixTypedTerm", _.PrefixTypedTerm.result) ++
    rule("PrefixEqTerm", "PrefixTypedTerm_1 Eq PrefixTypedTerm_2", c => pTmEquals(c.PrefixTypedTerm_1.resultAs[Preterm], c.PrefixTypedTerm_2.resultAs[Preterm])) ++
    rule("PrefixEqTerm", "PrefixTypedTerm_1 NotEq PrefixTypedTerm_2", c => pTmUnaryOp(Kernel.logical_not, pTmEquals(c.PrefixTypedTerm_1.resultAs[Preterm], c.PrefixTypedTerm_2.resultAs[Preterm]))) ++
    rule("PrefixNotTerm", "Not PrefixNotTerm", c => pTmUnaryOp(Kernel.logical_not, c.PrefixNotTerm.resultAs[Preterm])) ++
    rule("PrefixNotTerm", "PrefixEqTerm", _.PrefixEqTerm.result) ++
    rule("PrefixAndTerm", "PrefixAndTerm And PrefixNotTerm", c => pTmBinaryOp(Kernel.logical_and, c.PrefixAndTerm.resultAs[Preterm], c.PrefixNotTerm.resultAs[Preterm])) ++
    rule("PrefixAndTerm", "PrefixNotTerm", _.PrefixNotTerm.result) ++
    rule("PrefixOrTerm", "PrefixOrTerm Or PrefixAndTerm", c => pTmBinaryOp(Kernel.logical_or, c.PrefixOrTerm.resultAs[Preterm], c.PrefixAndTerm.resultAs[Preterm])) ++
    rule("PrefixOrTerm", "PrefixAndTerm", _.PrefixAndTerm.result) ++
    rule("PrefixImpliesTerm", "PrefixOrTerm RightArrow PrefixImpliesTerm", c => pTmBinaryOp(Kernel.implies, c.PrefixOrTerm.resultAs[Preterm], c.PrefixImpliesTerm.resultAs[Preterm])) ++
    rule("PrefixImpliesTerm", "PrefixOrTerm", _.PrefixOrTerm.result) ++
    rule("PrefixPropTerm", "PrefixImpliesTerm", _.PrefixImpliesTerm.result) ++
    rule("PrefixAbsTerm", "PrefixPropTerm", _.PrefixPropTerm.result) ++
    rule("PrefixAbsTerm", "PrefixQuantifierTerm", _.PrefixQuantifierTerm.result) ++
    rule("PrefixQuantifierTerm", "Forall PrefixBindings PrefixQuantifierTerm", c => pTmForall(c.PrefixBindings.resultAs[List[Binding]], c.PrefixQuantifierTerm.resultAs[Preterm])) ++
    rule("PrefixQuantifierTerm", "Exists PrefixBindings PrefixQuantifierTerm", c => pTmExists(c.PrefixBindings.resultAs[List[Binding]], c.PrefixQuantifierTerm.resultAs[Preterm])) ++
    rule("PrefixQuantifierTerm", "NotExists PrefixBindings PrefixQuantifierTerm", c => pTmUnaryOp(Kernel.logical_not, pTmExists(c.PrefixBindings.resultAs[List[Binding]], c.PrefixQuantifierTerm.resultAs[Preterm]))) ++
    rule("PrefixQuantifierTerm", "Forall PrefixBindings Dot PrefixAbsTerm", c => pTmForall(c.PrefixBindings.resultAs[List[Binding]], c.PrefixAbsTerm.resultAs[Preterm])) ++
    rule("PrefixQuantifierTerm", "Exists PrefixBindings Dot PrefixAbsTerm", c => pTmExists(c.PrefixBindings.resultAs[List[Binding]], c.PrefixAbsTerm.resultAs[Preterm])) ++
    rule("PrefixQuantifierTerm", "NotExists PrefixBindings Dot PrefixAbsTerm", c => pTmUnaryOp(Kernel.logical_not, pTmExists(c.PrefixBindings.resultAs[List[Binding]], c.PrefixAbsTerm.resultAs[Preterm]))) ++
    rule("PrefixAbsTerm", "PrefixBindings MapsTo PrefixAbsTerm", c => pTmAbs(c.PrefixBindings.resultAs[List[Binding]], c.PrefixAbsTerm.resultAs[Preterm])) ++
    rule("PrefixTermList", "PrefixTerm", c => List(c.PrefixTerm.resultAs[Preterm])) ++
    rule("PrefixTermList", "PrefixTermList Comma PrefixTerm", c => c.PrefixTerm.resultAs[Preterm] :: c.PrefixTermList.resultAs[List[Preterm]]) ++
    rule("PrefixTerm", "PrefixAbsTerm", _.PrefixAbsTerm.result)

val g_Value_term = 
    //rule("ValueNameTerm", "IndexedName", c => PTmName(parseName(c.IndexedName.text), PTyAny)) ++
    rule("ValueNameTerm", "Name", c => PTmName(parseName(c.Name.text), Pretype.PTyAny)) ++
    rule("ValueSetComprehensionTerm", "CurlyBracketOpen ValueTerm Bar ValueBindings CurlyBracketClose", 
      c => pTmSetComprehension(c.ValueBindings.resultAs[List[Binding]], c.ValueTerm.resultAs[Preterm], None)) ++
    rule("ValueSetComprehensionTerm", "CurlyBracketOpen ValueTerm_1 Bar ValueBindings Dot ValueTerm_2 CurlyBracketClose",  
      c => pTmSetComprehension(c.ValueBindings.resultAs[List[Binding]], c.ValueTerm_1.resultAs[Preterm], Some(c.ValueTerm_2.resultAs[Preterm]))) ++ 
    rule("ValueConcreteSetTerm", "CurlyBracketOpen ValueTermList CurlyBracketClose", c => pTmSet(c.ValueTermList.resultAs[List[Preterm]])) ++
    rule("ValueConcreteSetTerm", "CurlyBracketOpen CurlyBracketClose", c => pTmConst(Kernel.empty_set)) ++   
    rule("ValueAtomicTerm", "ValueNameTerm", _.ValueNameTerm.result) ++
    rule("ValueAtomicTerm", "RoundBracketOpen ValueTermList RoundBracketClose", c => pTmTuple(c.ValueTermList.resultAs[List[Preterm]])) ++
    rule("ValueAtomicTerm", "ValueSetComprehensionTerm", _.ValueSetComprehensionTerm.result) ++
    rule("ValueAtomicTerm", "ValueConcreteSetTerm", _.ValueConcreteSetTerm.result) ++    
    rule("ValueAtomicTerm", "True", c => pTmConst(Kernel.logical_true)) ++
    rule("ValueAtomicTerm", "False", c => pTmConst(Kernel.logical_false)) ++
    rule("ValueAtomicTerm", "EmptySet", c => pTmConst(Kernel.empty_set)) ++
    rule("ValueAtomicTerm", "QuoteOpen ValueQuotedTerm QuoteClose", c => pTmQuote(c.ValueQuotedTerm.result)) ++
    rule("ValueCombTerm", "ValueAtomicTerm", _.ValueAtomicTerm.result) ++
    rule("ValueCombTerm", "ValueCombTerm ValueAtomicTerm", 
      c => PTmComb(c.ValueCombTerm.resultAs[Preterm], c.ValueAtomicTerm.resultAs[Preterm], None, Pretype.PTyAny)) ++
    rule("ValuePureBinding", "IndexedName", c => Binding(parseIndexedName(c.IndexedName.text), None)) ++
    rule("ValueAnnotatedBinding", "IndexedName Colon Type", c => Binding(parseIndexedName(c.IndexedName.text), Some(TypeDomain(c.Type.resultAs[Pretype])))) ++    
    rule("ValueAnnotatedBinding", "IndexedName Elem ValueTerm", c => Binding(parseIndexedName(c.IndexedName.text), Some(SetDomain(c.ValueTerm.resultAs[Preterm])))) ++ 
    rule("ValueBinding", "ValuePureBinding", _.ValuePureBinding.result) ++
    rule("ValueBinding", "ValueAnnotatedBinding", _.ValueAnnotatedBinding.result) ++    
    rule("ValuePureBindings", "ValuePureBinding", c => List(c.ValuePureBinding.resultAs[Binding])) ++
    rule("ValuePureBindings", "ValuePureBindings ValuePureBinding", c => c.ValuePureBinding.resultAs[Binding] :: c.ValuePureBindings.resultAs[List[Binding]]) ++ 
    rule("ValueBindings", "ValuePureBindings", _.ValuePureBindings.result) ++
    rule("ValueBindings", "ValueAnnotatedBinding", c => List(c.ValueAnnotatedBinding.resultAs[Binding])) ++
    rule("ValueBindings", "ValueBindings Comma ValueBinding", c => c.ValueBinding.resultAs[Binding] :: c.ValueBindings.resultAs[List[Binding]]) ++ 
    rule("ValueSetUnaryOpTerm", "ValueCombTerm", _.ValueCombTerm.result) ++
    rule("ValueSetUnaryOpTerm", "Powerset ValueSetUnaryOpTerm", c => pTmUnaryOp(Kernel.set_power, c.ValueSetUnaryOpTerm.resultAs[Preterm])) ++
    rule("ValueSetUnaryOpTerm", "SetBigUnion ValueSetUnaryOpTerm", c => pTmUnaryOp(Kernel.set_bigunion, c.ValueSetUnaryOpTerm.resultAs[Preterm])) ++
    rule("ValueSetUnaryOpTerm", "SetBigIntersection ValueSetUnaryOpTerm", c => pTmUnaryOp(Kernel.set_bigintersection, c.ValueSetUnaryOpTerm.resultAs[Preterm])) ++
    rule("ValueSetIntersectionTerm", "ValueSetUnaryOpTerm", _.ValueSetUnaryOpTerm.result) ++
    rule("ValueSetIntersectionTerm", "ValueSetIntersectionTerm SetIntersection ValueSetUnaryOpTerm",
      c => pTmBinaryOp(Kernel.set_intersection, c.ValueSetIntersectionTerm.resultAs[Preterm], c.ValueSetUnaryOpTerm.resultAs[Preterm])) ++
    rule("ValueSetUnionTerm", "ValueSetIntersectionTerm", _.ValueSetIntersectionTerm.result) ++
    rule("ValueSetUnionTerm", "ValueSetUnionTerm SetUnion ValueSetIntersectionTerm",
      c => pTmBinaryOp(Kernel.set_union, c.ValueSetUnionTerm.resultAs[Preterm], c.ValueSetIntersectionTerm.resultAs[Preterm])) ++
    rule("ValueSetDiffTerm", "ValueSetUnionTerm", _.ValueSetUnionTerm.result) ++
    rule("ValueSetDiffTerm", "ValueSetDiffTerm SetDiff ValueSetUnionTerm", 
      c => pTmBinaryOp(Kernel.set_difference, c.ValueSetDiffTerm.resultAs[Preterm], c.ValueSetUnionTerm.resultAs[Preterm])) ++
    rule("ValueSetTerm", "ValueSetDiffTerm", _.ValueSetDiffTerm.result) ++
    rule("ValueSetBinaryRelationTerm", "ValueSetTerm", _.ValueSetTerm.result) ++
    rule("ValueSetBinaryRelationTerm", "ValueSetTerm_1 Elem ValueSetTerm_2", 
      c => pTmBinaryOp(Kernel.set_elementOf, c.ValueSetTerm_1.resultAs[Preterm], c.ValueSetTerm_2.resultAs[Preterm])) ++
    rule("ValueSetBinaryRelationTerm", "ValueSetTerm_1 NotElem ValueSetTerm_2", 
      c => pTmUnaryOp(Kernel.logical_not, pTmBinaryOp(Kernel.set_elementOf, c.ValueSetTerm_1.resultAs[Preterm], c.ValueSetTerm_2.resultAs[Preterm]))) ++    
    rule("ValueSetBinaryRelationTerm", "ValueSetTerm_1 Subset ValueSetTerm_2", 
      c => pTmBinaryOp(Kernel.set_subsetOf, c.ValueSetTerm_1.resultAs[Preterm], c.ValueSetTerm_2.resultAs[Preterm])) ++
    rule("ValueSetBinaryRelationTerm", "ValueSetTerm_1 NotSubset ValueSetTerm_2", 
      c => pTmUnaryOp(Kernel.logical_not, pTmBinaryOp(Kernel.set_subsetOf, c.ValueSetTerm_1.resultAs[Preterm], c.ValueSetTerm_2.resultAs[Preterm]))) ++    
    rule("ValueTypedTerm", "ValueSetBinaryRelationTerm", _.ValueSetBinaryRelationTerm.result) ++
    rule("ValueTypedTerm", "ValueTypedTerm Colon Type", c => PTmTyping(c.ValueTypedTerm.resultAs[Preterm], c.Type.resultAs[Pretype])) ++
    rule("ValueEqTerm", "ValueTypedTerm", _.ValueTypedTerm.result) ++
    rule("ValueEqTerm", "ValueTypedTerm_1 Eq ValueTypedTerm_2", c => pTmEquals(c.ValueTypedTerm_1.resultAs[Preterm], c.ValueTypedTerm_2.resultAs[Preterm])) ++
    rule("ValueEqTerm", "ValueTypedTerm_1 NotEq ValueTypedTerm_2", c => pTmUnaryOp(Kernel.logical_not, pTmEquals(c.ValueTypedTerm_1.resultAs[Preterm], c.ValueTypedTerm_2.resultAs[Preterm]))) ++
    rule("ValueNotTerm", "Not ValueNotTerm", c => pTmUnaryOp(Kernel.logical_not, c.ValueNotTerm.resultAs[Preterm])) ++
    rule("ValueNotTerm", "ValueEqTerm", _.ValueEqTerm.result) ++
    rule("ValueAndTerm", "ValueAndTerm And ValueNotTerm", c => pTmBinaryOp(Kernel.logical_and, c.ValueAndTerm.resultAs[Preterm], c.ValueNotTerm.resultAs[Preterm])) ++
    rule("ValueAndTerm", "ValueNotTerm", _.ValueNotTerm.result) ++
    rule("ValueOrTerm", "ValueOrTerm Or ValueAndTerm", c => pTmBinaryOp(Kernel.logical_or, c.ValueOrTerm.resultAs[Preterm], c.ValueAndTerm.resultAs[Preterm])) ++
    rule("ValueOrTerm", "ValueAndTerm", _.ValueAndTerm.result) ++
    rule("ValueImpliesTerm", "ValueOrTerm RightArrow ValueImpliesTerm", c => pTmBinaryOp(Kernel.implies, c.ValueOrTerm.resultAs[Preterm], c.ValueImpliesTerm.resultAs[Preterm])) ++
    rule("ValueImpliesTerm", "ValueOrTerm", _.ValueOrTerm.result) ++
    rule("ValuePropTerm", "ValueImpliesTerm", _.ValueImpliesTerm.result) ++
    rule("ValueAbsTerm", "ValuePropTerm", _.ValuePropTerm.result) ++
    rule("ValueAbsTerm", "ValueQuantifierTerm", _.ValueQuantifierTerm.result) ++
    rule("ValueQuantifierTerm", "Forall ValueBindings ValueQuantifierTerm", c => pTmForall(c.ValueBindings.resultAs[List[Binding]], c.ValueQuantifierTerm.resultAs[Preterm])) ++
    rule("ValueQuantifierTerm", "Exists ValueBindings ValueQuantifierTerm", c => pTmExists(c.ValueBindings.resultAs[List[Binding]], c.ValueQuantifierTerm.resultAs[Preterm])) ++
    rule("ValueQuantifierTerm", "NotExists ValueBindings ValueQuantifierTerm", c => pTmUnaryOp(Kernel.logical_not, pTmExists(c.ValueBindings.resultAs[List[Binding]], c.ValueQuantifierTerm.resultAs[Preterm]))) ++
    rule("ValueQuantifierTerm", "Forall ValueBindings Dot ValueAbsTerm", c => pTmForall(c.ValueBindings.resultAs[List[Binding]], c.ValueAbsTerm.resultAs[Preterm])) ++
    rule("ValueQuantifierTerm", "Exists ValueBindings Dot ValueAbsTerm", c => pTmExists(c.ValueBindings.resultAs[List[Binding]], c.ValueAbsTerm.resultAs[Preterm])) ++
    rule("ValueQuantifierTerm", "NotExists ValueBindings Dot ValueAbsTerm", c => pTmUnaryOp(Kernel.logical_not, pTmExists(c.ValueBindings.resultAs[List[Binding]], c.ValueAbsTerm.resultAs[Preterm]))) ++
    rule("ValueAbsTerm", "ValueBindings MapsTo ValueAbsTerm", c => pTmAbs(c.ValueBindings.resultAs[List[Binding]], c.ValueAbsTerm.resultAs[Preterm])) ++
    rule("ValueTermList", "ValueTerm", c => List(c.ValueTerm.resultAs[Preterm])) ++
    rule("ValueTermList", "ValueTermList Comma ValueTerm", c => c.ValueTerm.resultAs[Preterm] :: c.ValueTermList.resultAs[List[Preterm]]) ++
    rule("ValueTerm", "ValueAbsTerm", _.ValueAbsTerm.result)

val g_Pattern_term = 
    //rule("PatternNameTerm", "IndexedName", c => PTmName(parseName(c.IndexedName.text), PTyAny)) ++
    rule("PatternNameTerm", "Name", c => PTmName(parseName(c.Name.text), Pretype.PTyAny)) ++
    rule("PatternSetComprehensionTerm", "CurlyBracketOpen PatternTerm Bar PatternBindings CurlyBracketClose", 
      c => pTmSetComprehension(c.PatternBindings.resultAs[List[Binding]], c.PatternTerm.resultAs[Preterm], None)) ++
    rule("PatternSetComprehensionTerm", "CurlyBracketOpen PatternTerm_1 Bar PatternBindings Dot PatternTerm_2 CurlyBracketClose",  
      c => pTmSetComprehension(c.PatternBindings.resultAs[List[Binding]], c.PatternTerm_1.resultAs[Preterm], Some(c.PatternTerm_2.resultAs[Preterm]))) ++ 
    rule("PatternConcreteSetTerm", "CurlyBracketOpen PatternTermList CurlyBracketClose", c => pTmSet(c.PatternTermList.resultAs[List[Preterm]])) ++
    rule("PatternConcreteSetTerm", "CurlyBracketOpen CurlyBracketClose", c => pTmConst(Kernel.empty_set)) ++   
    rule("PatternAtomicTerm", "PatternNameTerm", _.PatternNameTerm.result) ++
    rule("PatternAtomicTerm", "RoundBracketOpen PatternTermList RoundBracketClose", c => pTmTuple(c.PatternTermList.resultAs[List[Preterm]])) ++
    rule("PatternAtomicTerm", "PatternSetComprehensionTerm", _.PatternSetComprehensionTerm.result) ++
    rule("PatternAtomicTerm", "PatternConcreteSetTerm", _.PatternConcreteSetTerm.result) ++    
    rule("PatternAtomicTerm", "True", c => pTmConst(Kernel.logical_true)) ++
    rule("PatternAtomicTerm", "False", c => pTmConst(Kernel.logical_false)) ++
    rule("PatternAtomicTerm", "EmptySet", c => pTmConst(Kernel.empty_set)) ++
    rule("PatternAtomicTerm", "QuoteOpen PatternQuotedTerm QuoteClose", c => pTmQuote(c.PatternQuotedTerm.result)) ++
    rule("PatternCombTerm", "PatternAtomicTerm", _.PatternAtomicTerm.result) ++
    rule("PatternCombTerm", "PatternCombTerm PatternAtomicTerm", 
      c => PTmComb(c.PatternCombTerm.resultAs[Preterm], c.PatternAtomicTerm.resultAs[Preterm], None, Pretype.PTyAny)) ++
    rule("PatternPureBinding", "IndexedName", c => Binding(parseIndexedName(c.IndexedName.text), None)) ++
    rule("PatternAnnotatedBinding", "IndexedName Colon Type", c => Binding(parseIndexedName(c.IndexedName.text), Some(TypeDomain(c.Type.resultAs[Pretype])))) ++    
    rule("PatternAnnotatedBinding", "IndexedName Elem PatternTerm", c => Binding(parseIndexedName(c.IndexedName.text), Some(SetDomain(c.PatternTerm.resultAs[Preterm])))) ++ 
    rule("PatternBinding", "PatternPureBinding", _.PatternPureBinding.result) ++
    rule("PatternBinding", "PatternAnnotatedBinding", _.PatternAnnotatedBinding.result) ++    
    rule("PatternPureBindings", "PatternPureBinding", c => List(c.PatternPureBinding.resultAs[Binding])) ++
    rule("PatternPureBindings", "PatternPureBindings PatternPureBinding", c => c.PatternPureBinding.resultAs[Binding] :: c.PatternPureBindings.resultAs[List[Binding]]) ++ 
    rule("PatternBindings", "PatternPureBindings", _.PatternPureBindings.result) ++
    rule("PatternBindings", "PatternAnnotatedBinding", c => List(c.PatternAnnotatedBinding.resultAs[Binding])) ++
    rule("PatternBindings", "PatternBindings Comma PatternBinding", c => c.PatternBinding.resultAs[Binding] :: c.PatternBindings.resultAs[List[Binding]]) ++ 
    rule("PatternSetUnaryOpTerm", "PatternCombTerm", _.PatternCombTerm.result) ++
    rule("PatternSetUnaryOpTerm", "Powerset PatternSetUnaryOpTerm", c => pTmUnaryOp(Kernel.set_power, c.PatternSetUnaryOpTerm.resultAs[Preterm])) ++
    rule("PatternSetUnaryOpTerm", "SetBigUnion PatternSetUnaryOpTerm", c => pTmUnaryOp(Kernel.set_bigunion, c.PatternSetUnaryOpTerm.resultAs[Preterm])) ++
    rule("PatternSetUnaryOpTerm", "SetBigIntersection PatternSetUnaryOpTerm", c => pTmUnaryOp(Kernel.set_bigintersection, c.PatternSetUnaryOpTerm.resultAs[Preterm])) ++
    rule("PatternSetIntersectionTerm", "PatternSetUnaryOpTerm", _.PatternSetUnaryOpTerm.result) ++
    rule("PatternSetIntersectionTerm", "PatternSetIntersectionTerm SetIntersection PatternSetUnaryOpTerm",
      c => pTmBinaryOp(Kernel.set_intersection, c.PatternSetIntersectionTerm.resultAs[Preterm], c.PatternSetUnaryOpTerm.resultAs[Preterm])) ++
    rule("PatternSetUnionTerm", "PatternSetIntersectionTerm", _.PatternSetIntersectionTerm.result) ++
    rule("PatternSetUnionTerm", "PatternSetUnionTerm SetUnion PatternSetIntersectionTerm",
      c => pTmBinaryOp(Kernel.set_union, c.PatternSetUnionTerm.resultAs[Preterm], c.PatternSetIntersectionTerm.resultAs[Preterm])) ++
    rule("PatternSetDiffTerm", "PatternSetUnionTerm", _.PatternSetUnionTerm.result) ++
    rule("PatternSetDiffTerm", "PatternSetDiffTerm SetDiff PatternSetUnionTerm", 
      c => pTmBinaryOp(Kernel.set_difference, c.PatternSetDiffTerm.resultAs[Preterm], c.PatternSetUnionTerm.resultAs[Preterm])) ++
    rule("PatternSetTerm", "PatternSetDiffTerm", _.PatternSetDiffTerm.result) ++
    rule("PatternSetBinaryRelationTerm", "PatternSetTerm", _.PatternSetTerm.result) ++
    rule("PatternSetBinaryRelationTerm", "PatternSetTerm_1 Elem PatternSetTerm_2", 
      c => pTmBinaryOp(Kernel.set_elementOf, c.PatternSetTerm_1.resultAs[Preterm], c.PatternSetTerm_2.resultAs[Preterm])) ++
    rule("PatternSetBinaryRelationTerm", "PatternSetTerm_1 NotElem PatternSetTerm_2", 
      c => pTmUnaryOp(Kernel.logical_not, pTmBinaryOp(Kernel.set_elementOf, c.PatternSetTerm_1.resultAs[Preterm], c.PatternSetTerm_2.resultAs[Preterm]))) ++    
    rule("PatternSetBinaryRelationTerm", "PatternSetTerm_1 Subset PatternSetTerm_2", 
      c => pTmBinaryOp(Kernel.set_subsetOf, c.PatternSetTerm_1.resultAs[Preterm], c.PatternSetTerm_2.resultAs[Preterm])) ++
    rule("PatternSetBinaryRelationTerm", "PatternSetTerm_1 NotSubset PatternSetTerm_2", 
      c => pTmUnaryOp(Kernel.logical_not, pTmBinaryOp(Kernel.set_subsetOf, c.PatternSetTerm_1.resultAs[Preterm], c.PatternSetTerm_2.resultAs[Preterm]))) ++    
    rule("PatternTypedTerm", "PatternSetBinaryRelationTerm", _.PatternSetBinaryRelationTerm.result) ++
    rule("PatternTypedTerm", "PatternTypedTerm Colon Type", c => PTmTyping(c.PatternTypedTerm.resultAs[Preterm], c.Type.resultAs[Pretype])) ++
    rule("PatternEqTerm", "PatternTypedTerm", _.PatternTypedTerm.result) ++
    rule("PatternEqTerm", "PatternTypedTerm_1 Eq PatternTypedTerm_2", c => pTmEquals(c.PatternTypedTerm_1.resultAs[Preterm], c.PatternTypedTerm_2.resultAs[Preterm])) ++
    rule("PatternEqTerm", "PatternTypedTerm_1 NotEq PatternTypedTerm_2", c => pTmUnaryOp(Kernel.logical_not, pTmEquals(c.PatternTypedTerm_1.resultAs[Preterm], c.PatternTypedTerm_2.resultAs[Preterm]))) ++
    rule("PatternNotTerm", "Not PatternNotTerm", c => pTmUnaryOp(Kernel.logical_not, c.PatternNotTerm.resultAs[Preterm])) ++
    rule("PatternNotTerm", "PatternEqTerm", _.PatternEqTerm.result) ++
    rule("PatternAndTerm", "PatternAndTerm And PatternNotTerm", c => pTmBinaryOp(Kernel.logical_and, c.PatternAndTerm.resultAs[Preterm], c.PatternNotTerm.resultAs[Preterm])) ++
    rule("PatternAndTerm", "PatternNotTerm", _.PatternNotTerm.result) ++
    rule("PatternOrTerm", "PatternOrTerm Or PatternAndTerm", c => pTmBinaryOp(Kernel.logical_or, c.PatternOrTerm.resultAs[Preterm], c.PatternAndTerm.resultAs[Preterm])) ++
    rule("PatternOrTerm", "PatternAndTerm", _.PatternAndTerm.result) ++
    rule("PatternImpliesTerm", "PatternOrTerm RightArrow PatternImpliesTerm", c => pTmBinaryOp(Kernel.implies, c.PatternOrTerm.resultAs[Preterm], c.PatternImpliesTerm.resultAs[Preterm])) ++
    rule("PatternImpliesTerm", "PatternOrTerm", _.PatternOrTerm.result) ++
    rule("PatternPropTerm", "PatternImpliesTerm", _.PatternImpliesTerm.result) ++
    rule("PatternAbsTerm", "PatternPropTerm", _.PatternPropTerm.result) ++
    rule("PatternAbsTerm", "PatternQuantifierTerm", _.PatternQuantifierTerm.result) ++
    rule("PatternQuantifierTerm", "Forall PatternBindings PatternQuantifierTerm", c => pTmForall(c.PatternBindings.resultAs[List[Binding]], c.PatternQuantifierTerm.resultAs[Preterm])) ++
    rule("PatternQuantifierTerm", "Exists PatternBindings PatternQuantifierTerm", c => pTmExists(c.PatternBindings.resultAs[List[Binding]], c.PatternQuantifierTerm.resultAs[Preterm])) ++
    rule("PatternQuantifierTerm", "NotExists PatternBindings PatternQuantifierTerm", c => pTmUnaryOp(Kernel.logical_not, pTmExists(c.PatternBindings.resultAs[List[Binding]], c.PatternQuantifierTerm.resultAs[Preterm]))) ++
    rule("PatternQuantifierTerm", "Forall PatternBindings Dot PatternAbsTerm", c => pTmForall(c.PatternBindings.resultAs[List[Binding]], c.PatternAbsTerm.resultAs[Preterm])) ++
    rule("PatternQuantifierTerm", "Exists PatternBindings Dot PatternAbsTerm", c => pTmExists(c.PatternBindings.resultAs[List[Binding]], c.PatternAbsTerm.resultAs[Preterm])) ++
    rule("PatternQuantifierTerm", "NotExists PatternBindings Dot PatternAbsTerm", c => pTmUnaryOp(Kernel.logical_not, pTmExists(c.PatternBindings.resultAs[List[Binding]], c.PatternAbsTerm.resultAs[Preterm]))) ++
    rule("PatternAbsTerm", "PatternBindings MapsTo PatternAbsTerm", c => pTmAbs(c.PatternBindings.resultAs[List[Binding]], c.PatternAbsTerm.resultAs[Preterm])) ++
    rule("PatternTermList", "PatternTerm", c => List(c.PatternTerm.resultAs[Preterm])) ++
    rule("PatternTermList", "PatternTermList Comma PatternTerm", c => c.PatternTerm.resultAs[Preterm] :: c.PatternTermList.resultAs[List[Preterm]]) ++
    rule("PatternTerm", "PatternAbsTerm", _.PatternAbsTerm.result)


  def grammar = 
    literals ++
    g_type ++
    g_Value_term ++
    g_Pattern_term
 
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
    grammar.parser.parse(d, "ValueTerm", 0) match {
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

  private def isBalanced(s : String, open : String, close : String) : Boolean = {
    var count = 0
    var i = 0
    do {
      val jOpen = s.indexOf(open, i)
      val jClose = s.indexOf(close, i)
      if (jOpen >= 0 && (jClose < 0 || jClose > jOpen)) {
        i = jOpen + 1
        count = count + 1
      } else if (jClose >= 0 && (jOpen < 0 || jOpen > jClose)) {
        i = jClose + 1
        count = count - 1
      } else i = -1
    } while (count > 0)
    s.length == i
  }

  private def protect(s : String) : String = {
    if (containsSpace(s)) {
      if ((s.startsWith("(") && isBalanced(s, "(", ")")) ||
          (s.startsWith("{") && isBalanced(s, "{", "}")) ||
          (s.startsWith("[") && isBalanced(s, "[", "]")))
        s
      else
        "(" + s + ")" 
    } else s
  }

  def printType(ty : Type) : String = {
    ty match {
      case Type.Universe => "𝒰"
      case Type.Prop => "ℙ"
      case Type.Fun(domain, range) => protect(printType(domain)) + " → " + printType(range)
    }  
  }

  def printTypeAnnotation(ty : Type) : String = {
    ty match {
      case Type.Universe => ""
      case _ => " : " + printType(ty)
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

  def printBinary(nameRes : NameResolution.Resolution, vars : Set[IndexedName], op : String, left : Term, right : Term) : String = {
    protect(printTerm(nameRes, vars, left)) + " " + op + " " + protect(printTerm(nameRes, vars, right))
  }

  def printUnary(nameRes : NameResolution.Resolution, vars : Set[IndexedName], op : String, tm : Term) : String = {
    op + " " + protect(printTerm(nameRes, vars, tm))
  }

  private val binaryOp : Map[Name, String] = 
    Map(
      Kernel.set_union -> "∪",
      Kernel.set_intersection -> "∩",
      Kernel.set_difference -> "∖",
      Kernel.set_elementOf -> "∈",
      Kernel.set_subsetOf -> "⊂",
      Kernel.logical_and -> "∧",
      Kernel.logical_or -> "∨",
      Kernel.implies -> "→"
    )

  private val unaryOp : Map[Name, String] = 
    Map(
      Kernel.logical_not -> "¬",
      Kernel.set_bigunion -> "⋃",
      Kernel.set_bigintersection -> "⋂",
      Kernel.set_power -> "𝒫"
    )

  private val nullaryOp : Map[Name, String] = 
    Map(
      Kernel.empty_set -> "∅",
      Kernel.logical_true -> "⊤",
      Kernel.logical_false -> "⊥"
    )

  def printTerm(nameRes : NameResolution.Resolution, tm : Term) : String = {
    val (t, _) = preparePrinting(tm)
    printTerm(nameRes, Set(), t)
  }

  // We check whether there are unqualified constants in this term which clash with variables. 
  // If yes, we rename the variables that cause the clash. 
  private def preparePrinting(tm : Term) : (Term, Set[IndexedName]) = {
    import Term._
    tm match {
      case Const(name) =>
        if (name.namespace.isDefined) 
          (tm, Set())
        else 
          (tm, Set(name.name))
      case Comb(f, g) =>
        val (u, fconsts) = preparePrinting(f)
        val (v, gconsts) = preparePrinting(g)
        (Comb(u, v), fconsts ++ gconsts)
      case Abs(name, ty, body) =>
        val (u, consts) = preparePrinting(body)
        if (consts.contains(name)) {
          var i : Integer = 
            KernelUtils.findHighestVarIndex(body) match {
              case Some(Some(i)) => i
              case _ => 1
            }
          var n : IndexedName = null
          do {
            n = IndexedName(name.name, Some(i))
            i = i + 1
          } while (consts.contains(n))
          (Abs(n, ty, KernelUtils.substVar(u, name, Var(n))), consts)
        } else {
          (Abs(name, ty, u), consts)
        }
      case _ => 
        (tm, Set()) 
    }
  }

  private def printNameInContext(nameRes : NameResolution.Resolution, vars : Set[IndexedName], name : Name) : String = {
    if (name.namespace.isDefined && !vars.contains(name.name)) {
      nameRes.get(name.name) match {
        case Some(n) if n == name => printName(name.name)
        case _ => printName(name)
      }
    } else printName(name)
  }

  private def printTerm(nameRes : NameResolution.Resolution, vars : Set[IndexedName], tm : Term) : String = {
    tm match {
      case Term.Comb(Term.PolyConst(Kernel.forall, _), Term.Abs(name, ty, body)) =>
        "∀ " + printName(name) + printTypeAnnotation(ty) + ". " + printTerm(nameRes, vars + name, body)
      case Term.Comb(Term.Comb(Term.Const(Kernel.forallin), set), Term.Abs(name, ty, body)) =>
        "∀ " + printName(name) + " ∈ " + printTerm(nameRes, vars, set) + ". " + printTerm(nameRes, vars + name, body)
      case Term.Comb(Term.PolyConst(Kernel.exists, _), Term.Abs(name, ty, body)) =>
        "∃ " + printName(name) + printTypeAnnotation(ty) + ". " + printTerm(nameRes, vars + name, body)
      case Term.Comb(Term.Comb(Term.Const(Kernel.existsin), set), Term.Abs(name, ty, body)) =>
        "∃ " + printName(name) + " ∈ " + printTerm(nameRes, vars, set) + ". " + printTerm(nameRes, vars + name, body)
      case Term.Comb(Term.Comb(Term.Const(Kernel.pair), left), right) =>
        "(" + printTerm(nameRes, vars, left) + ", " + printTerm(nameRes, vars, right) + ")"
      case Term.Comb(Term.Comb(Term.Const(op), left), right) if binaryOp.get(op).isDefined =>
        printBinary(nameRes, vars, binaryOp(op), left, right)
      case Term.Comb(Term.Const(op), tm) if unaryOp.get(op).isDefined =>
        printUnary(nameRes, vars, unaryOp(op), tm)
      case Term.Const(op) if nullaryOp.get(op).isDefined =>
        nullaryOp(op)
      case Term.Comb(Term.Comb(Term.PolyConst(Kernel.equals, _), left), right) =>
        printBinary(nameRes, vars, "=", left, right)
      case Term.Comb(Term.Comb(Term.Const(Kernel.funapply), f), x) =>
        protect(printTerm(nameRes, vars, f)) + " " + protect(printTerm(nameRes, vars, x))
      case Term.Comb(Term.Const(Kernel.set_singleton), tm) =>
        "{" + printTerm(nameRes, vars, tm) + "}"
      case Term.Comb(Term.Comb(Term.Const(Kernel.set_replacement), 
        Term.Comb(Term.Comb(Term.Const(Kernel.set_separation), tm), Term.Abs(pname, _, pred))), Term.Abs(name, _, body)) if name == pname =>
        "{" + printTerm(nameRes, vars + name, body) + " | " + printName(name) + " ∈ " + printTerm(nameRes, vars, tm) + ". " + printTerm(nameRes, vars + pname, pred) + "}"
      case Term.Comb(Term.Comb(Term.Const(Kernel.set_replacement), tm), Term.Abs(name, _, body)) =>
        "{" + printTerm(nameRes, vars + name, body) + " | " + printName(name) + " ∈ " + printTerm(nameRes, vars, tm) + "}"
      case Term.PolyConst(name, alpha) =>
        val ty = 
          name match {
            case Kernel.forall => Type.Fun(Type.Fun(alpha, Type.Prop), Type.Prop)
            case Kernel.exists => Type.Fun(Type.Fun(alpha, Type.Prop), Type.Prop)
            case Kernel.equals => Type.Fun(alpha, Type.Fun(alpha, Type.Prop))
            case _ => Utils.failwith("this is not a polymorphic name: "+name)
          }
        printNameInContext(nameRes, vars, name) + printTypeAnnotation(ty)
      case Term.Const(name : Name) => 
        printNameInContext(nameRes, vars, name)
      case Term.Comb(f, x) =>
        protect(printTerm(nameRes, vars, f)) + " " + protect(printTerm(nameRes, vars, x))
      case Term.Abs(name, ty, body) =>
        printName(name) + printTypeAnnotation(ty) + " ↦ " + printTerm(nameRes, vars + name, body)
      case Term.Var(name) =>
        printName(name)
    }
  }
      
}