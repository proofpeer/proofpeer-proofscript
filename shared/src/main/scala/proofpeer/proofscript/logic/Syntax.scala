package proofpeer.proofscript.logic

import proofpeer.general.StringUtils._
import proofpeer.indent._
import proofpeer.indent.regex._
import Utils._

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

  def lex(terminal : String, expr : RegularExpr, prio : Option[Int] = None) : Grammar = 
    proofpeer.indent.rule(terminal, expr, prio, "\\root")
   
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
      Name(Some(Namespace(namespace)), indexedname)
    }
  }

  def rule(n : String, rhs : String, action : ParseContext => Any) : Grammar =  {
    val (r, i) = string2rhsi(rhs)
    val noparams = proofpeer.indent.ParseParam.noParams(r.length)
    Grammar(ParseRule(n, r, i, noparams, Constraint.unconstrained, action))

  }

  val lowerLetter = chars('a', 'z')
  val upperLetter = chars('A', 'Z')
  val letter = ALT(lowerLetter, upperLetter)
  val digit = chars('0', '9')
  val digits = REPEAT1(digit)
  val underscore = char('_')
  val backslash = char('\\')
  val id = seq(letter, REPEAT(alt(letter, digit, 
      SEQ(underscore, letter))))
  val relativeNamespace = SEQ(REPEAT(SEQ(id, backslash)), id)
  val absoluteNamespace = SEQ(backslash, relativeNamespace)
  val indexedName = SEQ(id, OPT(SEQ(underscore, digits)))
  val relativeName = SEQ(indexedName, REPEAT(SEQ(backslash, indexedName)))

  val literals = 
    lex("LowerLetter", lowerLetter) ++
    lex("UpperLetter", upperLetter) ++
    lex("Letter", letter) ++
    lex("Digit", digit) ++
    lex("Digits", digits) ++
    lex("Underscore", underscore) ++
    lex("Backslash", backslash) ++
    lex("Id", id, Some(1)) ++
    lex("RelativeNamespace", relativeNamespace) ++
    lex("AbsoluteNamespace", absoluteNamespace) ++
    lex("Namespace", ALT(relativeNamespace, absoluteNamespace)) ++
    lex("IndexedName", indexedName, Some(1)) ++
    lex("RelativeName", relativeName) ++
    lex("Name", SEQ(OPT(backslash), relativeName), Some(1)) ++
    lex("Dot", char('.')) ++
    lex("Comma", char(',')) ++
    lex("Eq", char('=')) ++
    lex("NotEq", char(0x2260)) ++
    lex("RoundBracketOpen", char('(')) ++
    lex("RoundBracketClose", char(')')) ++
    lex("CurlyBracketOpen", char('{')) ++
    lex("CurlyBracketClose", char('}')) ++
    lex("Bar", char('|')) ++
    lex("RightArrow", char(0x2192)) ++ 
    lex("Colon", char(':')) ++
    lex("QuoteOpen", char(0x2039)) ++ 
    lex("QuoteClose", char(0x203A)) ++
    lex("DoubleQuoteOpen", char(0xAB)) ++ 
    lex("DoubleQuoteClose", char(0xBB)) ++    
    lex("Forall", char(0x2200)) ++
    lex("Exists", char(0x2203)) ++
    lex("NotExists", char(0x2204)) ++    
    lex("Universe", char(0x1D4B0)) ++
    lex("Prop", char(0x2119)) ++
    lex("Powerset", char(0x1D4AB)) ++ 
    lex("MapsTo", char(0x21A6)) ++
    lex("True", char(0x22A4)) ++
    lex("False", char(0x22A5)) ++
    lex("Elem", char(0x2208)) ++
    lex("NotElem", char(0x2209)) ++ 
    lex("Subset", char(0x2282)) ++
    lex("NotSubset", char(0x2284)) ++    
    lex("Or", char(0x2228)) ++
    lex("And", char(0x2227)) ++
    lex("Not", char(0x00AC)) ++
    lex("EmptySet", char(0x2205)) ++ 
    lex("SetDiff", char(0x2216)) ++
    lex("SetUnion", char(0x222A)) ++
    lex("SetIntersection", char(0x2229)) ++ 
    lex("SetBigUnion", char(0x22C3)) ++
    lex("SetBigIntersection", char(0x22C2)) 
      
  val g_Value_type = 
    rule("ValueAtomicType", "Universe", c => PTyUniverse) ++
    rule("ValueAtomicType", "Prop", c => PTyProp) ++
    rule("ValueAtomicType", "Underscore", c => PTyAny) ++
    rule("ValueAtomicType", "RoundBracketOpen ValueType RoundBracketClose", _.ValueType[Any]) ++
    rule("ValueAtomicType", "QuoteOpen ValueQuotedType QuoteClose", c => PTyQuote(c.ValueQuotedType)) ++
    rule("ValueAtomicType", "DoubleQuoteOpen ValueQuotedType DoubleQuoteClose", c => PTyQuote(c.ValueQuotedType)) ++
    rule("ValueType", "ValueAtomicType", _.ValueAtomicType[Any]) ++
    rule("ValueType", "ValueAtomicType RightArrow ValueType", c => PTyFun(c.ValueAtomicType, c.ValueType)) 

  val g_Pattern_type = 
    rule("PatternAtomicType", "Universe", c => PTyUniverse) ++
    rule("PatternAtomicType", "Prop", c => PTyProp) ++
    rule("PatternAtomicType", "Underscore", c => PTyAny) ++
    rule("PatternAtomicType", "RoundBracketOpen PatternType RoundBracketClose", _.PatternType[Any]) ++
    rule("PatternAtomicType", "QuoteOpen PatternQuotedType QuoteClose", c => PTyQuote(c.PatternQuotedType)) ++
    rule("PatternAtomicType", "DoubleQuoteOpen ValueQuotedType DoubleQuoteClose", c => PTyQuote(c.ValueQuotedType)) ++
    rule("PatternType", "PatternAtomicType", _.PatternAtomicType[Any]) ++
    rule("PatternType", "PatternAtomicType RightArrow PatternType", c => PTyFun(c.PatternAtomicType, c.PatternType)) 
    
val g_Value_term = 
    rule("ValueNameTerm", "Name", c => PTmName(parseName(c.text("Name")), Pretype.PTyAny)) ++
    rule("ValueSetComprehensionTerm", "CurlyBracketOpen ValueTerm Bar ValueBindings CurlyBracketClose", 
      c => pTmSetComprehension(c.ValueBindings, c.ValueTerm, None)) ++
    rule("ValueSetComprehensionTerm", "CurlyBracketOpen ValueTerm_1 Bar ValueBindings Dot ValueTerm_2 CurlyBracketClose",  
      c => pTmSetComprehension(c.ValueBindings, c.ValueTerm_1, Some(c.ValueTerm_2[Preterm]))) ++ 
    rule("ValueConcreteSetTerm", "CurlyBracketOpen ValueTermList CurlyBracketClose", c => pTmSet(c.ValueTermList)) ++
    rule("ValueConcreteSetTerm", "CurlyBracketOpen CurlyBracketClose", c => pTmConst(Kernel.empty_set)) ++   
    rule("ValueAtomicTerm", "ValueNameTerm", _.ValueNameTerm[Any]) ++
    rule("ValueAtomicTerm", "RoundBracketOpen ValueTermList RoundBracketClose", c => pTmTuple(c.ValueTermList)) ++
    rule("ValueAtomicTerm", "ValueSetComprehensionTerm", _.ValueSetComprehensionTerm[Any]) ++
    rule("ValueAtomicTerm", "ValueConcreteSetTerm", _.ValueConcreteSetTerm[Any]) ++    
    rule("ValueAtomicTerm", "True", c => pTmConst(Kernel.logical_true)) ++
    rule("ValueAtomicTerm", "False", c => pTmConst(Kernel.logical_false)) ++
    rule("ValueAtomicTerm", "EmptySet", c => pTmConst(Kernel.empty_set)) ++
    rule("ValueAtomicTerm", "QuoteOpen ValueQuotedTerm QuoteClose", c => pTmQuote(c.ValueQuotedTerm)) ++
    rule("ValueAtomicTerm", "DoubleQuoteOpen ValueQuotedTerm DoubleQuoteClose", c => pTmQuote(c.ValueQuotedTerm)) ++
    rule("ValueCombTerm", "ValueAtomicTerm", _.ValueAtomicTerm[Any]) ++
    rule("ValueCombTerm", "ValueCombTerm ValueAtomicTerm", 
      c => PTmComb(c.ValueCombTerm, c.ValueAtomicTerm, None, Pretype.PTyAny)) ++
    rule("ValuePureBinding", "IndexedName", c => Binding(parseIndexedName(c.text("IndexedName")), None)) ++
    rule("ValueAnnotatedBinding", "IndexedName Colon ValueType", c => Binding(parseIndexedName(c.text("IndexedName")), Some(TypeDomain(c.ValueType)))) ++    
    rule("ValueAnnotatedBinding", "IndexedName Elem ValueTerm", c => Binding(parseIndexedName(c.text("IndexedName")), Some(SetDomain(c.ValueTerm)))) ++ 
    rule("ValueBinding", "ValuePureBinding", _.ValuePureBinding[Any]) ++
    rule("ValueBinding", "ValueAnnotatedBinding", _.ValueAnnotatedBinding[Any]) ++    
    rule("ValuePureBindings", "ValuePureBinding", c => List(c.ValuePureBinding[Any])) ++
    rule("ValuePureBindings", "ValuePureBindings ValuePureBinding", c => c.ValuePureBinding[Binding] :: c.ValuePureBindings[List[Binding]]) ++ 
    rule("ValueBindings", "ValuePureBindings", _.ValuePureBindings[Any]) ++
    rule("ValueBindings", "ValueAnnotatedBinding", c => List(c.ValueAnnotatedBinding[Any])) ++
    rule("ValueBindings", "ValueBindings Comma ValueBinding", c => c.ValueBinding[Binding] :: c.ValueBindings[List[Binding]]) ++ 
    rule("ValueSetUnaryOpTerm", "ValueCombTerm", _.ValueCombTerm[Any]) ++
    rule("ValueSetUnaryOpTerm", "Powerset ValueSetUnaryOpTerm", c => pTmUnaryOp(Kernel.set_power, c.ValueSetUnaryOpTerm)) ++
    rule("ValueSetUnaryOpTerm", "SetBigUnion ValueSetUnaryOpTerm", c => pTmUnaryOp(Kernel.set_bigunion, c.ValueSetUnaryOpTerm)) ++
    rule("ValueSetUnaryOpTerm", "SetBigIntersection ValueSetUnaryOpTerm", c => pTmUnaryOp(Kernel.set_bigintersection, c.ValueSetUnaryOpTerm)) ++
    rule("ValueSetIntersectionTerm", "ValueSetUnaryOpTerm", _.ValueSetUnaryOpTerm[Any]) ++
    rule("ValueSetIntersectionTerm", "ValueSetIntersectionTerm SetIntersection ValueSetUnaryOpTerm",
      c => pTmBinaryOp(Kernel.set_intersection, c.ValueSetIntersectionTerm, c.ValueSetUnaryOpTerm)) ++
    rule("ValueSetUnionTerm", "ValueSetIntersectionTerm", _.ValueSetIntersectionTerm[Any]) ++
    rule("ValueSetUnionTerm", "ValueSetUnionTerm SetUnion ValueSetIntersectionTerm",
      c => pTmBinaryOp(Kernel.set_union, c.ValueSetUnionTerm, c.ValueSetIntersectionTerm)) ++
    rule("ValueSetDiffTerm", "ValueSetUnionTerm", _.ValueSetUnionTerm[Any]) ++
    rule("ValueSetDiffTerm", "ValueSetDiffTerm SetDiff ValueSetUnionTerm", 
      c => pTmBinaryOp(Kernel.set_difference, c.ValueSetDiffTerm, c.ValueSetUnionTerm)) ++
    rule("ValueSetTerm", "ValueSetDiffTerm", _.ValueSetDiffTerm[Any]) ++
    rule("ValueSetBinaryRelationTerm", "ValueSetTerm", _.ValueSetTerm[Any]) ++
    rule("ValueSetBinaryRelationTerm", "ValueSetTerm_1 Elem ValueSetTerm_2", 
      c => pTmBinaryOp(Kernel.set_elementOf, c.ValueSetTerm_1, c.ValueSetTerm_2)) ++
    rule("ValueSetBinaryRelationTerm", "ValueSetTerm_1 NotElem ValueSetTerm_2", 
      c => pTmUnaryOp(Kernel.logical_not, pTmBinaryOp(Kernel.set_elementOf, c.ValueSetTerm_1, c.ValueSetTerm_2))) ++    
    rule("ValueSetBinaryRelationTerm", "ValueSetTerm_1 Subset ValueSetTerm_2", 
      c => pTmBinaryOp(Kernel.set_subsetOf, c.ValueSetTerm_1, c.ValueSetTerm_2)) ++
    rule("ValueSetBinaryRelationTerm", "ValueSetTerm_1 NotSubset ValueSetTerm_2", 
      c => pTmUnaryOp(Kernel.logical_not, pTmBinaryOp(Kernel.set_subsetOf, c.ValueSetTerm_1, c.ValueSetTerm_2))) ++    
    rule("ValueRelationTerm", "ValueSetBinaryRelationTerm", _.ValueSetBinaryRelationTerm[Any]) ++
    rule("ValueEqTerm", "ValueRelationTerm", _.ValueRelationTerm[Any]) ++
    rule("ValueEqTerm", "ValueRelationTerm_1 Eq ValueRelationTerm_2", c => pTmEquals(c.ValueRelationTerm_1, c.ValueRelationTerm_2)) ++
    rule("ValueEqTerm", "ValueRelationTerm_1 NotEq ValueRelationTerm_2", c => pTmUnaryOp(Kernel.logical_not, pTmEquals(c.ValueRelationTerm_1, c.ValueRelationTerm_2))) ++
    rule("ValueNotTerm", "Not ValueNotTerm", c => pTmUnaryOp(Kernel.logical_not, c.ValueNotTerm)) ++
    rule("ValueNotTerm", "ValueEqTerm", _.ValueEqTerm[Any]) ++
    rule("ValueAndTerm", "ValueAndTerm And ValueNotTerm", c => pTmBinaryOp(Kernel.logical_and, c.ValueAndTerm, c.ValueNotTerm)) ++
    rule("ValueAndTerm", "ValueNotTerm", _.ValueNotTerm[Any]) ++
    rule("ValueOrTerm", "ValueOrTerm Or ValueAndTerm", c => pTmBinaryOp(Kernel.logical_or, c.ValueOrTerm, c.ValueAndTerm)) ++
    rule("ValueOrTerm", "ValueAndTerm", _.ValueAndTerm[Any]) ++
    rule("ValueImpliesTerm", "ValueOrTerm RightArrow ValueImpliesTerm", c => pTmBinaryOp(Kernel.implies, c.ValueOrTerm, c.ValueImpliesTerm)) ++
    rule("ValueImpliesTerm", "ValueOrTerm", _.ValueOrTerm[Any]) ++
    rule("ValuePropTerm", "ValueImpliesTerm", _.ValueImpliesTerm[Any]) ++
    rule("ValueTypedTerm", "ValuePropTerm", _.ValuePropTerm[Any]) ++
    rule("ValueTypedTerm", "ValueTypedTerm Colon ValueType", c => PTmTyping(c.ValueTypedTerm, c.ValueType)) ++
    rule("ValueAbsTerm", "ValueTypedTerm", _.ValueTypedTerm[Any]) ++
    rule("ValueAbsTerm", "ValueQuantifierTerm", _.ValueQuantifierTerm[Any]) ++
    rule("ValueQuantifierTerm", "Forall ValueBindings ValueQuantifierTerm", c => pTmForall(c.ValueBindings[List[Binding]], c.ValueQuantifierTerm[Preterm])) ++
    rule("ValueQuantifierTerm", "Exists ValueBindings ValueQuantifierTerm", c => pTmExists(c.ValueBindings[List[Binding]], c.ValueQuantifierTerm[Preterm])) ++
    rule("ValueQuantifierTerm", "NotExists ValueBindings ValueQuantifierTerm", c => pTmUnaryOp(Kernel.logical_not, pTmExists(c.ValueBindings[List[Binding]], c.ValueQuantifierTerm[Preterm]))) ++
    rule("ValueQuantifierTerm", "Forall ValueBindings Dot ValueAbsTerm", c => pTmForall(c.ValueBindings[List[Binding]], c.ValueAbsTerm[Preterm])) ++
    rule("ValueQuantifierTerm", "Exists ValueBindings Dot ValueAbsTerm", c => pTmExists(c.ValueBindings[List[Binding]], c.ValueAbsTerm[Preterm])) ++
    rule("ValueQuantifierTerm", "NotExists ValueBindings Dot ValueAbsTerm", c => pTmUnaryOp(Kernel.logical_not, pTmExists(c.ValueBindings[List[Binding]], c.ValueAbsTerm[Preterm]))) ++
    rule("ValueAbsTerm", "ValueBindings MapsTo ValueAbsTerm", c => pTmAbs(c.ValueBindings[List[Binding]], c.ValueAbsTerm[Preterm])) ++
    rule("ValueTerm", "ValueAbsTerm", _.ValueAbsTerm[Any]) ++
    rule("ValueTermList", "ValueTerm", c => List(c.ValueTerm[Preterm])) ++
    rule("ValueTermList", "ValueTermList Comma ValueTerm", c => c.ValueTerm[Preterm] :: c.ValueTermList[List[Preterm]]) 

val g_Pattern_term = 
    rule("PatternNameTerm", "Name", c => PTmName(parseName(c.text("Name")), Pretype.PTyAny)) ++
    rule("PatternSetComprehensionTerm", "CurlyBracketOpen PatternTerm Bar PatternBindings CurlyBracketClose", 
      c => pTmSetComprehension(c.PatternBindings, c.PatternTerm, None)) ++
    rule("PatternSetComprehensionTerm", "CurlyBracketOpen PatternTerm_1 Bar PatternBindings Dot PatternTerm_2 CurlyBracketClose",  
      c => pTmSetComprehension(c.PatternBindings, c.PatternTerm_1, Some(c.PatternTerm_2[Preterm]))) ++ 
    rule("PatternConcreteSetTerm", "CurlyBracketOpen PatternTermList CurlyBracketClose", c => pTmSet(c.PatternTermList)) ++
    rule("PatternConcreteSetTerm", "CurlyBracketOpen CurlyBracketClose", c => pTmConst(Kernel.empty_set)) ++   
    rule("PatternAtomicTerm", "PatternNameTerm", _.PatternNameTerm[Any]) ++
    rule("PatternAtomicTerm", "RoundBracketOpen PatternTermList RoundBracketClose", c => pTmTuple(c.PatternTermList)) ++
    rule("PatternAtomicTerm", "PatternSetComprehensionTerm", _.PatternSetComprehensionTerm[Any]) ++
    rule("PatternAtomicTerm", "PatternConcreteSetTerm", _.PatternConcreteSetTerm[Any]) ++    
    rule("PatternAtomicTerm", "True", c => pTmConst(Kernel.logical_true)) ++
    rule("PatternAtomicTerm", "False", c => pTmConst(Kernel.logical_false)) ++
    rule("PatternAtomicTerm", "EmptySet", c => pTmConst(Kernel.empty_set)) ++
    rule("PatternAtomicTerm", "QuoteOpen PatternQuotedTerm QuoteClose", c => pTmQuote(c.PatternQuotedTerm)) ++
    rule("PatternAtomicTerm", "DoubleQuoteOpen ValueQuotedTerm DoubleQuoteClose", c => pTmQuote(c.ValueQuotedTerm)) ++
    rule("PatternCombTerm", "PatternAtomicTerm", _.PatternAtomicTerm[Any]) ++
    rule("PatternCombTerm", "PatternCombTerm PatternAtomicTerm", 
      c => PTmComb(c.PatternCombTerm, c.PatternAtomicTerm, None, Pretype.PTyAny)) ++
    rule("PatternPureBinding", "IndexedName", c => Binding(parseIndexedName(c.text("IndexedName")), None)) ++
    rule("PatternAnnotatedBinding", "IndexedName Colon PatternType", c => Binding(parseIndexedName(c.text("IndexedName")), Some(TypeDomain(c.PatternType)))) ++    
    rule("PatternAnnotatedBinding", "IndexedName Elem PatternTerm", c => Binding(parseIndexedName(c.text("IndexedName")), Some(SetDomain(c.PatternTerm)))) ++ 
    rule("PatternBinding", "PatternPureBinding", _.PatternPureBinding[Any]) ++
    rule("PatternBinding", "PatternAnnotatedBinding", _.PatternAnnotatedBinding[Any]) ++    
    rule("PatternPureBindings", "PatternPureBinding", c => List(c.PatternPureBinding[Any])) ++
    rule("PatternPureBindings", "PatternPureBindings PatternPureBinding", c => c.PatternPureBinding[Binding] :: c.PatternPureBindings[List[Binding]]) ++ 
    rule("PatternBindings", "PatternPureBindings", _.PatternPureBindings[Any]) ++
    rule("PatternBindings", "PatternAnnotatedBinding", c => List(c.PatternAnnotatedBinding[Any])) ++
    rule("PatternBindings", "PatternBindings Comma PatternBinding", c => c.PatternBinding[Binding] :: c.PatternBindings[List[Binding]]) ++ 
    rule("PatternSetUnaryOpTerm", "PatternCombTerm", _.PatternCombTerm[Any]) ++
    rule("PatternSetUnaryOpTerm", "Powerset PatternSetUnaryOpTerm", c => pTmUnaryOp(Kernel.set_power, c.PatternSetUnaryOpTerm)) ++
    rule("PatternSetUnaryOpTerm", "SetBigUnion PatternSetUnaryOpTerm", c => pTmUnaryOp(Kernel.set_bigunion, c.PatternSetUnaryOpTerm)) ++
    rule("PatternSetUnaryOpTerm", "SetBigIntersection PatternSetUnaryOpTerm", c => pTmUnaryOp(Kernel.set_bigintersection, c.PatternSetUnaryOpTerm)) ++
    rule("PatternSetIntersectionTerm", "PatternSetUnaryOpTerm", _.PatternSetUnaryOpTerm[Any]) ++
    rule("PatternSetIntersectionTerm", "PatternSetIntersectionTerm SetIntersection PatternSetUnaryOpTerm",
      c => pTmBinaryOp(Kernel.set_intersection, c.PatternSetIntersectionTerm, c.PatternSetUnaryOpTerm)) ++
    rule("PatternSetUnionTerm", "PatternSetIntersectionTerm", _.PatternSetIntersectionTerm[Any]) ++
    rule("PatternSetUnionTerm", "PatternSetUnionTerm SetUnion PatternSetIntersectionTerm",
      c => pTmBinaryOp(Kernel.set_union, c.PatternSetUnionTerm, c.PatternSetIntersectionTerm)) ++
    rule("PatternSetDiffTerm", "PatternSetUnionTerm", _.PatternSetUnionTerm[Any]) ++
    rule("PatternSetDiffTerm", "PatternSetDiffTerm SetDiff PatternSetUnionTerm", 
      c => pTmBinaryOp(Kernel.set_difference, c.PatternSetDiffTerm, c.PatternSetUnionTerm)) ++
    rule("PatternSetTerm", "PatternSetDiffTerm", _.PatternSetDiffTerm[Any]) ++
    rule("PatternSetBinaryRelationTerm", "PatternSetTerm", _.PatternSetTerm[Any]) ++
    rule("PatternSetBinaryRelationTerm", "PatternSetTerm_1 Elem PatternSetTerm_2", 
      c => pTmBinaryOp(Kernel.set_elementOf, c.PatternSetTerm_1, c.PatternSetTerm_2)) ++
    rule("PatternSetBinaryRelationTerm", "PatternSetTerm_1 NotElem PatternSetTerm_2", 
      c => pTmUnaryOp(Kernel.logical_not, pTmBinaryOp(Kernel.set_elementOf, c.PatternSetTerm_1, c.PatternSetTerm_2))) ++    
    rule("PatternSetBinaryRelationTerm", "PatternSetTerm_1 Subset PatternSetTerm_2", 
      c => pTmBinaryOp(Kernel.set_subsetOf, c.PatternSetTerm_1, c.PatternSetTerm_2)) ++
    rule("PatternSetBinaryRelationTerm", "PatternSetTerm_1 NotSubset PatternSetTerm_2", 
      c => pTmUnaryOp(Kernel.logical_not, pTmBinaryOp(Kernel.set_subsetOf, c.PatternSetTerm_1, c.PatternSetTerm_2))) ++    
    rule("PatternRelationTerm", "PatternSetBinaryRelationTerm", _.PatternSetBinaryRelationTerm[Any]) ++
    rule("PatternEqTerm", "PatternRelationTerm", _.PatternRelationTerm[Any]) ++
    rule("PatternEqTerm", "PatternRelationTerm_1 Eq PatternRelationTerm_2", c => pTmEquals(c.PatternRelationTerm_1, c.PatternRelationTerm_2)) ++
    rule("PatternEqTerm", "PatternRelationTerm_1 NotEq PatternRelationTerm_2", c => pTmUnaryOp(Kernel.logical_not, pTmEquals(c.PatternRelationTerm_1, c.PatternRelationTerm_2))) ++
    rule("PatternNotTerm", "Not PatternNotTerm", c => pTmUnaryOp(Kernel.logical_not, c.PatternNotTerm)) ++
    rule("PatternNotTerm", "PatternEqTerm", _.PatternEqTerm[Any]) ++
    rule("PatternAndTerm", "PatternAndTerm And PatternNotTerm", c => pTmBinaryOp(Kernel.logical_and, c.PatternAndTerm, c.PatternNotTerm)) ++
    rule("PatternAndTerm", "PatternNotTerm", _.PatternNotTerm[Any]) ++
    rule("PatternOrTerm", "PatternOrTerm Or PatternAndTerm", c => pTmBinaryOp(Kernel.logical_or, c.PatternOrTerm, c.PatternAndTerm)) ++
    rule("PatternOrTerm", "PatternAndTerm", _.PatternAndTerm[Any]) ++
    rule("PatternImpliesTerm", "PatternOrTerm RightArrow PatternImpliesTerm", c => pTmBinaryOp(Kernel.implies, c.PatternOrTerm, c.PatternImpliesTerm)) ++
    rule("PatternImpliesTerm", "PatternOrTerm", _.PatternOrTerm[Any]) ++
    rule("PatternPropTerm", "PatternImpliesTerm", _.PatternImpliesTerm[Any]) ++
    rule("PatternTypedTerm", "PatternPropTerm", _.PatternPropTerm[Any]) ++
    rule("PatternTypedTerm", "PatternTypedTerm Colon PatternType", c => PTmTyping(c.PatternTypedTerm, c.PatternType)) ++    
    rule("PatternAbsTerm", "PatternTypedTerm", _.PatternTypedTerm[Any]) ++
    rule("PatternAbsTerm", "PatternQuantifierTerm", _.PatternQuantifierTerm[Any]) ++
    rule("PatternQuantifierTerm", "Forall PatternBindings PatternQuantifierTerm", c => pTmForall(c.PatternBindings[List[Binding]], c.PatternQuantifierTerm[Preterm])) ++
    rule("PatternQuantifierTerm", "Exists PatternBindings PatternQuantifierTerm", c => pTmExists(c.PatternBindings[List[Binding]], c.PatternQuantifierTerm[Preterm])) ++
    rule("PatternQuantifierTerm", "NotExists PatternBindings PatternQuantifierTerm", c => pTmUnaryOp(Kernel.logical_not, pTmExists(c.PatternBindings[List[Binding]], c.PatternQuantifierTerm[Preterm]))) ++
    rule("PatternQuantifierTerm", "Forall PatternBindings Dot PatternAbsTerm", c => pTmForall(c.PatternBindings[List[Binding]], c.PatternAbsTerm[Preterm])) ++
    rule("PatternQuantifierTerm", "Exists PatternBindings Dot PatternAbsTerm", c => pTmExists(c.PatternBindings[List[Binding]], c.PatternAbsTerm[Preterm])) ++
    rule("PatternQuantifierTerm", "NotExists PatternBindings Dot PatternAbsTerm", c => pTmUnaryOp(Kernel.logical_not, pTmExists(c.PatternBindings[List[Binding]], c.PatternAbsTerm[Preterm]))) ++
    rule("PatternAbsTerm", "PatternBindings MapsTo PatternAbsTerm", c => pTmAbs(c.PatternBindings[List[Binding]], c.PatternAbsTerm[Preterm])) ++
    rule("PatternTerm", "PatternAbsTerm", _.PatternAbsTerm[Any]) ++
    rule("PatternTermList", "PatternTerm", c => List(c.PatternTerm[Any])) ++
    rule("PatternTermList", "PatternTermList Comma PatternTerm", c => c.PatternTerm[Preterm] :: c.PatternTermList[List[Preterm]]) 


  def grammar = 
    literals ++
    g_Value_type ++
    g_Pattern_type ++
    g_Value_term ++
    g_Pattern_term

  def parsePreterm(input : String) : Option[Preterm] = {
    val d = Document.fromString(input, Some(2))
    proofpeer.proofscript.frontend.Parser.earleyParser.parse(d, "ValueTerm") match {
      case Left(parsetree) if !parsetree.hasAmbiguities => 
        val preterm = parsetree.getValue[Preterm]
        if (Preterm.hasQuotes(preterm)) None else Some(preterm)
      case _ => None
    }
  } 

  def parsePretype(input : String) : Option[Pretype] = {
    val d = Document.fromString(input, Some(2))
    proofpeer.proofscript.frontend.Parser.earleyParser.parse(d, "ValueType") match {
      case Left(parsetree) if !parsetree.hasAmbiguities => 
        val pretype = parsetree.getValue[Pretype]
        if (Pretype.hasQuotes(pretype)) None else Some(pretype)
      case _ => None
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

  type Resolution = Preterm.NameResolution

  def printBinary(nameRes : Resolution, vars : Set[IndexedName], op : String, left : Term, right : Term) : String = {
    protect(printTerm(nameRes, vars, left)) + " " + op + " " + protect(printTerm(nameRes, vars, right))
  }

  def printUnary(nameRes : Resolution, vars : Set[IndexedName], op : String, tm : Term) : String = {
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

  def printTerm(nameRes : Resolution, tm : Term) : String = {
    printTerm(nameRes, Set(), KernelUtils.avoidVarConstClashes(tm))
  }

  private def printNameInContext(nameRes : Resolution, vars : Set[IndexedName], name : Name) : String = {
    if (name.namespace.isDefined && !vars.contains(name.name)) {
      nameRes(Name(None, name.name)) match {
        case Left(n) if n == name => printName(name.name)
        case _ => printName(name)
      }
    } else printName(name)
  }

  private def printTerm(nameRes : Resolution, vars : Set[IndexedName], tm : Term) : String = {
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

  def checkprintTerm(aliases : Aliases, nameresolution : NamespaceResolution[IndexedName],
    context : Context, tm : Term) : String = 
  {
    val res = Preterm.obtainNameResolution(aliases, nameresolution, context)
    val u = printTerm(res, tm)
    val tm2 = parseTerm(aliases, nameresolution, context, u)
    if (!KernelUtils.alpha_equivalent(tm, tm2))
      Utils.failwith("term '"+u+"' is not a correct representation of: '"+tm+"'")
    else
      u
  }

  def checkprintTerm(aliases : Aliases, nameresolution : NamespaceResolution[IndexedName],
    context : Context, tm : CTerm) : String = 
  {
    val term = context.lift(tm)
    checkprintTerm(aliases, nameresolution, context, term.term)
  }

  def parseTerm(aliases : Aliases, nameresolution : NamespaceResolution[IndexedName],
    context : Context, s : String) : Term =
  {
    parsePreterm(s) match {
      case None => Utils.failwith("cannot parse as preterm: '"+s+"'")
      case Some(ptm) => 
        val typingContext = Preterm.obtainTypingContext(aliases, nameresolution, context)
        Preterm.inferTerm(typingContext, ptm) match {
          case Left(tm) => tm
          case Right(errors) =>
            Utils.failwith("cannot convert preterm to term: "+ptm)
        }
    }    
  }

  def parseCTerm(aliases : Aliases, nameresolution : NamespaceResolution[IndexedName],
    context : Context, s : String) : CTerm =
  {
    context.certify(parseTerm(aliases, nameresolution, context, s))
  }

     
}