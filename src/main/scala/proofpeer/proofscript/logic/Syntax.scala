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

*/

object Syntax {
  
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
      Name(Some(new Namespace(namespace)), indexedname)
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
    ltokenrule("QuoteOpen", Range.singleton(0x00AB)) ++
    ltokenrule("QuoteClose", Range.singleton(0x00BB)) ++
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
    
  val g_term = 
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
    rule("AtomicTerm", "QuoteOpen QuotedTerm QuoteClose", c => pTmQuote(c.QuotedTerm.result)) ++
    rule("CombTerm", "AtomicTerm", _.AtomicTerm.result) ++
    rule("CombTerm", "CombTerm AtomicTerm", c => PTmComb(c.CombTerm.resultAs[Preterm], c.AtomicTerm.resultAs[Preterm], None, Pretype.PTyAny)) ++
    rule("PureBinding", "IndexedName", c => Binding(parseIndexedName(c.IndexedName.text), None)) ++
    rule("AnnotatedBinding", "IndexedName Colon Type", c => Binding(parseIndexedName(c.IndexedName.text), Some(TypeDomain(c.Type.resultAs[Pretype])))) ++    
    rule("AnnotatedBinding", "IndexedName Elem Term", c => Binding(parseIndexedName(c.IndexedName.text), Some(SetDomain(c.Term.resultAs[Preterm])))) ++ 
    rule("Binding", "PureBinding", _.PureBinding.result) ++
    rule("Binding", "AnnotatedBinding", _.AnnotatedBinding.result) ++    
    rule("PureBindings", "PureBinding", c => List(c.PureBinding.resultAs[Binding])) ++
    rule("PureBindings", "PureBindings PureBinding", c => c.PureBinding.resultAs[Binding] :: c.PureBindings.resultAs[List[Binding]]) ++ 
    rule("Bindings", "PureBindings", _.PureBindings.result) ++
    rule("Bindings", "AnnotatedBinding", c => List(c.AnnotatedBinding.resultAs[Binding])) ++
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
    rule("AbsTerm", "QuantifierTerm", _.QuantifierTerm.result) ++
    rule("QuantifierTerm", "Forall Bindings QuantifierTerm", c => pTmForall(c.Bindings.resultAs[List[Binding]], c.QuantifierTerm.resultAs[Preterm])) ++
    rule("QuantifierTerm", "Exists Bindings QuantifierTerm", c => pTmExists(c.Bindings.resultAs[List[Binding]], c.QuantifierTerm.resultAs[Preterm])) ++
    rule("QuantifierTerm", "NotExists Bindings QuantifierTerm", c => pTmUnaryOp(Kernel.logical_not, pTmExists(c.Bindings.resultAs[List[Binding]], c.QuantifierTerm.resultAs[Preterm]))) ++
    rule("QuantifierTerm", "Forall Bindings Dot AbsTerm", c => pTmForall(c.Bindings.resultAs[List[Binding]], c.AbsTerm.resultAs[Preterm])) ++
    rule("QuantifierTerm", "Exists Bindings Dot AbsTerm", c => pTmExists(c.Bindings.resultAs[List[Binding]], c.AbsTerm.resultAs[Preterm])) ++
    rule("QuantifierTerm", "NotExists Bindings Dot AbsTerm", c => pTmUnaryOp(Kernel.logical_not, pTmExists(c.Bindings.resultAs[List[Binding]], c.AbsTerm.resultAs[Preterm]))) ++
    rule("AbsTerm", "Bindings MapsTo AbsTerm", c => pTmAbs(c.Bindings.resultAs[List[Binding]], c.AbsTerm.resultAs[Preterm])) ++
    rule("TermList", "Term", c => List(c.Term.resultAs[Preterm])) ++
    rule("TermList", "TermList Comma Term", c => c.Term.resultAs[Preterm] :: c.TermList.resultAs[List[Preterm]]) ++
    rule("Term", "AbsTerm", _.AbsTerm.result)

  def grammar = 
    literals ++
    g_type ++
    g_term

    
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