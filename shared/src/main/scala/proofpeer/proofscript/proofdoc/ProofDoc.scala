package proofpeer.proofscript.proofdoc

import proofpeer.proofscript.frontend.{TracksSourcePosition, ParseTree}

sealed trait ProofDoc extends ParseTree 

object ProofDoc {

  sealed trait Prop extends TracksSourcePosition
  case class StringProp(s : String) extends Prop
  case class ParseTreeProp(p : ParseTree) extends Prop

  case class V(ty : T, keyword : Option[StringProp], props : Vector[Prop], values : Vector[V]) extends TracksSourcePosition {
    def isWord = ty.isWord
    def isBlock = ty.isBlock
    def addValue(v : V) : V = V(ty, keyword, props, values :+ v)
  }

  val noprops : Vector[Prop] = Vector()
  val novalues : Vector[V] = Vector()

  sealed trait T {
    def isWord : Boolean = true
    def isBlock : Boolean = true
  }
  
  sealed trait Word extends T {
    override def isBlock = false
  }
  
  sealed trait Block extends T {
    override def isWord = false
  }

  /** A Paragraph contains only values and no props. Each of the values must be a word. */
  case object Paragraph extends Block
  
  /** A Generator contains only of a single property which represents the code that is generated. */
  case object Generator extends T 

  /** A Text has only a single string property. */
  case object Text extends Word

  /** A FaultyText has only a single string property. */
  case object FaultyText extends Word

  /** Blocks represents a sequence of Block values. It has no props. */
  case object Blocks extends Block

  case object DummyBlock extends Block

}

class ProofDocSyntax(annotate : (Any, Option[proofpeer.indent.Span]) => Any) {

  import proofpeer.indent._
  import proofpeer.indent.regex._
  import proofpeer.indent.Constraint._
  import ProofDoc._

  def range(cs : Char*) : Range = {
    var r = Range()
    for (c <- cs) r += Range(c)
    r
  }

  def Subalign(a : String, b : String) = or(Indent(a, b), Align(a, b))
  def SameOrNextLine(a : String, b : String) = Leq(FirstRow(b), LastRow(a), 1)
  def DifferentLines(a : String, b : String) = Leq(LastRow(a), FirstRow(b), -1)
  def OneLineApart(a : String, b : String) = Leq(LastRow(a), FirstRow(b), -2)

  /** Generally useful regular expressions */
  val letter = alt(chars('a', 'z'), chars('A', 'Z'))
  val digit = chars('0', '9')
  val anychar = CHAR(Range.universal)

  var scope : String = null
  var priority : Int = 1
  var grammar : Grammar = Grammar()

  def setScope(s : String) {
    scope = s
    priority = 1
  }
  def lex(terminal : String, r : RegularExpr) {
    grammar = grammar ++ rule(terminal, r, Some(priority), scope)
    priority += 1
  }
  def grule(nonterminal : String, rhs : String, constraint : Constraint, action : ParseContext => Any) {
    def annotatedAction(c : ParseContext) : Any = {
      val s : Option[Span] = if (c.span == null) None else Some(c.span)    
      annotate(action(c), s)
    }
    grammar = grammar ++ rule(nonterminal, rhs, constraint, annotatedAction _)
  }
  def grule(nonterminal : String, rhs : String, action : ParseContext => Any) {
    grule(nonterminal, rhs, unconstrained, action)
  }
  def annotateProp(p : Prop, s : Span) : Prop = {
    annotate(p, Some(s)).asInstanceOf[Prop]
  }
  
  /** Scope Paragraph */

  setScope("Scope Paragraph")

  val specialrange = range('*', '~', '$', '`', '@', '\\', '[', ']', '<', '>')
  val simplechar = CHAR(-specialrange)
  val escapechar = seq(char('\\'), CHAR(specialrange))
  val simpleword = REPEAT1(alt(simplechar, escapechar)) 

  lex("SIMPLEWORD", simpleword)
  lex("ASTERISK", char('*'))
  lex("OPENLINK", char('['))
  lex("CLOSELINK", char(']'))
  lex("OPENANGLE", char('<'))
  lex("CLOSEANGLE", char('>'))
  lex("USER", seq(char('@'), letter, REPEAT(alt(letter, digit))))
  lex("KEYWORD", seq(REPEAT1(char('~')), REPEAT(letter), OPT(char('$'))))  
  lex("REFERENCE", seq(char('<'), REPEAT(letter), char(':'), REPEAT(CHAR(-range('>'))), char('>')))
    
  /** Grammar rules */
  grule("Blocks", "", c => V(Blocks, None, noprops, novalues))
  grule("Blocks", "KBlocks", _.KBlocks[V])
  grule("Blocks", "PBlocks", _.PBlocks[V])

  // PBlocks always ends with a Paragraph, KBlocks always ends with a KBlock
  grule("PBlocks", "Paragraph",
    c => V(Blocks, None, noprops, Vector(c.Paragraph)))
  grule("PBlocks", "KBlocks Paragraph", 
    and(Align("KBlocks", "Paragraph"), DifferentLines("KBlocks", "Paragraph")), 
    c => c.KBlocks[V].addValue(c.Paragraph))
  grule("PBlocks", "PBlocks Paragraph", 
    and(Align("PBlocks", "Paragraph"), OneLineApart("PBlocks", "Paragraph")), 
    c => c.PBlocks[V].addValue(c.Paragraph))
  grule("KBlocks", "Blocks KBlock",
    and(Align("Blocks", "KBlock"), DifferentLines("Blocks", "KBlock")), 
    c => c.Blocks[V].addValue(c.KBlock))

  grule("Paragraph", "Word", 
    c => V(Paragraph, None, noprops, Vector(c.Word)))
  grule("Paragraph", "Paragraph Word", 
    and(Subalign("Paragraph", "Word"), SameOrNextLine("Paragraph", "Word")),
    c => c.Paragraph[V].addValue(c.Word))

  // what are Words and KBlocks?

  grule("Word", "SIMPLEWORD", 
    c => V(Text, None, Vector(annotateProp(StringProp(c.text), c.span)), novalues))

  grule("KBlock", "KEYWORD",
    c => V(DummyBlock, None, noprops, novalues))
}


/*
object ProofDoc {

  sealed trait Word extends ProofDoc {
    protected def calcVars = (Set(), Set())
  }

  sealed trait Words extends Word {
    def words : Vector[Word] = Vector()
    override protected def calcVars = {
      var frees : Set[String] = Set()
      for (w <- words) {
        frees = frees ++ w.freeVars
      }
      (frees, Set())
    }    
  }

  case class PString(s : String) extends TracksSourcePosition 

  case class GString(ss : Vector[Either[PString, Generator]]) extends TracksSourcePosition

  sealed trait Block extends ProofDoc {
    def keyword : Option[PString]
    def params : Vector[Word] = Vector()
    def subBlocks : Vector[Block] = Vector()
    protected def calcVars = {
      var frees : Set[String] = Set()
      var intros : Set[String] = Set()
      for (p <- params) {
        frees = frees ++ p.freeVars
      }
      for (b <- subBlocks) {
        frees = frees ++ (b.freeVars -- intros)
        intros = intros ++ b.introVars
      }
      (frees, intros)
    }
  }

  // $`p` 
  case class Generator(p : ParseTree) extends Word {
    override protected def calcVars = (p.freeVars, p.introVars)
  }

  // `p`
  case class InlineProofScript(p : ParseTree) extends Word 

  // ``text``
  case class InlineVerbatim(text : PString) extends Word 

  // ```language code```
  case class InlineCode(language : PString, code : PString) extends Word 

  // $$math$$
  case class InlineMath(math : PString) extends Word

  case class Text(text : String) extends Word

  case class Link (override val words : Vector[Word], reference : Reference) extends Words

  sealed trait Reference extends Word

  case class ExternalRef(ref : String) extends Reference

  case class LabelRef(path : Option[PString], label : PString) extends Reference

  case class EntityRef(path : Option[PString], entity : PString) extends Reference

  case class Ref(path : Option[PString]) extends Reference 

  case class UserRef(username : String) extends Reference

  case class Emph(override val words : Vector[Word]) extends Words

  case class Bold(override val words : Vector[Word]) extends Words

  // ~$ p
  case class BlockGenerator(keyword : Option[PString], p : ParseTree) extends Block {
    override protected def calcVars = (p.freeVars, p.introVars)
  }

  case class Paragraph(keyword : Option[PString], words : Vector[Word]) extends Block {
    override def params = words
  }

  // level starts with 1
  case class Header(level : Int, title : Vector[Word]) extends Block {
    def keyword = None
    override def params = title
  }

  case class ProofScript(keyword : Option[PString], code : GString) extends Block 

  case class Code(keyword : Option[PString], language : Option[PString], code : GString) extends Block 

  case class Verbatim(keyword : Option[PString], text : GString) extends Block 

  case class Math(keyword : Option[PString], math : GString) extends Block 

  case class Label(keyword : Option[PString], id : Word) extends Block

  case class Tag(keyword : Option[PString], tags : Vector[Word]) extends Block

  case class Line(keyword : Option[PString]) extends Block

  case class Quote(keyword : Option[PString], origin : Vector[Word], quote : Vector[Block]) extends Block {
    override def params = origin
    override def subBlocks = quote
  }

  case class Item(keyword : Option[PString], override val params : Vector[Word], blocks : Vector[Block]) extends Block {
    override def subBlocks = blocks
  }

  case class UList(keyword : Option[PString], items : Vector[Item]) extends Block {
    override def subBlocks = items
  }

  case class OList(keyword : Option[PString], items : Vector[Item]) extends Block {
    override def subBlocks = items
  }

  // the parameters to a table specify the width of columns and wether the columns are separated by vertical lines,
  // for example |_| _ _| 45.9 specifies that there are 4 columns, 3 vertical lines, and the last column occupies
  // 45.9% of the page width
  case class Table(keyword : Option[PString], override val params : Vector[Word], rows : Vector[Block]) extends Block {
    override def subBlocks = rows
  }

  case class TableRow(keyword : Option[PString], items : Vector[Item]) extends Block {
    override def subBlocks = items
  }

  case class Bibliography(keyword : Option[PString], items : Vector[Item]) extends Block {
    override def subBlocks = items
  }

  case class Image(keyword : Option[PString], override val params : Vector[Word], props : Vector[Block]) extends Block {
    override def subBlocks = props
  }

} */
