package proofpeer.proofscript.proofdoc

import proofpeer.proofscript.frontend.{TracksSourcePosition, ParseTree}
import proofpeer.general.StringUtils

sealed trait ProofDoc extends ParseTree 

final object ProofDoc {

  sealed trait Prop extends TracksSourcePosition
  case class StringProp(s : String) extends Prop

  val DEFAULT_PROP = "default"
  val KEYWORD_PROP = "keyword"  

  case class V(ty : T, props : Map[String, Prop], errors : Vector[Prop], values : Vector[V]) extends TracksSourcePosition {
    def add(v : V) : V = if (v != null) V(ty, props, errors, values :+ v) else this
    def addInFront(v : V) = if (v != null) V(ty, props, errors, v +: values) else this
    def add(vs : Vector[V]) = V(ty, props, errors, values ++ vs)
    def add(name : String, p : Prop) = V(ty, props + (name -> p), errors, values)
    def addError(p : Prop) = V(ty, props, errors :+ p, values)
    def stringOf(propname : String) : String = props(propname).asInstanceOf[StringProp].s
  }

  object V {
    private val noprops : Map[String, Prop] = Map()
    private val noerrors : Vector[Prop] = Vector()
    private val novalues : Vector[V] = Vector()
    def apply(ty : T) : V = V(ty, noprops, noerrors, novalues)
    def apply(ty : T, prop : Prop) : V = V(ty).add(DEFAULT_PROP, prop)
    def apply(ty : T, v : V) : V = V(ty).add(v)
  }


  sealed trait T 
  
  case object Text extends T

  case object Punctuation extends T

  case object Reference extends T

  case object User extends T

  case object Blocks extends T

  case object Words extends T

  case object Link extends T

  case object Emph extends T

  case object DoubleEmph extends T

  case object Header extends T

  case object Emoticon extends T

  case object Hashtag extends T

  case object Math extends T

  case object Verbatim extends T

  case object Quote extends T

  case object ProofScript extends T

  case object Run extends T

  case object Anything extends T

  case object ItemList extends T

  case object ListItem extends T

  case object Table extends T

  case object TableParam extends T

  case object Row extends T

  case object Line extends T

  case object Cell extends T

  case object Label extends T

  case object LabelOpen extends T

  case object LabelClose extends T

  case object References extends T

  case object RefItem extends T

  case object RefItemFields extends T

  case object RefItemField extends T

  case object Fallback extends T

  /** This is used until we know what to do with accidental ambiguitites */
  case object Ambiguity extends T 

}

class ProofDocSyntax(annotate : (Any, Option[proofpeer.indent.Span]) => Any) {

  import proofpeer.indent._
  import proofpeer.indent.regex._
  import proofpeer.indent.Constraint._
  import ProofDoc._
  import ProofDoc.V

  def computeAmbiguousValue(nonterminal : String, span : Span, parsetrees : Vector[proofpeer.indent.ParseTree]) : Any = {
    val values = parsetrees.map(_.getValue[V])
    V(Ambiguity, StringProp(nonterminal)).add(values)
  }

  def range(cs : Char*) : Range = {
    var r = Range()
    for (c <- cs) r += Range(c)
    r
  }

  // case insensitive string as regular expression
  def cis(s : String) : RegularExpr = {
    import proofpeer.general.StringUtils._
    var v : Vector[RegularExpr] = Vector()
    for (c <- s) {
      v = v :+ CHAR(Range(toLowerCase(c)) + Range(toUpperCase(c)))
    }
    seq(v : _*)
  }

  /** Generally useful regular expressions */
  val letter = alt(chars('a', 'z'), chars('A', 'Z'))
  val digit = chars('0', '9')
  val anychar = CHAR(Range.universal)

  var scope : String = null
  var priority : Int = 1
  var grammar : Grammar = Grammar(computeAmbiguousValue _)

  def setScope(s : String) {
    scope = s
    priority = 1
  }
  def lex(terminal : String, r : RegularExpr) {
    grammar = grammar ++ rule(terminal, r, Some(priority), scope)
    priority += 1
  }
  def lex(terminal : String, lexer : Lexer) {
    grammar = grammar ++ lexrule(terminal, lexer, Some(priority), scope)
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
  def annotateProp[T <: Prop](p : T, s : Span) : T = {
    annotate(p, Some(s)).asInstanceOf[T]
  }
  def sprop(c : ParseContext, t : String) : StringProp = {
    annotateProp(StringProp(c.text(t)), c.span(t))
  }
  def sprop(c : ParseContext) : StringProp = {
    annotateProp(StringProp(c.text), c.span)    
  }
  def eprop(c : ParseContext, descr : String) : StringProp = {
    annotateProp(StringProp(descr), c.span)    
  }
  def eprop(c : ParseContext, t : String, descr : String) : StringProp = {
    annotateProp(StringProp(descr), c.span(t))    
  }
  
  val punctuation = range('(', ')', '.', '!', '?', ':', ';', ',', '"', '\'', '-')
  val specialrange = range('*', '~', '$', '`', '@', '\\', '<', '>', '{', '}', '[', ']', '#')
  val handledspecialrange = range('*', '$', '`', '@', '\\', '<', '{', '[', ']', '#')
  val nonsimple = specialrange + punctuation
  val simplechar = CHAR(-nonsimple)
  val escapechar = seq(char('\\'), CHAR(nonsimple))
  val unicodechar = seq(char('\\'), REPEAT1(alt(digit, chars('a', 'f'), chars('A', 'F'))), char('/'))
  val simpleword = REPEAT1(alt(simplechar, escapechar, unicodechar)) 

  def unescape(s : String) : String = {
    val builder : StringBuilder = new StringBuilder()
    var escape : Boolean = false
    var code : Int = 0
    val MAX_UNICODE : Int = 0x10ffff
    for (c <- s) {
      if (!escape) {
        if (c == '\\') escape = true
        else builder.append(c)
      } else {
        if (nonsimple.contains(c)) {
          builder.append(c)
          escape = false
        } else {
          if (c == '/') {
            StringUtils.fromCodePoint(code) match {
              case Some(s) => builder.append(s)
              case None => // ignore code
            }
            escape = false
            code = 0
          } else {
            val d : Int = 
              if (c >= '0' && c <= '9') c - '0'
              else if (c >= 'A' && c <= 'F') (c - 'A') + 10
              else if (c >= 'a' && c <= 'f') (c - 'a') + 10
              else throw new RuntimeException("internal error: c = " + c)
            if (code <= MAX_UNICODE) code = code * 16 + d
          }
        }
      }
    }
    builder.toString
  }

  // It's a shame that this lexer is needed, it exists so that double backquotes are recognised
  // only when the backquotes are not separated by spaces. 
  // The Lexer library should be extended at some point to cover these cases.
  private object InlineProofScriptLexer extends Lexer {

    val zero : Boolean = false

    val first : Range = Range('`')

    def lex(d : Document, startPosition : Int, param : ParseParam.V) : (Int, ParseParam.V) = {
      val size = d.size
      var pos = startPosition
      val List(minColumn, minRow, maxStartColumn, maxStartRow) = 
        ParseParam.v2Ints(List(Int.MinValue, Int.MinValue, Int.MaxValue, Int.MaxValue), param)
      var lastRow = -1

      def nil(len : Int) : (Int, ParseParam.V) = (len, ParseParam.NIL)

      def isDoubleBackquote : Boolean = {
        if (pos + 1 < size) {
          val (row1, col1, code1) = d.character(pos)
          lastRow = row1
          if (code1 == '`' && col1 >= minColumn && row1 >= minRow &&
            (pos > startPosition || (col1 <= maxStartColumn && row1 <= maxStartRow))) 
          {
            val (row2, col2, code2) = d.character(pos + 1)
            code2 == '`' && row1 == row2 && col2 == col1 + 1 && col2 >= minColumn
          } else false
        } else false
      }

      if (isDoubleBackquote) {
        pos += 2
        while (pos < size) {
          val (row, col, code) = d.character(pos)
          if (col < minColumn || row != lastRow) return nil(pos - startPosition)
          if (code != '`') pos += 1
          else {
            if (isDoubleBackquote) pos += 2
            else pos += 1
            return nil(pos - startPosition)
          }
          lastRow = row
        }
      }

      nil(pos - startPosition)
    }

  }

  private object ProtrudeLexer extends Lexer {

    val zero : Boolean = false

    val first : Range = Range.universal

    def lex(d : Document, startPosition : Int, param : ParseParam.V) : (Int, ParseParam.V) = {
      val size = d.size
      if (startPosition >= size) return (-1, ParseParam.UNDEFINED)
      val List(minColumn, maxStartColumn) = ParseParam.v2Ints(List(Int.MinValue, Int.MaxValue), param)
      val (_, startColumn, _) = d.character(startPosition)
      if (startColumn < minColumn || startColumn > maxStartColumn) return (-1, ParseParam.UNDEFINED)
      var pos = startPosition + 1
      while (pos < size) {
        val (_, column, _) = d.character(pos)
        if (column > startColumn) pos = pos + 1
        else return (pos - startPosition, ParseParam.NIL)
      }
      (size - startPosition, ParseParam.NIL)
    }
  
  }

  /** Fallbacks */

  setScope(FALLBACK_SCOPE)

  lex("FALLBACK", Lexer.untilEnd(anything))
  lex("FALLBACKLINE", Lexer.untilNewline(anything))
  lex("FALLBACKWORD", Lexer.untilWhitespace(REPEAT1(CHAR(-(punctuation + handledspecialrange)))))
  lex("FALLBACKPROTRUDE", Lexer.demandLeftBorder(ProtrudeLexer, 1))

  def fallback(c : ParseContext, nonterminal : String) : V = {
    V(Fallback, eprop(c, nonterminal))
  }

  /** Scope Paragraph */

  setScope("Scope Paragraph")

  def keyword(r : RegularExpr) : Lexer = {
    Lexer.demandRightBorder(Lexer.demandLeftBorder(Lexer.untilWhitespace(r), 1))
  }

  def klex(terminal : String, r : RegularExpr) {
    lex(terminal, keyword(r))
  }

  lex("BACKSLASH", char('\\'))
  lex("SIMPLEWORD", simpleword)
  lex("PUNCTUATION", alt(CHAR(punctuation)))
  lex("ASTERISK", char('*'))
  lex("DOUBLEASTERISK", string("**"))
  lex("OPENLINK", char('['))
  lex("CLOSELINK", char(']'))
  lex("USER", seq(char('@'), OPT(simpleword)))
  lex("HASHTAG", seq(char('#'), OPT(simpleword)))
  lex("LABEL", seq(string("::"), simpleword))
  lex("LABELOPEN", seq(string("(:"), simpleword))
  lex("LABELCLOSE", seq(simpleword, string(":)")))
  lex("HYPHEN", char('-'))
  lex("ENDASH", string("--"))
  lex("EMDASH", string("---"))
  lex("LEFTQUOTE", Lexer.demandLeftBorder(Lexer.untilWhitespace(string("'")), 0, nonsimple))
  lex("RIGHTQUOTE", Lexer.demandRightBorder(Lexer.untilWhitespace(string("'")), 0, nonsimple)) 
  lex("LEFTDOUBLEQUOTE", Lexer.demandLeftBorder(Lexer.untilWhitespace(char('"')), 0, nonsimple))
  lex("RIGHTDOUBLEQUOTE", Lexer.demandRightBorder(Lexer.untilWhitespace(char('"')), 0, nonsimple)) 
  klex("REFITEMLABEL", seq(string("::"), simpleword))
  klex("LISTBULLET", alt(char('-'), seq(alt(REPEAT1(digit), letter), char('.'))))
  klex("ITEMHYPHEN", char('-'))
  klex("KEYWORD", seq(REPEAT1(char('~')), REPEAT(letter), OPT(char('$'))))  
  klex("MATH", alt(cis("~math"), string("~$")))
  klex("VERBATIM", alt(cis("~verbatim"), string("~`")))
  klex("RUN", alt(cis("~run"), string("~{")))
  klex("PROOFSCRIPT", alt(cis("~proofscript"), string("~``")))
  klex("QUOTE", cis("~quote"))
  klex("TABLE", cis("~table"))
  klex("REFERENCES", cis("~references"))
  lex("TABLEPARAM", REPEAT1(alt(char('|'), cis("c"), cis("l"), cis("r"))))
  klex("ROW", cis("~row"))
  klex("LINE", cis("~line"))
  klex("HEADER", REPEAT1(char('~')))
  klex("DISPLAY", cis("~display"))
  klex("IN", cis("~in"))
  klex("TITLE", cis("~title"))
  klex("AUTHOR", cis("~author"))
  klex("YEAR", cis("~year"))
  klex("MONTH", cis("~month"))
  klex("DAY", cis("~day"))
  lex("EMOTICON", alt(string(":-)"), string(";-)"), string(":-D"), string(":-P"),
    string(":-/"), string(":-|"), string(":-("), string(":-O")))
  lex("INLINEMATH", Lexer.untilNewline(seq(char('$'), REPEAT(CHAR(-range('$'))), OPT(char('$')))))
  lex("INLINEVERBATIM", Lexer.untilNewline(seq(char('`'), REPEAT(CHAR(-range('`'))), OPT(char('`')))))
  lex("INLINERUN", Lexer.untilNewline(seq(char('{'), REPEAT(CHAR(-range('}'))), OPT(char('}')))))
  lex("INLINEPROOFSCRIPT", InlineProofScriptLexer)
  lex("REFERENCE", Lexer.untilNewline(seq(char('<'), REPEAT(CHAR(-range('>'))), OPT(char('>')))))
  lex("ANYTHING", Lexer.untilEnd(anything))

  def mkLexedEntity(c : ParseContext, ty : T, start : String, stop : String, prep : String => String = (x => x)) : V = {
    var text = c.text
    val span = c.span
    var v : V = V(ty)
    def str(s : String) : Prop = annotateProp(StringProp(s), span)
    if (!text.startsWith(start)) v = v.addError(str("doesn't start with " + start))
    else text = text.substring(start.size)
    if (!text.endsWith(stop)) v = v.addError(str("doesn't end with " + stop))
    else text = text.substring(0, text.size - stop.size)
    v = v.add(DEFAULT_PROP, str(prep(text)))
    v
  }

  def mkInlineMath(c : ParseContext) : V = mkLexedEntity(c, Math, "$", "$")

  def mkReference(c : ParseContext) : V = mkLexedEntity(c, Reference, "<", ">")

  def mkInlineVerbatim(c : ParseContext) : V = mkLexedEntity(c, Verbatim, "`", "`")

  def mkInlineRun(c : ParseContext) : V = mkLexedEntity(c, Run, "{", "}")

  def mkUser(c : ParseContext) : V = {
    val v = mkLexedEntity(c, User, "@", "", unescape _)
    if (v.stringOf(DEFAULT_PROP) == "") v.addError(eprop(c, "empty peer name")) else v
  }

  def mkHashtag(c : ParseContext) : V = {
    val v = mkLexedEntity(c, Hashtag, "#", "", unescape _)
    if (v.stringOf(DEFAULT_PROP) == "") v.addError(eprop(c, "empty hashtag")) else v
  }

  def mkInlineProofScript(c : ParseContext) : V = {
    def prep(s : String) : String = if (s.endsWith("`")) s.substring(0, s.size - 1) else s 
    mkLexedEntity(c, ProofScript, "``", "``", prep _)
  }

  /** Grammar rules */

  grule("ProofDoc", "Blocks(nil, nil)", _.Blocks[V])

  // Blocks: (minColumn, minRow) => [(maxStartColumn, WordsMinRow, ItemListMinRow)]
  grule("Blocks", "", c => V(Blocks))
  grule("Blocks", "Blocks_1~ Words(~.1, Blocks_1.val.2 | ~.2, Blocks_1.val.1 | nil, nil, 0) { (Words.val, Words.lastRow + 2, Words.lastRow + 2) }", 
    c => c.Blocks_1[V].add(c.Words[V]))
  grule("Blocks", "Blocks_1~ ItemList(~.1, Blocks_1.val.3 | ~.2, Blocks_1.val.1 | nil) { (ItemList.val, ItemList.lastRow + 1, ItemList.lastRow + 2) }", 
    c => c.Blocks_1[V].add(c.ItemList[V]))

  // Words: (minColumn, minRow, maxStartColumn, maxStartRow, type) => maxStartColumn  
  grule("Words", "CompactWord~ { CompactWord.val }", c => V(Words, c.CompactWord[V]))
  grule("Words", "BlockWord~ { BlockWord.leftMost }", c => V(Words, c.BlockWord[V]))
  grule("Words", "Words_1~ CompactWord(~.1, ~.2, Words_1.val, Words_1.lastRow + 1, ~.5) { CompactWord.val }",
    c => c.Words_1[V].add(c.CompactWord[V]))
  grule("Words", "Words_1~ BlockWord(~.1, ~.2, Words_1.val, Words_1.lastRow + 1, ~.5) { BlockWord.leftMost }",
    c => c.Words_1[V].add(c.BlockWord[V]))

  grule("LineOfWords", "Words~", Constraint.Line("Words"), _.Words[V])
  grule("LineOfWords", "", c => V(Words))
  grule("LineOfWords", "FALLBACKLINE~", c => fallback(c, "LineOfWords"))

  // These are the bits which can be set in the "type" parameter for Words / CompactWord
  private val B_LINK = 0 
  private val B_EMPH = 1
  private val B_DOUBLEEMPH = 2

  def mkPunctuation(c : ParseContext, character : String) : V = 
    V(Punctuation, annotateProp(StringProp(character), c.span))

  // CompactWord: (minColumn, minRow, maxStartColumn, maxStartRow, type) => -1 or nil,
  // a return value of -1 designates that this is the last word in Words
  grule("CompactWord", "SIMPLEWORD~", 
    c => V(Text, annotateProp(StringProp(unescape(c.text)), c.span)))
  grule("CompactWord", "BACKSLASH~", 
    c => V(Text, annotateProp(StringProp(""), c.span)))  
  grule("CompactWord", "PUNCTUATION~", c => V(Punctuation, sprop(c)))
  grule("CompactWord", "HYPHEN~", c => mkPunctuation(c, "\u2010"))
  grule("CompactWord", "ENDASH~", c => mkPunctuation(c, "\u2013"))
  grule("CompactWord", "EMDASH~", c => mkPunctuation(c, "\u2014"))
  grule("CompactWord", "LEFTQUOTE~", c => mkPunctuation(c, "\u2018"))
  grule("CompactWord", "RIGHTQUOTE~", c => mkPunctuation(c, "\u2019"))
  grule("CompactWord", "LEFTDOUBLEQUOTE~", c => mkPunctuation(c, "\u201C"))
  grule("CompactWord", "RIGHTDOUBLEQUOTE~", c => mkPunctuation(c, "\u201D")) 
  grule("CompactWord", "EMOTICON~", c => V(Emoticon, sprop(c)))
  grule("CompactWord", "USER~", c => mkUser(c))
  grule("CompactWord", "Reference~", _.Reference[V])
  grule("CompactWord", "INLINEMATH~", c => mkInlineMath(c))
  grule("CompactWord", "INLINEPROOFSCRIPT~", c => mkInlineProofScript(c))
  grule("CompactWord", "INLINEVERBATIM~", c => mkInlineVerbatim(c))
  grule("CompactWord", "INLINERUN~", c => mkInlineRun(c))
  grule("CompactWord", "HASHTAG~", c => mkHashtag(c))
  grule("CompactWord", "LABEL~", c => mkLexedEntity(c, Label, "::", "", unescape _))
  grule("CompactWord", "LABELOPEN~", c => mkLexedEntity(c, LabelOpen, "(:", "", unescape _))
  grule("CompactWord", "LABELCLOSE~", c => mkLexedEntity(c, LabelClose, "", ":)", unescape _))
  grule("CompactWord", "Link~ { Link.val }", Not(TestBit(ParameterSelect(5), B_LINK)), _.Link[V])
  grule("CompactWord", "OPENLINK~", TestBit(ParameterSelect(5), B_LINK),   
    c => V(Text).addError(eprop(c, "cannot have link within link")))
  grule("CompactWord", "CLOSELINK~", Not(TestBit(ParameterSelect(5), B_LINK)),   
    c => V(Text).addError(eprop(c, "no link to close"))) 
  grule("CompactWord", "Emph~ { Emph.val }", Not(TestBit(ParameterSelect(5), B_EMPH)), _.Emph[V])
  grule("CompactWord", "DoubleEmph~ { DoubleEmph.val }", Not(TestBit(ParameterSelect(5), B_DOUBLEEMPH)), _.DoubleEmph[V])
  grule("CompactWord", "FALLBACKWORD~", c => fallback(c, "CompactWord"))

  // BlockWord: (minColumn, minRow, maxStartColumn, maxStartRow, type) => ?
  grule("BlockWord", "HEADER~ Blocks(HEADER.leftMost + 1, nil)",
    c => V(Header).add(KEYWORD_PROP, sprop(c, "HEADER")).add(c.Blocks[V]))
  grule("BlockWord", "QUOTE~ LineOfWords(QUOTE.leftMost + 1, nil, nil, QUOTE.lastRow, ~.5) Blocks(QUOTE.leftMost + 1, QUOTE.lastRow + 1)",
    c => V(Quote).add(KEYWORD_PROP, sprop(c, "QUOTE")).add(c.LineOfWords[V]).add(c.Blocks[V]))
  grule("BlockWord", "MATH~ Anything(MATH.leftMost + 1, MATH.lastRow + 1)", c => V(Math, c.Anything[V]))
  grule("BlockWord", "VERBATIM~ Anything(VERBATIM.leftMost + 1, VERBATIM.lastRow + 1)", c => V(Verbatim, c.Anything[V]))
  grule("BlockWord", "PROOFSCRIPT~ Anything(PROOFSCRIPT.leftMost + 1, PROOFSCRIPT.lastRow + 1)", c => V(ProofScript, c.Anything[V]))
  grule("BlockWord", "RUN~ Anything(RUN.leftMost + 1, RUN.lastRow + 1)", c => V(Run, c.Anything[V]))
  grule("BlockWord", "Table~", _.Table[V])
  grule("BlockWord", "References~", _.References[V])

  // Reference
  grule("Reference", "REFERENCE~", c => mkReference(c)) 

  // Link
  grule("Link", s"OPENLINK~ Words(~.1, nil, nil, OPENLINK.lastRow + 1, ~.5 ! $B_LINK) CLOSELINK(~.1, nil, Words.val | nil, Words.lastRow + 1)",
    c => V(Link, c.Words[V]))
  grule("Link", "OPENLINK~ CLOSELINK(~.1, nil, nil, OPENLINK.lastRow + 1)",
    c => V(Link))
  grule("Link", s"OPENLINK~ Words(~.1, nil, nil, OPENLINK.lastRow + 1, ~.5 ! $B_LINK) { -1 }",
    c => V(Link, c.Words[V]).addError(eprop(c, "unclosed link, closing ] missing")))
  grule("Link", "OPENLINK~ { -1 }",
    c => V(Link).addError(eprop(c, "unclosed link, closing [ missing")))

  // Emph
  grule("Emph", s"ASTERISK_1~ Words(~.1, nil, nil, ASTERISK_1.lastRow + 1, ~.5 ! $B_EMPH) ASTERISK_2(~.1, nil, Words.val | nil, Words.lastRow + 1)",
    c => V(Emph, c.Words[V]))
  grule("Emph", s"ASTERISK_1~ ASTERISK_2(~.1, nil, nil, ASTERISK_1.lastRow + 1)",
    c => V(Emph))
  grule("Emph", s"ASTERISK_1~ Words(~.1, nil, nil, ASTERISK_1.lastRow + 1, ~.5 ! $B_EMPH) { -1 }",
    c => V(Emph, c.Words[V]).addError(eprop(c, "closing * missing")))
  grule("Emph", s"ASTERISK_1~ { -1 }",
    c => V(Emph).addError(eprop(c, "closing * missing")))

  // DoubleEmph
  grule("DoubleEmph", s"DOUBLEASTERISK_1~ Words(~.1, nil, nil, DOUBLEASTERISK_1.lastRow + 1, ~.5 ! $B_DOUBLEEMPH) DOUBLEASTERISK_2(~.1, nil, Words.val | nil, Words.lastRow + 1)",
    c => V(DoubleEmph, c.Words[V]))
  grule("DoubleEmph", s"DOUBLEASTERISK_1~ DOUBLEASTERISK_2(~.1, nil, nil, DOUBLEASTERISK_1.lastRow + 1)",
    c => V(DoubleEmph))
  grule("DoubleEmph", s"DOUBLEASTERISK_1~ Words(~.1, nil, nil, DOUBLEASTERISK_1.lastRow + 1, ~.5 ! $B_DOUBLEEMPH) { -1 }",
    c => V(DoubleEmph, c.Words[V]).addError(eprop(c, "closing ** missing")))
  grule("DoubleEmph", s"DOUBLEASTERISK_1~ { -1 }",
    c => V(DoubleEmph).addError(eprop(c, "closing ** missing")))  

  // Anything
  grule("Anything", "ANYTHING~", c => V(Anything, sprop(c)))  
  grule("Anything", "", c => V(Anything, sprop(c)))

  // ItemList: (minColumn, minRow, maxStartColumn) => maxStartColumn
  grule("ItemList", "ListItem(~.1, ~.2, ~.3, nil) { ListItem.val }", c => V(ItemList, c.ListItem[V]))
  grule("ItemList", "ItemList_1~ ListItem(~.1, nil, ItemList_1.val, ItemList_1.lastRow + 1) { ListItem.val }",
    c => c.ItemList_1[V].add(c.ListItem[V]))
  grule("ListItem", "LISTBULLET~ Blocks(LISTBULLET.leftMost + 1, nil) { LISTBULLET.leftMost }",
    c => V(ListItem, c.Blocks[V]).add(KEYWORD_PROP, sprop(c, "LISTBULLET")))

  // Table
  grule("Table", "TABLE~ TableParam(TABLE.lastRow) TableBody(TABLE.leftMost + 1)",
    c => c.TableBody[V].addInFront(c.TableParam[V]).add(KEYWORD_PROP, sprop(c, "TABLE")))
  
  // TableParam: maxRowStart => ?
  grule("TableParam", "TableParamCore~ FALLBACKLINE(nil, nil, nil, ~)", 
    c => c.TableParamCore[V].addError(eprop(c, "FALLBACKLINE", "invalid table parameters")))
  grule("TableParam", "TableParamCore~", c => c.TableParamCore[V])
  grule("TableParamCore", "TABLEPARAM(nil, nil, nil, ~)", c => V(TableParam, sprop(c)))
  grule("TableParamCore", "", c => V(TableParam))

  // TableBody: minColumn => maxStartColumn
  grule("TableBody", "", c => V(Table))
  grule("TableBody", "TableBody_1~ TableElem(~, TableBody_1.val) { TableElem.leftMost }", 
    c => c.TableBody_1[V].add(c.TableElem[V]))

  // TableElem: (minColumn, maxStartColumn) => ?
  grule("TableElem", "TableLine~", _.TableLine[V])
  grule("TableElem", "TableRow~", _.TableRow[V])
  grule("TableElem", "FALLBACKPROTRUDE~", c => fallback(c, "TableElem"))

  // TableLine: (minColumn, maxStartColumn) => ?
  grule("TableLine", "LINE(~.1, nil, ~.2)", c => V(ProofDoc.Line))
  grule("TableLine", "LINE(~.1, nil, ~.2) FALLBACKLINE(nil, nil, nil, LINE.lastRow)", 
    c => V(ProofDoc.Line).addError(eprop(c, "FALLBACKLINE", "unexpected parameters to ~line")))

  // TableRow: (minColumn, maxStartColumn) => ?
  grule("TableRow", "ROW(~.1, nil, ~.2) TableCells(ROW.leftMost + 1, nil)", 
    c => c.TableCells[V].add(KEYWORD_PROP, sprop(c, "ROW")))
  grule("TableRow", "ROW(~.1, nil, ~.2) FALLBACKLINE(nil, nil, nil, ROW.lastRow) TableCells(ROW.leftMost + 1, nil)", 
    c => c.TableCells[V].add(KEYWORD_PROP, sprop(c, "ROW")).addError(eprop(c, "FALLBACKLINE", "unexpected parameters to ~row")))

  // TableCells, TableCell: (minColumn, maxStartColumn) => maxStartColumn
  grule("TableCells", "", c => V(Row))
  grule("TableCells", "TableCells_1~ TableCell(~.1, TableCells_1.val | ~.2) { TableCell.leftMost }",
    c => c.TableCells_1[V].add(c.TableCell[V]))
  grule("TableCell", "ITEMHYPHEN(~.1, nil, ~.2) Blocks(ITEMHYPHEN.leftMost+1, nil) { ITEMHYPHEN.leftMost }",
    c => V(Cell, c.Blocks[V]).add(KEYWORD_PROP, sprop(c, "ITEMHYPHEN")))
  grule("TableCell", "FALLBACKPROTRUDE~", c => fallback(c, "TableCell"))

  // References
  grule("References", "REFERENCES~ RefItems(REFERENCES.leftMost + 1)", 
    c => c.RefItems[V].add(KEYWORD_PROP, sprop(c, "REFERENCES")))

  // RefItems: minColumn => maxStartColumn
  grule("RefItems", "", c => V(References))
  grule("RefItems", "RefItems_1~ RefItem(~, RefItems_1.val) { RefItem.leftMost }",
    c => c.RefItems_1[V].add(c.RefItem[V]))

  // RefItem: (minColumn, maxStartColumn) => ?
  grule("RefItem", "RefItemLabel~ RefItemReference(RefItemLabel.lastRow) RefItemFields(RefItemLabel.leftMost + 1)", 
    c => c.RefItemLabel[V].add(c.RefItemReference[V]).add(c.RefItemFields[V]))
  grule("RefItem", "RefItemLabel~ RefItemReference(RefItemLabel.lastRow) FALLBACKLINE(nil, nil, nil, RefItemLabel.lastRow) RefItemFields(RefItemLabel.leftMost + 1)", 
    c => c.RefItemLabel[V].add(c.RefItemReference[V]).add(c.RefItemFields[V]).addError(eprop(c, "FALLBACKLINE", "invalid reference item parameter")))
  grule("RefItem", "FALLBACKPROTRUDE~", c => fallback(c, "RefItem"))
  grule("RefItemLabel", "REFITEMLABEL(~.1, nil, ~.2)", c => mkLexedEntity(c, RefItem, "::", "", unescape _))
  grule("RefItemReference", "Reference(nil, nil, nil, ~)", _.Reference[V])
  grule("RefItemReference", "", c => null)

  // RefItemFields: minColumn => maxStartColumn
  grule("RefItemFields", "", c => V(RefItemFields))
  grule("RefItemFields", "RefItemFields_1~ RefItemField(~, RefItemFields_1.val) { RefItemField.leftMost }",
    c => c.RefItemFields_1[V].add(c.RefItemField[V]))

  // RefItemField: (minColumn, maxStartColumn) => ?
  def gRefItemField(FIELD : String) {
    grule("RefItemField", FIELD + "(~.1, nil, ~.2) Blocks(" + FIELD + ".leftMost + 1)", 
      c => V(RefItemField, c.Blocks[V]).add(DEFAULT_PROP, sprop(c, FIELD)))
  }
  
  grule("RefItemField", "FALLBACKPROTRUDE~", c => fallback(c, "RefItemField"))

  gRefItemField("DISPLAY")
  gRefItemField("AUTHOR")
  gRefItemField("TITLE")
  gRefItemField("IN")
  gRefItemField("YEAR")
  gRefItemField("MONTH")
  gRefItemField("DAY")

  /** Experiment to see how to do error recovery for embedded rich layout-insensitive syntax */

  setScope("Experiment")

  klex("EXPERIMENT", cis("~x"))
  lex("XPLUS", char('+'))
  lex("XTIMES", char('*'))
  lex("XOPEN", char('('))
  lex("XCLOSE", char(')'))
  lex("XVAR", char('n'))

  scope = FALLBACK_SCOPE

  lex("ERROR_F", Lexer.untilWhitespace(REPEAT(CHAR(-range('+', '*', '(', ')')))))
  lex("ERROR", EMPTY)
 
  case object Experiment extends T
  case object Sum extends T
  case object Product extends T
  case object App extends T
  case object Bracket extends T
  case object Var extends T

  grule("BlockWord", "Experiment~", _.Experiment[V])
  grule("Experiment", "EXPERIMENT~ E(EXPERIMENT.leftMost + 1)", c => V(Experiment, c.E[V]))
  grule("Experiment", "EXPERIMENT~ E(EXPERIMENT.leftMost + 1) FALLBACK(EXPERIMENT.leftMost + 1)",
    c => V(Experiment, c.E[V]).addError(eprop(c, "FALLBACK", "superfluous input")))
  grule("E", "E_1~ XPLUS~ T~", c => V(Sum, c.E_1[V]).add(c.T[V]))
  grule("E", "T~", _.T[V])
  grule("T", "T_1~ XTIMES~ A~", c => V(Product, c.T_1[V]).add(c.A[V]))
  grule("T", "A~", _.A[V])
  grule("A", "A_1~ F~", c => V(App, c.A_1[V]).add(c.F[V]))
  grule("A", "F~", _.F[V])
  grule("F", "XVAR~", c => V(Var))
  grule("F", "XOPEN~ E~ XCLOSE~", c => V(Bracket, c.E[V]))
  grule("F", "XOPEN~ E~ ERROR", c => V(Bracket, c.E[V]).addError(eprop(c, "missing closing bracket")))  
  grule("F", "ERROR_F~", c => fallback(c, "F").add(DEFAULT_PROP,sprop(c)))

}

object ProofDocTest {

  val testSource = """
package proofpeer.editor

import proofpeer.vue._
import proofpeer.vue.dom._
import proofpeer.vue.components._

import scala.scalajs.js
import js.annotation._


object CodeMirror extends CustomComponentClass {

  case object READONLY extends CustomAttributeName[Boolean]("readonly")

  trait KeyHandler {
    def allowKeypress(c : String) : Boolean
    def allowKeydown(keycode : Int) : Boolean
  }
  case object KEY_HANDLER extends CustomAttributeName[KeyHandler]("keyhandler")

  trait ActivityHandler {
    def cursorActivity()
    def scrollActivity()
    def contentActivity()
  }
  case object ACTIVITY_HANDLER extends CustomAttributeName[ActivityHandler]("activityhandler")


  private val DEFAULT_KEY_HANDLER = new KeyHandler {
    def allowKeypress(c : String) : Boolean = true
    def allowKeydown(keycode : Int) : Boolean = true
  }

  private val DEFAULT_ACTIVITY_HANDLER = new ActivityHandler {
    def cursorActivity() {}
    def scrollActivity() {}
    def contentActivity() {}
  }

  def render(parentNode : dom.Node, component : CustomComponent) : Blueprint = {
    DIV(component)()
  }

  private class Router(keyHandler : KeyHandler, activityHandler : ActivityHandler) {

    def keypresshandler(cm : js.Dynamic, event : js.Dynamic) {
      val c : Char = event.charCode.asInstanceOf[Int].toChar
      if (!keyHandler.allowKeypress(c.toString)) {
        event.preventDefault()
      }
    }

    def keydownhandler(cm : js.Dynamic, event : js.Dynamic) {
      if (!keyHandler.allowKeydown(event.keyCode.asInstanceOf[Int])) {
        event.preventDefault()
      }
    }

    def cursorActivity() {
      activityHandler.cursorActivity()
    }

    def scrollActivity() {
      activityHandler.scrollActivity()
    }

    def contentActivity() {
      activityHandler.contentActivity()
    }

    def register(cm : js.Dynamic) {
      cm.on("keydown", (keydownhandler _) : js.Function2[js.Dynamic, js.Dynamic, Unit])
      cm.on("keypress", (keypresshandler _) : js.Function2[js.Dynamic, js.Dynamic, Unit])
      cm.on("cursorActivity", (cursorActivity _) : js.Function0[Unit])
      cm.on("scroll", (scrollActivity _) : js.Function0[Unit])
      cm.on("change", (contentActivity _) : js.Function0[Unit])
    }

  }

  override def componentDidMount(component : CustomComponent) {
    val readOnly : Any = 
      if (component.attributes(READONLY, true)) "nocursor" else false
    val editor = js.Dynamic.global.CodeMirror(component.mountNode(), 
      js.Dictionary("lineNumbers" -> true, "readOnly" -> readOnly, 
        "indentUnit" -> 2, "tabSize" -> 2, "indentWithTabs" -> true, "mode" -> "proofdoc"))
    component.setLocalState(editor)
    val dims = component.attributes(DIMS)
    editor.setSize(dims.width.get - 4, dims.height.get - 4)
    editor.setValue("")
    val router = new Router(
      component.attributes(KEY_HANDLER, DEFAULT_KEY_HANDLER),
      component.attributes(ACTIVITY_HANDLER, DEFAULT_ACTIVITY_HANDLER))
    editor.focus()
    router.register(editor)
  }

  override def componentWillReceiveBlueprint(component : CustomComponent, nextBlueprint : Blueprint) {
    val editor : js.Dynamic = component.localState
    if (editor != null) {
      val dims = nextBlueprint.attributes(DIMS)
      val readOnly = component.attributes(READONLY, true)
      editor.setSize(dims.width.get - 4, dims.height.get - 4)
    }
  }

  private def codeMirror(component : Component) : js.Dynamic = {
    component.asInstanceOf[CustomComponent].localState[js.Dynamic]    
  }

  def insertAtCursor(component : Component, s : String) {
    val cm = codeMirror(component)
    val pos = cm.getCursor()
    cm.replaceRange(s, pos)
    cm.focus()
  }

  def focus(component : Component) {
    codeMirror(component).focus()
  }

  def getContent(component : Component) : String = {
    val cm = codeMirror(component)
    cm.getValue().asInstanceOf[String]
  }

  def getCursorPosition(component : Component) : (Int, Int) = {
    val cm = codeMirror(component)
    val cursor = cm.getCursor()
    (cursor.line.asInstanceOf[Int], cursor.ch.asInstanceOf[Int])
  }

  def isInitialized(component : Component) = codeMirror(component) != null

  def getScrollPosition(component : Component) : (Int, Int) = {
    val cm = codeMirror(component)
    val info = cm.getScrollInfo()
    (info.left.asInstanceOf[Int], info.top.asInstanceOf[Int])
  }

  private var hasBeenSetup : Boolean = false

  def setup() {
    if (hasBeenSetup) return
    hasBeenSetup = true
    val cs = ConfigSheet()
    val fs = cs.bodyStyle
    Styling.addRules(
      .CodeMirror {
        background-color: white;
        border: solid 2px #c9c9c9;
      }
    )
    def mkMode(config : js.Dynamic, modeConfig : js.Dynamic) : js.Any = {
      new ProofDocMode()
    }
    js.Dynamic.global.CodeMirror.defineMode("proofdoc", (mkMode _ ) : js.Function2[js.Dynamic, js.Dynamic, js.Any]) 
  }
  
}

@ScalaJSDefined
class ProofDocModeState extends js.Object {
  var len : Int = 0
}

@ScalaJSDefined
class ProofDocMode extends js.Object {

  def println(x : Any) {
    //System.out.println(x)
  }
  
  def startState() : ProofDocModeState = {
    println("startState")
    new ProofDocModeState()
  }

  def copyState(p : ProofDocModeState) : ProofDocModeState = {
    println("copyState (len = " + p.len + ")")
    val q = new ProofDocModeState()
    q.len = p.len
    q
  }

  def token(stream : js.Dynamic, state : ProofDocModeState) : String = {
    var len = state.len
    def isWhitespace(s : String) : Boolean = s == " "
    def isNotWhitespace(s : String) : Boolean = s != null && s != " "
    def str(s : js.Dynamic) : String = {
      s.asInstanceOf[js.UndefOr[String]].toOption match {
        case None => null
        case Some(s) => s
      }      
    }
    def peek(stream : js.Dynamic) : String = {
      str(stream.peek())
    }
    def next(stream : js.Dynamic) : String = {
      str(stream.next())
    }
    while (isWhitespace(peek(stream))) { 
      len += 1 
      next(stream)
    }
    if (len != state.len) {
      state.len = len
      null
    } else {
      var token = ""
      while (isNotWhitespace(peek(stream))) {
        len += 1
        token += next(stream)
      }
      println("token at (" + state.len + "): " + token)
      state.len = len
      "error"
    }
  }

  def blankLine(state : ProofDocModeState) {
    println("blankLine (len = " + state.len + ")")
  }



}

"""    

  import proofpeer.indent._
  import proofpeer.proofscript.frontend._
  import proofpeer.proofscript.logic.Namespace

  private val src = new Source(Namespace.root, "userinput")

  def mkSourcePosition(s : Option[Span]) : SourcePosition = {
    new SourcePosition {
      def source = src
      def span = s
    }
  }

  def annotate(obj : Any, span : Option[Span]) : Any = {
    if (obj.isInstanceOf[TracksSourcePosition]) {
      obj.asInstanceOf[TracksSourcePosition].sourcePosition = mkSourcePosition(span)
    }
    obj
  }

  val grammar = new ProofDocSyntax(annotate _).grammar
  val parser = new Parser(grammar, true)

  def parse(content : String) {
    proofpeer.indent.earley.Earley.debug = true
    val d = Document.fromString(content, Some(2))
    var r : String = ""
    def report(s : String) {
      println(s)
    }
    report("parsing ...")
    def loc(s : Span) : String = {
      if (s.firstRow == s.lastRow) {
        if (s.rightMostLast == s.leftMostFirst)
          "line " + (s.firstRow + 1) + ", column " + (s.leftMostFirst + 1)
        else
          "line " + (s.firstRow + 1) + ", columns " + (s.leftMostFirst + 1) + " - " + (s.rightMostLast + 1) 
      } else {
        "line " + (s.firstRow + 1) + ", column " + (s.leftMostFirst + 1) + " - "
        "line " + (s.lastRow + 1) + ", column " + (s.rightMostLast + 1) 
      }
    }
    val t1 = System.currentTimeMillis
    parser.earley.parse(d, "ProofDoc") match {
      case Left(parsetree) => 
        val t2 = System.currentTimeMillis
        report("parsed in: " + (t2 - t1))
      case Right(errorposition) => 
        if (errorposition < 0) report("error parsing at start of document")
        else if (errorposition >= d.size) report("error parsing at end of document")
        else {
          val (row, column, _) = d.character(errorposition)
          report("error parsing at line " + (row + 1) + ", column " + (column + 1))
        }   
    }
    r            
  }

  def mainx(args : Array[String]) {
    println("ProofDocTest")
    parse(testSource)
    parse(testSource)
  }






}
