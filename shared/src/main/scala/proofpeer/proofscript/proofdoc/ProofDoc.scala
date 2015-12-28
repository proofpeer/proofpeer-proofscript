package proofpeer.proofscript.proofdoc

import proofpeer.proofscript.frontend.{TracksSourcePosition, ParseTree}
import proofpeer.general.StringUtils
import proofpeer.indent.Document

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

  case object InlineMath extends T

  case object InlineVerbatim extends T

  case object InlineProofScript extends T

  case object InlineRun extends T

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

final object Linearization {
  import ProofDoc.V

  type Style = String

  final case class Position(row : Int, column : Int) extends Ordered[Position] {
    def compare(that : Position) : Int = {
      if (row < that.row) -1
      else if (row > that.row) 1
      else if (column < that.column) -1
      else if (column > that.column) 1
      else 0
    }
    def inc(document : Document) : Position = {
      Position(row, column + 1)
    }
    def dec(document : Document) : Position = {
      if (column > 0)
        Position(row, column - 1)
      else {
        assert(row > 0)
        Position(row - 1, document.lengthOfRow(row - 1))
      }
    }
  }

  case class Token(startPosition : Position, endPosition : Position, styles : Set[String]) {
    assert(startPosition <= endPosition)
  }

  type Tokens = Vector[Token]

  val empty : Tokens = Vector()

  def single(token : Token) : Tokens = Vector(token)

  def concat(tokens1 : Tokens, tokens2 : Tokens) : Tokens = {
    if (tokens1.isEmpty) tokens2
    else if (tokens2.isEmpty) tokens1
    else {
      val u = tokens1.last
      val v = tokens2.head
      assert (u.endPosition < v.startPosition)
      tokens1 ++ tokens2
    }
  }

  def append(tokens : Tokens, v : Token) : Tokens = {
    if (tokens.isEmpty) single(v) 
    else {
      val u = tokens.last
      assert (u.endPosition < v.startPosition)
      tokens :+ v
    }
  }

  def make(document : Document, v : V) : Tokens = {
    new MakeTokens(document).make(v)
  }

  private class MakeTokens(document : Document) {

    def increment(p : Position, limit : Position) : Position = {
      val q = p.inc(document)
      if (q > limit) limit else q
    }

    def decrement(p : Position, limit : Position) : Position = {
      val q = p.dec(document)
      if (q < limit) limit else q
    }

    def make(v : V) : Tokens = {
      val tokens = make(v, empty)
      val r = document.numberOfRows - 1
      if (r >= 0) {
        val start = Position(0, 0)
        val end = Position(r, document.lengthOfRow(r))
        addStyle(addStyle(tokens, start, end, "text"), start, end, "proofdoc")
      } else 
        tokens
    }

    def make(v : V, tokens : Tokens) : Tokens = {
      import ProofDoc._
      v.ty match {
        case Fallback => makeFallback(v, "error", tokens)
        case Ambiguity => makeSimple(v, "ambiguity", tokens)
        case Reference => makeSimple(v, "reference", tokens)
        case User => makeSimple(v, "user", tokens)
        case Link => makeSimpleRecursive(v, "link", tokens)
        case Emph => makeSimpleRecursive(v, "emph", tokens)
        case Label => makeSimple(v, "label", tokens)
        case LabelOpen => makeSimple(v, "label", tokens)
        case LabelClose => makeSimple(v, "label", tokens)
        case DoubleEmph => makeSimpleRecursive(v, "doubleemph", tokens)
        case Header => 
          val level = v.props(KEYWORD_PROP).asInstanceOf[StringProp].s.length
          val style = "header" + (if (level <= 3) level else 3)
          makeSimpleRecursive(v, style, tokens)
        case Emoticon => makeSimple(v, "emoticon", tokens)
        case Hashtag => makeSimple(v, "hashtag", tokens)
        case InlineMath => makeSimple(v, "inlinemath", tokens)
        case InlineVerbatim => makeSimple(v, "inlineverbatim", tokens)
        case InlineRun => makeSimple(v, "inlinerun", tokens)
        case InlineProofScript => makeSimple(v, "inlineproofscript", tokens)
        case Math => makeKeywordAnythingBlock(v, "keyword", "math", tokens)
        case Verbatim => makeKeywordAnythingBlock(v, "keyword", "verbatim", tokens)
        case ProofScript => makeKeywordAnythingBlock(v, "keyword", "proofscript", tokens)
        case Run => makeKeywordAnythingBlock(v, "keyword", "run", tokens)
        case ListItem => makeKeywordRecursive(v, "listbullet", tokens)
        case Table => makeKeywordRecursive(v, "keyword", tokens)
        case Line => makeKeywordRecursive(v, "keyword", tokens)
        case Row => makeKeywordRecursive(v, "keyword", tokens)
        case Cell => makeKeywordRecursive(v, "keyword", tokens)
        case TableParam => makeTableParam(v, tokens)
        case Quote => makeQuote(v, "keyword", "quote", tokens)
        case References => makeKeywordRecursive(v, "keyword", tokens)
        case RefItem => makeDefaultRecursive(v, "label", tokens)
        case RefItemFields => makeRecursive(v, tokens)
        case RefItemField => makeKeywordRecursive(v, "keyword", tokens)
        case _ => makeRecursive(v, tokens)
      }
    }

    def isEmpty(t : TracksSourcePosition) : Boolean = {
      t.sourcePosition.span.get.isNull
    }

    def locationOf(t : TracksSourcePosition) : (Position, Position) = {
      if (document.size == 0) return (Position(0, 0), Position(0, 0))
      val span = t.sourcePosition.span.get
      if (span.firstIndexIncl < span.lastIndexExcl) {
        val (r1, c1, _) = document.character(span.firstIndexIncl)
        val (r2, c2, _) = document.character(span.lastIndexExcl - 1)
        (Position(r1, c1), Position(r2, c2))
      } else if (span.firstIndexIncl > 0 && span.firstIndexIncl < document.size) {
        val (r1, c1, _) = document.character(span.firstIndexIncl - 1)
        val (r2, c2, _) = document.character(span.firstIndexIncl)
        (Position(r1, c1 + 1), Position(r2, c2))
      } else if (span.firstIndexIncl == 0) {
        val (r, c, _) = document.character(0)
        (Position(0, 0), Position(r, c))
      } else /* span.firstIndexIncl >= document.size */ {
        val (r, c, _) = document.character(span.firstIndexIncl - 1)
        (Position(r, c), Position(r, c + 1))
      }
    }

    def addStyle(tokens : Tokens, startPosition : Position, endPosition : Position, style : Style) : Tokens = {
      assert(startPosition <= endPosition)
      var start = startPosition
      var end = endPosition
      var processing : Boolean = true
      var newTokens : Tokens = Vector()
      for (t <- tokens) {
        if (processing) {
          if (end < t.startPosition) {
            newTokens = append(append(newTokens, Token(start, end, Set(style))), t)
            processing = false
          } else if (start > t.endPosition) {
            newTokens = append(newTokens, t)
            processing = true
          } else {
            if (start < t.startPosition) {
              newTokens = append(newTokens, Token(start, decrement(t.startPosition, start), Set(style)))
              start = t.startPosition
            } else if (start > t.startPosition) {
              newTokens = append(newTokens, Token(t.startPosition, decrement(start, t.startPosition), t.styles))
            } 
            // start points now to the beginning of the new token with the combined styles
            if (end > t.endPosition) {
              newTokens = append(newTokens, Token(start, t.endPosition, t.styles + style))
              start = increment(t.endPosition, end)
              processing = true
            } else if (end < t.endPosition) {
              newTokens = append(newTokens, Token(start, end, t.styles + style))
              newTokens = append(newTokens, Token(increment(end, t.endPosition), t.endPosition, t.styles))
              processing = false
            } else /* end == t.endPosition */ {
              newTokens = append(newTokens, Token(start, end, t.styles + style))
              processing = false
            }
          }
        } else 
          newTokens = append(newTokens, t)
      }
      if (processing) {
        newTokens = append(newTokens, Token(start, end, Set(style)))
      }
      newTokens
    }

    // apply the style to the whole span of V
    // do not descend further into V
    def makeSimple(v : V, style : Style, tokens : Tokens) : Tokens = {
      val l = locationOf(v)
      val ts = if (isEmpty(v)) empty else single(Token(l._1, l._2, Set(style))) 
      val errors = makeErrors(v.errors.map(locationOf _), ts)
      concat(tokens, errors)
    }

    def makeFallback(v : V, style : Style, tokens : Tokens) : Tokens = {
      val l = locationOf(v)
      addStyle(tokens, l._1, l._2, "error")
    }

    // descend into V to compute the styles to be applied 
    def makeRecursive(v : V, tokens : Tokens) : Tokens = {
      var ts : Tokens = empty
      for (value <- v.values) ts = make(value, ts)
      concat(tokens, makeErrors(v.errors.map(locationOf _), ts))
    }

    // combines makeSimple and makeRecursive
    def makeSimpleRecursive(v : V, style : Style, tokens : Tokens) : Tokens = {
      var ts : Tokens = empty
      for (value <- v.values) ts = make(value, ts)
      val l = locationOf(v)
      ts = if (isEmpty(v)) ts else addStyle(ts, l._1, l._2, style)
      concat(tokens, makeErrors(v.errors.map(locationOf _), ts))
    }

    def makeErrors(errors : Vector[(Position, Position)], tokens : Tokens) : Tokens = {
      var ts = tokens
      for ((startPosition, endPosition) <- errors)
        ts = addStyle(ts, startPosition, endPosition, "error")
      ts
    }

    def makeKeywordAnythingBlock(v : V, keywordStyle : Style, anythingStyle : Style, tokens : Tokens) : Tokens = {
      val keywordLocation = locationOf(v.props(ProofDoc.KEYWORD_PROP))
      val keywordToken = Token(keywordLocation._1, keywordLocation._2, Set(keywordStyle))
      val span = v.values(0).sourcePosition.span.get
      val ts = 
        if (span.isNull) {
          single(keywordToken)
        } else {
          val start = Position(span.firstRow, 0)
          val end = Position(span.lastRow, document.lengthOfRow(span.lastRow) - 1)
          addStyle(single(keywordToken), start, end, anythingStyle)
        }
      concat(tokens, makeErrors(v.errors.map(locationOf _), ts))
    }

    def makeKeywordRecursive(v : V, keywordStyle : Style, tokens : Tokens) : Tokens = {
      val keywordLocation = locationOf(v.props(ProofDoc.KEYWORD_PROP))
      val keywordToken = Token(keywordLocation._1, keywordLocation._2, Set(keywordStyle))
      makeRecursive(v, append(tokens, keywordToken))
    }

    def makeDefaultRecursive(v : V, keywordStyle : Style, tokens : Tokens) : Tokens = {
      val keywordLocation = locationOf(v.props(ProofDoc.DEFAULT_PROP))
      val keywordToken = Token(keywordLocation._1, keywordLocation._2, Set(keywordStyle))
      makeRecursive(v, append(tokens, keywordToken))
    }

    def makeQuote(v : V, keywordStyle : Style, quoteStyle : Style, tokens : Tokens) : Tokens = {
      val keywordLocation = locationOf(v.props(ProofDoc.KEYWORD_PROP))
      val keywordToken = Token(keywordLocation._1, keywordLocation._2, Set(keywordStyle))
      val ts = makeRecursive(v, append(tokens, keywordToken))
      val token = ts.last
      val start = Position(keywordToken.startPosition.row + 1, 0)
      val end = locationOf(v)._2
      if (start <= end) addStyle(ts, start, end, quoteStyle) else ts
    }

    def makeTableParam(v : V, tokens : Tokens) : Tokens = {
      val paramProp = v.props(ProofDoc.DEFAULT_PROP)
      val (pos, _) = locationOf(paramProp)
      val s = paramProp.asInstanceOf[ProofDoc.StringProp].s
      var ts = makeRecursive(v, tokens)
      var i = 0
      for (c <- s) {
        val style = if (c == '|') "tableparam-bar" else "tableparam-orientation"
        val p = Position(pos.row, pos.column + i)
        ts = addStyle(ts, p, p, style)
        i = i + 1
      }
      ts
    }

  }

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

    val zero = false

    val first = Range('`')

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

    val zero = false

    val first = Range.universal

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
  lex("LABELOPEN", seq(string("::("), simpleword))
  lex("LABELCLOSE", seq(simpleword, string(")::")))
  lex("HYPHEN", char('-'))
  lex("ENDASH", string("--"))
  lex("EMDASH", string("---"))
  lex("LEFTQUOTE", Lexer.demandLeftBorder(Lexer.untilWhitespace(string("'")), 0, nonsimple))
  lex("RIGHTQUOTE", Lexer.demandRightBorder(Lexer.untilWhitespace(string("'")), 0, nonsimple)) 
  lex("LEFTDOUBLEQUOTE", Lexer.demandLeftBorder(Lexer.untilWhitespace(char('"')), 0, nonsimple))
  lex("RIGHTDOUBLEQUOTE", Lexer.demandRightBorder(Lexer.untilWhitespace(char('"')), 0, nonsimple)) 
  klex("REFITEMLABEL", simpleword)
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
  lex("TABLEPARAM", Lexer.untilNewline(REPEAT1(alt(char('|'), cis("c"), cis("l"), cis("r")))))
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
  lex("INLINEMATH", Lexer.untilNewline(seq(char('$'), REPEAT(CHAR(-Range('$'))), OPT(char('$')))))
  lex("INLINEVERBATIM", Lexer.untilNewline(seq(char('`'), REPEAT(CHAR(-Range('`'))), OPT(char('`')))))
  lex("INLINERUN", Lexer.untilNewline(seq(char('{'), REPEAT(CHAR(-Range('}'))), OPT(char('}')))))
  lex("INLINEPROOFSCRIPT", InlineProofScriptLexer)
  lex("REFERENCE", Lexer.untilNewline(seq(char('<'), REPEAT(CHAR(-Range('>'))), OPT(char('>')))))
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

  def mkInlineMath(c : ParseContext) : V = mkLexedEntity(c, InlineMath, "$", "$")

  def mkReference(c : ParseContext) : V = mkLexedEntity(c, Reference, "<", ">")

  def mkInlineVerbatim(c : ParseContext) : V = mkLexedEntity(c, InlineVerbatim, "`", "`")

  def mkInlineRun(c : ParseContext) : V = mkLexedEntity(c, InlineRun, "{", "}")

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
    mkLexedEntity(c, InlineProofScript, "``", "``", prep _)
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
  grule("CompactWord", "LABELOPEN~", c => mkLexedEntity(c, LabelOpen, "::(", "", unescape _))
  grule("CompactWord", "LABELCLOSE~", c => mkLexedEntity(c, LabelClose, "", ")::", unescape _))
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
  grule("BlockWord", "QUOTE~ Blocks(QUOTE.leftMost + 1, QUOTE.lastRow + 1)",
    c => V(Quote).add(KEYWORD_PROP, sprop(c, "QUOTE")).add(c.Blocks[V]))
  grule("BlockWord", "QUOTE~ FALLBACKLINE(nil, nil, nil, QUOTE.lastRow) Blocks(QUOTE.leftMost + 1, QUOTE.lastRow + 1)",
    c => V(Quote).add(KEYWORD_PROP, sprop(c, "QUOTE")).addError(
      eprop(c, "FALLBACKLINE", "superfluous parameter")).add(c.Blocks[V]))
  grule("BlockWord", "Table~", _.Table[V])
  grule("BlockWord", "References~", _.References[V])
  
  def mkBlockWord(terminal : String, t : T) {
    grule("BlockWord", s"$terminal~ Anything($terminal.leftMost + 1, $terminal.lastRow + 1)", 
      c => V(t, c.Anything[V]).add(KEYWORD_PROP, sprop(c, terminal)))
    grule("BlockWord", s"$terminal~ FALLBACKLINE(nil, nil, nil, $terminal.lastRow) Anything($terminal.leftMost + 1, $terminal.lastRow + 1)", 
      c => V(t, c.Anything[V]).addError(eprop(c, "FALLBACKLINE", "superfluous parameter")).add(KEYWORD_PROP, sprop(c, terminal)))
  }
  
  mkBlockWord("MATH", Math)
  mkBlockWord("VERBATIM", Verbatim)
  mkBlockWord("PROOFSCRIPT", ProofScript)
  mkBlockWord("RUN", Run)

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
  grule("TableParamCore", "", c => V(TableParam, sprop(c)))

  // TableBody: minColumn => maxStartColumn
  grule("TableBody", "", c => V(Table))
  grule("TableBody", "TableBody_1~ TableElem(~, TableBody_1.val) { TableElem.leftMost }", 
    c => c.TableBody_1[V].add(c.TableElem[V]))

  // TableElem: (minColumn, maxStartColumn) => ?
  grule("TableElem", "TableLine~", _.TableLine[V])
  grule("TableElem", "TableRow~", _.TableRow[V])
  grule("TableElem", "FALLBACKPROTRUDE~", c => fallback(c, "TableElem"))

  // TableLine: (minColumn, maxStartColumn) => ?
  grule("TableLine", "LINE(~.1, nil, ~.2)", c => V(ProofDoc.Line).add(KEYWORD_PROP, sprop(c, "LINE")))
  grule("TableLine", "LINE(~.1, nil, ~.2) FALLBACK(LINE.leftMost + 1)", 
    c => V(ProofDoc.Line).add(KEYWORD_PROP, sprop(c, "LINE")).addError(
      eprop(c, "FALLBACK", "unexpected parameters to ~line")))

  // TableRow: (minColumn, maxStartColumn) => ?
  grule("TableRow", "ROW(~.1, nil, ~.2) TableCells(ROW.leftMost + 1, nil)", 
    c => c.TableCells[V].add(KEYWORD_PROP, sprop(c, "ROW")))
  grule("TableRow", "ROW(~.1, nil, ~.2) FALLBACKLINE(nil, nil, nil, ROW.lastRow) TableCells(ROW.leftMost + 1, nil)", 
    c => c.TableCells[V].add(KEYWORD_PROP, sprop(c, "ROW")).addError(
      eprop(c, "FALLBACKLINE", "unexpected parameters to ~row")))

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
  grule("References", "REFERENCES~ FALLBACKLINE(nil, nil, nil, REFERENCES.lastRow) RefItems(REFERENCES.leftMost + 1)", 
    c => c.RefItems[V].add(KEYWORD_PROP, sprop(c, "REFERENCES")).addError(eprop(c, "FALLBACKLINE", "superfluous parameter")))

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
  grule("RefItemLabel", "REFITEMLABEL(~.1, nil, ~.2)", c => mkLexedEntity(c, RefItem, "", "", unescape _))
  grule("RefItemReference", "Reference(nil, nil, nil, ~)", _.Reference[V])
  grule("RefItemReference", "", c => null)

  // RefItemFields: minColumn => maxStartColumn
  grule("RefItemFields", "", c => V(RefItemFields))
  grule("RefItemFields", "RefItemFields_1~ RefItemField(~, RefItemFields_1.val) { RefItemField.leftMost }",
    c => c.RefItemFields_1[V].add(c.RefItemField[V]))

  // RefItemField: (minColumn, maxStartColumn) => ?
  def gRefItemField(FIELD : String) {
    grule("RefItemField", FIELD + "(~.1, nil, ~.2) Blocks(" + FIELD + ".leftMost + 1)", 
      c => V(RefItemField, c.Blocks[V]).add(KEYWORD_PROP, sprop(c, FIELD)))
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
