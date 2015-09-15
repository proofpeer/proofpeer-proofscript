package proofpeer.proofscript.proofdoc

import proofpeer.proofscript.frontend.{TracksSourcePosition, ParseTree}

sealed trait ProofDoc extends ParseTree 

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

}
