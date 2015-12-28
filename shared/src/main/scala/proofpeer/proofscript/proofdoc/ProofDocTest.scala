package proofpeer.proofscript.proofdoc

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

  def main(args : Array[String]) {
    println("ProofDocTest")
    parse(testSource)
    parse(testSource)
  }






}
