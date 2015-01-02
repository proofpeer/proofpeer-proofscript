package proofpeer.proofscript.frontend

import ParseTree._
import proofpeer.general.{VectorSerializer, Serializer}
import proofpeer.indent.Span

case class SerializedSourcePosition(source : Source, span : Option[Span]) extends SourcePosition

class ParseTreeSerializer(source : Source, computeSpan : (Int, Int) => Span) extends Serializer[ParseTree, Vector[Any]] {

  val PTS = this

  private object Kind {
    val BLOCK = 1
    val STTHEORY = 2
    val STTHEOREM = 3
    val STCHOOSE = 4
    val STLET = 5
    val STASSUME = 6
    val STRETURN = 7
    val STDEF = 8
    val DEFCASE = 9
    val STASSIGN = 10
    val STVALINTRO = 11
    val STVAL = 12
    val STFAILURE = 13
    val STASSERT = 14
    val STFAIL = 15
    val STSHOW = 16
    val STCONTROLFLOW = 17
    val STEXPR = 18
    val STCOMMENT = 19
  }

  object StatementSerializer extends Serializer[Statement, Any] {

    def serialize(statement : Statement) : Any = PTS.serialize(statement)

    def deserialize(serialized : Any) : Statement = {
      PTS.deserialize(serialized) match {
        case statement : Statement => statement
        case d => throw new RuntimeException("cannot deserialize, statement expected, found: " + d)
      } 
    }

  }

  private val StatementsSerializer = VectorSerializer(StatementSerializer)

  def serialize(parsetree : ParseTree) : Vector[Any] = {
    val (kind, args) : (Int, Vector[Any]) =
      parsetree match {
        case Block(statements) => (Kind.BLOCK, StatementsSerializer.serialize(statements))      
        case _ => throw new RuntimeException("cannot serialize parse tree: " + parsetree)
      }
    val (firstTokenIndex, lastTokenIndex) =
      if (parsetree.sourcePosition == null) 
        (-1, -1)
      else 
        parsetree.sourcePosition.span match {
          case None => (-1, -1)
          case Some(span) => (span.firstTokenIndex, span.lastTokenIndex)
        }
    kind +: firstTokenIndex +: lastTokenIndex +: args
  }

  private def toInt(v : Any) = v.asInstanceOf[Long].toInt

  def deserialize(serialized : Any) : ParseTree = {
    serialized match {
      case v : Vector[Any] if v.size >= 3 =>
        val kind = toInt(v(0))
        val firstTokenIndex = toInt(v(1))
        val lastTokenIndex = toInt(v(2))
        val args : Vector[Any] = v.drop(3)
        val tree = 
          (kind, args) match {
            case (Kind.BLOCK, _) => Block(StatementsSerializer.deserialize(args))
            case (k, _) => throw new RuntimeException("cannot deserialize parse tree with kind " + k +" and these arguments: " + args)
          }
        if (firstTokenIndex < 0)
          tree.sourcePosition = SerializedSourcePosition(source, None)
        else
          tree.sourcePosition = SerializedSourcePosition(source, Some(computeSpan(firstTokenIndex, lastTokenIndex)))
        tree
      case _ => throw new RuntimeException("cannot deserialize parse tree: " + serialized)
    }
  }

}
