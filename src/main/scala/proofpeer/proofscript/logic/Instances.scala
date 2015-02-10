package proofpeer.proofscript.logic

import scala.language.implicitConversions
import scalaz._
import Scalaz._

object EqualsInstances {
  implicit object TermIsEqual extends Equal[Term] {
    def equal(l: Term, r: Term) = l == r
  }
}
