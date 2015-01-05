package proofpeer.proofscript.serialization

import proofpeer.proofscript.logic.Namespace

trait UniquelyIdentifiable {
  var optionalUniqueIdentifier : Option[(Namespace, Long)] = None
}
