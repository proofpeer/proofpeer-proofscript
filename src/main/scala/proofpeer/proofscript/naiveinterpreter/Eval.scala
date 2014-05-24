package proofpeer.proofscript.naiveinterpreter

import proofpeer.proofscript.frontend._
import proofpeer.proofscript.logic._


class Eval(states : States, kernel : Kernel, nameresolution : NameResolution, 
	resolveNamespace : Namespace => Namespace, namespace : Namespace) 
{

	def evalStatements(state : State, statements : Vector[ParseTree.Statement]) : Option[State] = {
		Some(state)
	}

}