package proofpeer.proofscript.naiveinterpreter

import proofpeer.proofscript.logic._

trait StateValue {}

case class ContextValue(value : Context) extends StateValue
case class TheoremValue(value : Theorem) extends StateValue
case class TermValue(value : Term) extends StateValue
case class BoolValue(value : Boolean) extends StateValue
case class IntValue(value : BigInt) extends StateValue
case class FunctionValue(value : StateValue => StateValue) extends StateValue
case class TupleValue(value : Vector[StateValue]) extends StateValue

class State(val context : Context, values : Map[String, StateValue]) {

	def lookup(id : String) : Option[StateValue] = values.get(id)

	def put(id : String, v : StateValue) : State = {
		new State(context, values + (id -> v))
	}

	def put(ctx : Context) : State = {
		new State(ctx, values)
	}

}

trait States {

	def lookup(namespace : Namespace) : Option[State]

	def register(namespace : Namespace, state : State)

}

object States {

	private class SimpleStates extends States {
		var states : Map[Namespace, State] = Map()
		def lookup(namespace : Namespace) = states.get(namespace)
		def register(namespace : Namespace, state : State) {
			states = states + (namespace -> state)
		}
	}

}

