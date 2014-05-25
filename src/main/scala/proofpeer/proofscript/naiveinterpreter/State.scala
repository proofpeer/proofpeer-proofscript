package proofpeer.proofscript.naiveinterpreter

import proofpeer.proofscript.logic._

trait StateValue {}

trait Collect {}
object Collect {
	case object Zero extends Collect
	case object One extends Collect
	case class Multiple(collector : Collector) extends Collect 

	trait Collector {
		def add(value : StateValue) : Collector 
		def reap : StateValue
	}

	private class TupleCollector(collected : List[StateValue]) extends Collector {
		def add(value : StateValue) = new TupleCollector(value :: collected)
		def reap : StateValue = TupleValue(collected.reverse.toVector)
	}

	private val emptyTupleCollector = new TupleCollector(List())

	def emptyMultiple : Multiple = Multiple(emptyTupleCollector)
}


case class ContextValue(value : Context) extends StateValue
case class TheoremValue(value : Theorem) extends StateValue
case class TermValue(value : Term) extends StateValue
case class BoolValue(value : Boolean) extends StateValue
case class IntValue(value : BigInt) extends StateValue
case class FunctionValue(value : StateValue => StateValue) extends StateValue
case class TupleValue(value : Vector[StateValue]) extends StateValue

class State(val context : Context, val values : Map[String, StateValue], val assignables : Set[String]) {

	def lookup(id : String) : Option[StateValue] = values.get(id)

	def put(id : String, v : StateValue) : State = {
		new State(context, values + (id -> v), assignables + id)
	}

	def freeze : State = {
		new State(context, values, Set())
	}

	def put(ctx : Context) : State = {
		new State(ctx, values, assignables)
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

	def empty : States = new SimpleStates()

}

