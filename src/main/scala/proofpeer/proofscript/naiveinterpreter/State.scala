package proofpeer.proofscript.naiveinterpreter

import proofpeer.proofscript.logic._

trait StateValue {}

trait Collect {}
object Collect {
	case object Zero extends Collect
	case class One(collected : Option[StateValue]) extends Collect
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

	def emptyOne : One = One(None)
}


case class ContextValue(value : Context) extends StateValue
case class TheoremValue(value : Theorem) extends StateValue
case class TermValue(value : Term) extends StateValue
case class BoolValue(value : Boolean) extends StateValue
case class IntValue(value : BigInt) extends StateValue
case class FunctionValue(value : StateValue => StateValue) extends StateValue
case class TupleValue(value : Vector[StateValue]) extends StateValue {
	def prepend(x : StateValue) : TupleValue = TupleValue(x +: value)
	def append(x : StateValue) : TupleValue = TupleValue(value :+ x)
	def concat(tuple : TupleValue) : TupleValue = TupleValue(value ++ tuple.value)
}

object State {
	def fromValue(value : StateValue) : State = 
		new State(null, null, Collect.One(Some(value)), false)

	case class StateValueRef(var value : StateValue)

	case class Env(nonlinear : Map[String, StateValue], linear : Map[String, StateValueRef]) {
		def lookup(id : String) : Option[StateValue] = {
			nonlinear.get(id) match {
				case None => 
					linear.get(id) match {
						case Some(r) => Some(r.value)
						case None => None
					}
				case some => some
			}
		}
		def freeze : Env = 
			Env(nonlinear ++ (linear.mapValues(_.value)), Map())
		def bind(id : String, value : StateValue) : Env = 
			Env(nonlinear - id, linear + (id -> StateValueRef(value)))
		def bind(m : Map[String, StateValue]) : Env = 
			Env(nonlinear -- m.keySet, linear ++ m.mapValues(StateValueRef(_)))
		def rebind(id : String, value : StateValue) : Env = {
			linear(id).value = value
			this
		}
		def rebind(m : Map[String, StateValue]) : Env = {
			for ((id, value) <- m) linear(id).value = value
			this
		}
		def linearIds : Set[String] = linear.keySet
	}
}

class State(val context : Context, val env : State.Env, val collect : Collect, val canReturn : Boolean) {

	def lookup(id : String) : Option[StateValue] = env.lookup(id)

	def assignables : Set[String] = env.linearIds

	def bind(vs : Map[String, StateValue]) : State = {
		new State(context, env.bind(vs), collect, canReturn)
	}

	def rebind(vs : Map[String, StateValue]) : State = {
		new State(context, env.rebind(vs), collect, canReturn)
	}

	def setCanReturn(cR : Boolean) : State = {
		new State(context, env, collect, cR)
	}

	def freeze : State = {
		new State(context, env.freeze, collect, false)
	}

	def setContext(ctx : Context) : State = {
		new State(ctx, env, collect, canReturn)
	}

	def setCollect(c : Collect) : State = {
		new State(context, env, c, canReturn)
	}

	def subsume(state : State) : State = {
		new State(state.context, env, state.collect, canReturn)
	} 

	def addToCollect(value : StateValue) : State = {
		collect match {
			case Collect.One(None) =>
				new State(context, env, Collect.One(Some(value)), canReturn)
			case Collect.Multiple(collector) =>
				new State(context, env, Collect.Multiple(collector.add(value)), canReturn)
			case _ => 
				throw new RuntimeException("internal error: wrong collector multiplicty")

		}
	}

	def reapCollect : StateValue = {
		collect match {
			case Collect.One(Some(v)) => v
			case Collect.Multiple(collector) => 
				collector.reap
			case _ =>
				throw new RuntimeException("internal error: wrong collector multiplicity")
		}
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

