package proofpeer.proofscript.naiveinterpreter

import proofpeer.proofscript.logic._
import proofpeer.proofscript.frontend.ParseTree

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

case object NilValue extends StateValue
case class ContextValue(value : Context) extends StateValue 
case class TheoremValue(value : Theorem) extends StateValue
case class TermValue(value : CTerm) extends StateValue
case class BoolValue(value : Boolean) extends StateValue
case class IntValue(value : BigInt) extends StateValue
case class SimpleFunctionValue(state : State, f : ParseTree.Fun) extends StateValue
case class RecursiveFunctionValue(var state : State, val cases : Vector[ParseTree.DefCase]) extends StateValue
case class NativeFunctionValue(nativeFunction : NativeFunctions.F) extends StateValue
case class StringValue(value : Vector[Int]) extends StateValue {
	override def toString : String = {
		new String(value.toArray, 0, value.size)		
	}
	def concat(s : StringValue) : StringValue = StringValue(value ++ s.value)
}
case class TupleValue(value : Vector[StateValue]) extends StateValue {
	def prepend(x : StateValue) : TupleValue = TupleValue(x +: value)
	def append(x : StateValue) : TupleValue = TupleValue(value :+ x)
	def concat(tuple : TupleValue) : TupleValue = TupleValue(value ++ tuple.value)
}

object StateValue {

	def isFunction(v : StateValue) : Boolean = {
		v match {
			case _ : SimpleFunctionValue => true
			case _ : RecursiveFunctionValue => true
			case _ : NativeFunctionValue => true
			case _ => false
		}
	}

	def display(context : Context) : String = {
		context.kind match {
			case ContextKind.Complete => context.namespace.toString
			case _ =>
				var i = 0
				var ctx = context.parentContext
				while (ctx.isDefined) {
					i = i + 1
					ctx = ctx.get.parentContext
				}
				context.namespace.toString + "+" + i
		}
	}

	def display(aliases : Aliases,
							nameresolution : NamespaceResolution[IndexedName], 
							context : Context, 
							tm : Term) : String = 
	{
		try {
			"'" + Syntax.checkprintTerm(aliases, nameresolution, context, tm) + "'"
		} catch {
			case _ : Utils.KernelException => "{error printing} : Theorem"
		}
	}

	def display(aliases : Aliases, nameresolution : NamespaceResolution[IndexedName], 
		context : Context, value : StateValue) : String = 
	{
		value match {
			case NilValue => "nil"
			case BoolValue(value) => if (value) "true" else "false"
			case IntValue(value) => "" + value
			case f : SimpleFunctionValue => "? : Function"
			case f : RecursiveFunctionValue => "? : Function"
			case f : NativeFunctionValue => "? : Function"
			case TupleValue(value) =>
				var error = "["
				var first = true
				for (v <- value) {
					if (first) first = false else error = error + ", "
					error = error + display(aliases, nameresolution, context, v)
				} 
				error + "]"
			case ContextValue(context) => display(context) + " : Context"
			case TheoremValue(th) =>
				try {
					val liftedTh = context.lift(th, false)
					display(aliases, nameresolution, liftedTh.context, liftedTh.proposition) + " : Theorem"
				} catch {
					case _ : Utils.KernelException => 
						"{context = " + display(th.context) + ", theorem = " + 
						display(aliases, nameresolution, th.context, th.proposition) + "} : Theorem"
				}
			case TermValue(ctm) => display(aliases, nameresolution, ctm.context, ctm.term)
			case s : StringValue => "\"" + s + "\""
			case _ => "?@" + value.hashCode
		}
	}
	
}

object State {
	def fromValue(value : StateValue) : State = 
		new State(null, null, null, Collect.One(Some(value)), false)

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
		def lookup(ids : Set[String]) : Either[Map[String, StateValue], Set[String]] = {
			var m : Map[String, StateValue] = Map()
			var not_found : Set[String] = Set()
			for (id <- ids) {
				lookup(id) match {
					case None => not_found = not_found + id
					case Some(v) => m = m + (id -> v)
				}
			}
			if (not_found.isEmpty) Left(m) else Right(not_found)
		}
		def freeze : Env = 
			if (linear.isEmpty) this 
			else Env(nonlinear ++ (linear.mapValues(_.value)), Map())
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

class State(val context : Context, val lexicalContext : Context, val env : State.Env, val collect : Collect, val canReturn : Boolean) {

	def lookup(id : String) : Option[StateValue] = env.lookup(id)

	def assignables : Set[String] = env.linearIds

	def bind(vs : Map[String, StateValue]) : State = {
		new State(context, lexicalContext, env.bind(vs), collect, canReturn)
	}

	def rebind(vs : Map[String, StateValue]) : State = {
		new State(context, lexicalContext, env.rebind(vs), collect, canReturn)
	}

	def setCanReturn(cR : Boolean) : State = {
		new State(context, lexicalContext, env, collect, cR)
	}

	def freeze : State = {
		new State(context, lexicalContext, env.freeze, collect, false)
	}

	def setContext(ctx : Context, l) : State = {
		new State(ctx, env, collect, canReturn)
	}

	def setCollect(c : Collect) : State = {
		new State(context, lexicalContext, env, c, canReturn)
	}

	def subsume(state : State) : State = {
		new State(state.context, state.lexicalContext, env, state.collect, canReturn)
	} 

	def addToCollect(value : StateValue) : State = {
		collect match {
			case Collect.One(None) =>
				new State(context, lexicalContext, env, Collect.One(Some(value)), canReturn)
			case Collect.Multiple(collector) =>
				new State(context, lexicalContext, env, Collect.Multiple(collector.add(value)), canReturn)
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

