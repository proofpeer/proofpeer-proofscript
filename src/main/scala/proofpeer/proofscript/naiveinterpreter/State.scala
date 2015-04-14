package proofpeer.proofscript.naiveinterpreter

import proofpeer.proofscript.logic._
import proofpeer.proofscript.frontend.ParseTree
import proofpeer.proofscript.serialization.UniquelyIdentifiable
import proofpeer.general.StringUtils

trait StateValue extends UniquelyIdentifiable {
	def isComparable : Boolean
}

sealed trait Collect {}
object Collect {
	case object Zero extends Collect
	case class One(collected : Option[StateValue]) extends Collect
	case class Multiple(collector : Collector) extends Collect 

	sealed trait Collector {
		def add(value : StateValue) : Collector 
		def reap : StateValue
	}

	private class TupleCollector(val collected : List[StateValue]) extends Collector {
		def add(value : StateValue) = new TupleCollector(value :: collected)
		def reap : StateValue = {
			val values = collected.reverse.toVector
			TupleValue(values, values.forall(_.isComparable))
		}
	}

	private val emptyTupleCollector = new TupleCollector(List())

	def emptyMultiple : Multiple = Multiple(emptyTupleCollector)

	def emptyOne : One = One(None)

	import proofpeer.general._

	final class CollectorSerializer(StateValueSerializer : Serializer[StateValue]) 
	extends TransformSerializer[Collector, List[StateValue]](
		ListSerializer(StateValueSerializer),
		(collector : Collector) => collector.asInstanceOf[TupleCollector].collected,
		(stateValues : List[StateValue]) => new TupleCollector(stateValues)
	)
	
}

case object NilValue extends StateValue {
	def isComparable = true
}
case class ContextValue(value : Context) extends StateValue {
	def isComparable = false
}
case class TheoremValue(value : Theorem) extends StateValue {
	def isComparable = false
}
case class TermValue(value : Term) extends StateValue {
	def isComparable = true
}
case class TypeValue(value : Type) extends StateValue {
	def isComparable = true
}
case class BoolValue(value : Boolean) extends StateValue {
	def isComparable = true
}
case class IntValue(value : BigInt) extends StateValue {
	def isComparable = true
}
case class SimpleFunctionValue(state : State, f : ParseTree.Fun) extends StateValue {
	def isComparable = false
}
case class RecursiveFunctionValue(var state : State, var cases : Vector[ParseTree.DefCase], var cache : Map[StateValue, StateValue], var context : Option[Context]) extends StateValue {
	def isComparable = false	
}
case class NativeFunctionValue(nativeFunction : NativeFunctions.F) extends StateValue {
	def isComparable = false	
}
case class StringValue(value : Vector[Int]) extends StateValue {
	override def toString : String = {
		new String(value.toArray, 0, value.size)		
	}
	def concat(s : StringValue) : StringValue = StringValue(value ++ s.value)
	def isComparable = true
}
case class TupleValue(value : Vector[StateValue], comparable : Boolean) extends StateValue {
	def prepend(x : StateValue) : TupleValue = TupleValue(x +: value, comparable && x.isComparable) 
	def append(x : StateValue) : TupleValue = TupleValue(value :+ x, comparable && x.isComparable)
	def concat(tuple : TupleValue) : TupleValue = TupleValue(value ++ tuple.value, comparable && tuple.isComparable)
	def isComparable = comparable
}
case class SetValue(value : Set[StateValue]) extends StateValue {
	def isComparable = true
	def concat(set : SetValue) : SetValue = SetValue(value ++ set.value)
	def minus(set : SetValue) : SetValue = SetValue(value -- set.value)
}
case class MapValue(value : Map[StateValue, StateValue], comparable : Boolean) extends StateValue {
	def isComparable = comparable
	def concat(m : MapValue) : MapValue = {
		val r = value ++ m.value
		if (comparable && m.comparable)
			MapValue(r, true)
		else if (!m.comparable)
			MapValue(r, false)
		else {
			MapValue(r, r.values.forall(v => v.isComparable))
		}
	}
	def minus(set : SetValue) : MapValue = {
		val r = value -- set.value
		if (comparable)
			MapValue(r, true)
		else 
			MapValue(r, r.values.forall(v => v.isComparable))
	}
}

object StateValue {

	def mkStringValue(s : String) : StringValue = StringValue(StringUtils.codePoints(s))

	def isFunction(v : StateValue) : Boolean = {
		v match {
			case _ : SimpleFunctionValue => true
			case _ : RecursiveFunctionValue => true
			case _ : NativeFunctionValue => true
			case _ => false
		}
	}

	def isTheoremValue(v : StateValue) : Boolean = {
		v match {
			case _ : TheoremValue => true
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

	private def display(aliases : Aliases,
							nameresolution : NamespaceResolution[IndexedName], 
							context : Context, 
							tm : Term) : String = 
	{
		"'" + Syntax.checkprintTerm(aliases, nameresolution, context, tm) + "'"
	}

	private def displayRaw(tm : Term) : String = {
		Syntax.printTerm(Preterm.unknownResolution, tm)
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
			case TupleValue(value, _) =>
				var s = "["
				var first = true
				for (v <- value) {
					if (first) first = false else s = s + ", "
					s = s + display(aliases, nameresolution, context, v)
				} 
				s + "]"
			case SetValue(value) =>
				var s = "{"
				var first = true
				for (v <- value) {
					if (first) first = false else s = s + ", "
					s = s + display(aliases, nameresolution, context, v)
				} 
				s + "}"
			case MapValue(value, _) =>
				var s = "{"
				var first = true
				for ((k, v) <- value) {
					if (first) first = false else s = s + ", "
					val sk = display(aliases, nameresolution, context, k)
					val sv = display(aliases, nameresolution, context, v)
					s = s + sk + " → " + sv
				} 
				if (first) "{→}" else s + "}"			
			case ContextValue(context) => display(context) + " : Context"
			case TheoremValue(th) =>
				try {
					val liftedTh = context.lift(th)
					display(aliases, nameresolution, liftedTh.context, liftedTh.proposition) + " : Theorem"
				} catch {
					case _ : Utils.KernelException => 
						"{invalid in current context, context = " + display(th.context) + ", theorem = " + 
						display(aliases, nameresolution, th.context, th.proposition) + "} : Theorem"
				}
			case TermValue(tm) => 
				try {
					display(aliases, nameresolution, context, tm)
				} catch {
					case _ : Utils.KernelException =>
						"{invalid in current context, raw term is: '" + displayRaw(tm) + "'} : Term"
				}
			case TypeValue(ty) =>
				"': " + Syntax.printType(ty) + "'"
			case s : StringValue => "\"" + s + "\""
			case _ => "?@" + value.hashCode
		}
	}
	
}

object State {
	def fromValue(value : StateValue) : State = 
		new State(null, null, Collect.One(Some(value)), false)

	case class StateValueRef(var value : StateValue)

	case class Env(nonlinear : Map[String, StateValue], linear : Map[String, StateValueRef]) extends UniquelyIdentifiable {
		def size = nonlinear.size + linear.size
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

class State(val context : Context, val env : State.Env, val collect : Collect, val canReturn : Boolean) extends UniquelyIdentifiable {

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
