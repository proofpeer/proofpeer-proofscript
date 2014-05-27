package proofpeer.proofscript.naiveinterpreter

import proofpeer.proofscript.frontend._
import proofpeer.proofscript.logic._
import ParseTree._

sealed trait Result[T]
case class Success[T](result : T, isReturnValue : Boolean) extends Result[T]
case class Failed[T](pos : SourcePosition, error : String) extends Result[T]

class Eval(states : States, kernel : Kernel, 
	scriptNameresolution : NamespaceResolution[String], logicNameresolution : NamespaceResolution[IndexedName], 
	aliases : Aliases, namespace : Namespace) 
{

	def success[T](result : T) : Success[T] = Success(result, false)

	def fail[T](p : TracksSourcePosition, error : String) : Failed[T] = Failed(p.sourcePosition, error)

	def fail[S,T](f : Failed[S]) : Failed[T] = Failed(f.pos, f.error)

	def evalStatements(_state : State, statements : Vector[Statement]) : Result[State] = {
		var state = _state
		val num = statements.size
		var i = 0
		for (st <- statements) {
			st match {
				case STVal(pat, body) => 
					evalBlock(state.setCollect(Collect.emptyOne), body) match {
						case f : Failed[_] => return fail(f)
						case Success(s, isReturnValue) => 
							if (isReturnValue) return Success(s, isReturnValue)
							val value = s.reapCollect
							state = state.subsume(s, body.introVars, state.collect)
							matchPattern(state.freeze, pat, value) match {
								case Failed(pos, error) => return Failed(pos, error)
								case Success(None, _) => return fail(pat, "value " + value + " does not match pattern")
								case Success(Some(matchings), _) => state = state.add(matchings)
							}
					}
				case STExpr(expr) =>
					val ok =
						state.collect match {
							case Collect.Zero => false
							case c : Collect.One => i == num - 1
							case c : Collect.Multiple => true
						}
					if (!ok) return fail(st, "cannot yield here")
					evalExpr(state.freeze, expr) match {
						case f : Failed[_] => return fail(f)
						case Success(s, _) => state = state.addToCollect(s)
					}
				case STReturn(expr) => 
					if (!state.canReturn) return fail(st, "cannot return here")
					evalExpr(state.freeze, expr) match {
						case f : Failed[_] => return fail(f)
						case Success(s, _) => return Success(State.fromValue(s), true)
					}
				case STShow(expr) => 
					evalExpr(state.freeze, expr) match {
						case f : Failed[_] => return fail(f)
						case Success(value, _) => 
							val location : String = 
								st.sourcePosition.span match {
									case None => ""
									case Some(span) => ":" + (span.firstRow + 1)
								}
							println("** show ("+namespace+location+"): "+value)
					}
				case STFail(None) => return fail(st, "fail")
				case STFail(Some(expr)) =>
					evalExpr(state.freeze, expr) match {
						case f : Failed[_] => return fail(f)
						case Success(value, _) => return fail(st, "fail: "+value)
					}				
				case _ => return fail(st, "statement has not been implemented yet: "+st)
			}
			i = i + 1
		}
		success(state)
	}

	def evalBlock(state : State, block : Block) : Result[State] = {
		evalStatements(state, block.statements)
	}

	def evalExpr(state : State, expr : Expr) : Result[StateValue] = {
		def lookup(full : Boolean, namespace : Namespace, name : String) : Result[StateValue] = {
			val r = 
				if (full) 
					scriptNameresolution.fullResolution(namespace) 
				else 
					scriptNameresolution.baseResolution(namespace)
			r.get(name) match {
				case None => fail(expr, "unknown identifier")
				case Some(namespaces) =>
					namespaces.size match {
						case 0 => fail(expr, "unknown identifier")
						case 1 => 
							val ns = namespaces.head
							success(states.lookup(ns).get.lookup(name).get)
						case n =>
							var display = ""
							for (ns <- namespaces) display = display + ns + " "
							fail(expr, "ambiguous identifier " + name + ", defined in "+n+" different namespaces: "+display)
					}
			}
		}
		expr match {
			case Bool(b) => success(BoolValue(b))
			case Integer(i) => success(IntValue(i))
			case Id(name) =>
				state.lookup(name) match {
					case None => lookup(false, namespace, name)
					case Some(v) => success(v)
				}
			case QualifiedId(_ns, name) =>
				val ns = aliases.resolve(_ns)
				if (scriptNameresolution.ancestorNamespaces(namespace).contains(ns))
					lookup(true, ns, name)
				else 
					fail(expr, "unknown or inaccessible namespace: "+ns)
			case UnaryOperation(op, expr) =>
				evalExpr(state, expr) match {
					case Success(value, _) =>
						(op, value) match {
							case (Not, BoolValue(b)) => success(BoolValue(!b)) 
							case (Neg, IntValue(i)) => success(IntValue(-i))
							case _ => fail(op, "unary operator "+op+" cannot be applied to: "+value)
						}
					case f => f
				}
			case BinaryOperation(op, left, right) =>
				evalExpr(state, left) match {
					case Success(left, _) =>
						evalExpr(state, right) match {
							case Success(right, _) =>
								(op, left, right) match {
									case (Add, IntValue(x), IntValue(y)) => success(IntValue(x + y))
									case (Sub, IntValue(x), IntValue(y)) => success(IntValue(x - y))
									case _ => fail(op, "binary operator "+op+" cannot be applied to values: "+left+", "+right)
								}
							case f => f
						}
					case f => f
				}
			case _ => fail(expr, "don't know how to evaluate this expression")
		}	
	}

	type Matchings = Map[String, StateValue]

	def matchPattern(state : State, pat : Pattern, value : StateValue) : Result[Option[Matchings]] = {
		matchPattern(state, pat, value, Map())
	}

	def matchPattern(state : State, pat : Pattern, value : StateValue, matchings : Matchings) : Result[Option[Matchings]] = {
		pat match {
			case PAny => success(Some(matchings))
			case PId(name) => 
				matchings.get(name) match {
					case None => success(Some(matchings + (name -> value)))
					case Some(v) => fail(pat, "pattern is not linear")
				}
			case _ => return fail(pat, "pattern has not been implemented yet")
		}		
	}

}