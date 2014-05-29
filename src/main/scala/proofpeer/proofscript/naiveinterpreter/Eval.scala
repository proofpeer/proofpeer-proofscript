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

	def evalBlock(_state : State, block : Block) : Result[State] = {
		val statements = block.statements
		var state = _state
		val num = statements.size
		var i = 0
		for (st <- statements) {
			st match {
				case STVal(pat, body) => 
					evalBlock(state.setCollect(Collect.emptyOne), body) match {
						case f : Failed[_] => return fail(f)
						case su @ Success(s, isReturnValue) => 
							if (isReturnValue) return su
							val value = s.reapCollect
							state = state.setContext(s.context)
							matchPattern(state.freeze, pat, value) match {
								case Failed(pos, error) => return Failed(pos, error)
								case Success(None, _) => return fail(pat, "value " + value + " does not match pattern")
								case Success(Some(matchings), _) => state = state.bind(matchings)
							}
					}
				case STAssign(pat, body) =>
					if (!(pat.introVars subsetOf state.assignables)) {
						val unassignables = pat.introVars -- state.assignables
						var error = "pattern assigns to variables not in linear scope:"
						for (v <- unassignables) error = error + " " + v
						return fail(pat, error)
					}
					evalBlock(state.setCollect(Collect.emptyOne), body) match {
						case f : Failed[_] => return fail(f)
						case su @ Success(s, isReturnValue) => 
							if (isReturnValue) return su
							val value = s.reapCollect
							state = state.setContext(s.context)
							matchPattern(state.freeze, pat, value) match {
								case Failed(pos, error) => return Failed(pos, error)
								case Success(None, _) => return fail(pat, "value " + value + " does not match pattern")
								case Success(Some(matchings), _) => state = state.rebind(matchings)
							}
					}					
				case STExpr(expr) =>
					val ok =
						state.collect match {
							case Collect.Zero => false
							case _ : Collect.One => i == num - 1
							case _ : Collect.Multiple => true
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
				case STControlFlow(controlflow) =>
					val (changedCollect, collect) = 
						state.collect match {
							case _ : Collect.One if i != num - 1 => (true, Collect.Zero)
							case c => (false, c)
						}
					evalControlFlow(state.setCollect(collect), controlflow) match {
						case f : Failed[_] => return fail(f)
						case su @ Success(value, isReturnValue) =>
							if (isReturnValue) return su
							state = if (changedCollect) value.setCollect(state.collect) else value
					}
				case _ => return fail(st, "statement has not been implemented yet: "+st)
			}
			i = i + 1
		}
		state.collect match {
			case Collect.One(None) => fail(block, "block does not yield a value") 
			case _ => success(state)
		}
	}

	def evalSubBlock(state : State, block : Block) : Result[State] = {
		evalBlock(state, block) match {
			case f : Failed[_] => f
			case su @ Success(updatedState, isReturnValue) =>
				if (isReturnValue) su
				else success(state.subsume(updatedState))
		}
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
			case ControlFlowExpr(controlflow) =>
				val cstate = state.setCollect(Collect.emptyOne)
				evalControlFlow(cstate, controlflow) match {
					case f : Failed[_] => return fail(f)
					case Success(state, _) => success(state.reapCollect)
				} 
			case _ => fail(expr, "don't know how to evaluate this expression")
		}	
	}

	def producesMultiple(controlflow : ControlFlow) : Boolean = {
		controlflow match {
			case Do(_, true) => true
			case _ : While => true
			case _ : For => true
			case _ => false
		}
	}

	def evalControlFlow(state : State, controlflow : ControlFlow) : Result[State] = {
		val wrapMultiple =
			state.collect match {
				case _ : Collect.One => producesMultiple(controlflow)
				case _ => false
			}	
		if (wrapMultiple) {
			evalControlFlowSwitch(state.setCollect(Collect.emptyMultiple), controlflow) match {
				case f : Failed[_] => f
				case su @ Success(state, isReturnValue) =>
					if (isReturnValue) su
					else success(state.setCollect(Collect.One(Some(state.reapCollect))))
			}
		} else 
			evalControlFlowSwitch(state, controlflow)
	}

	def evalDo(state : State, control : Do) : Result[State] = {
		evalSubBlock(state, control.block)
	}

	def evalControlFlowSwitch(state : State, controlflow : ControlFlow) : Result[State] = {
		controlflow match {
			case c : Do => evalDo(state, c)
			case _ => fail(controlflow, "controlflow not implemented yet: "+controlflow)
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