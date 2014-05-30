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

	sealed trait CmpResult
	case object IsLess extends CmpResult
	case object IsLessOrEqual extends CmpResult
	case object IsEq extends CmpResult
	case object IsGreater extends CmpResult
	case object IsGreaterOrEqual extends CmpResult
	case object IsNEq extends CmpResult

	def cmp(x : StateValue, y : StateValue) : Option[CmpResult] = {
		(x, y) match {
			case (IntValue(x), IntValue(y)) => 
				if (x < y) Some(IsLess) 
				else if (x > y) Some(IsGreater)
				else Some(IsEq)
			case (BoolValue(x), BoolValue(y)) =>
				if (x == y) Some(IsEq) else Some(IsNEq)
			case (TupleValue(xs), TupleValue(ys)) =>
				val len = xs.size
				if (len == ys.size) {
					var has_less = false
					var has_eq = false
					var has_greater = false
					var has_neq = false
					for (i <- 0 until len)
						cmp(xs(i), ys(i)) match {
							case None => return None
							case Some(c) =>
								c match {
									case IsLess => has_less = true
									case IsLessOrEqual =>
										has_less = true
										has_eq = true 
									case IsEq => has_eq = true
									case IsGreater => has_greater = true
									case IsGreaterOrEqual => 
										has_greater = true
										has_eq = true
									case IsNEq => has_neq = true
								}
						}
					if (has_neq) Some(IsNEq)
					else
						(has_less, has_eq, has_greater) match {
							case (true, false, false) => Some(IsLess)
							case (true, true, false) => Some(IsLessOrEqual)
							case (false, _, false) => Some(IsEq)
							case (false, false, true) => Some(IsGreater)
							case (false, true, true) => Some(IsGreaterOrEqual)
							case (true, _, true) => Some(IsNEq)
						}
				} else None
			case _ => None
		}
	}

	def cmp(op : CmpOperator, x : StateValue, y : StateValue) : Result[Boolean] = {
		cmp (x, y) match {
			case None => fail(op, "values cannot be compared: " + x + ", " + y)
			case Some(c) =>
				success(
					op match {
						case Eq => c == IsEq
						case NEq => c != IsEq 
						case Le => c == IsLess
						case Leq => c == IsLess || c == IsEq || c == IsLessOrEqual
						case Gr => c == IsGreater
						case Geq => c == IsGreater || c == IsEq || c == IsGreaterOrEqual
					})
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
			case BinaryOperation(op, left, right) if op != And && op != Or =>
				evalExpr(state, left) match {
					case Success(left, _) =>
						evalExpr(state, right) match {
							case Success(right, _) =>
								(op, left, right) match {
									case (Add, IntValue(x), IntValue(y)) => success(IntValue(x + y))
									case (Sub, IntValue(x), IntValue(y)) => success(IntValue(x - y))
									case (Mul, IntValue(x), IntValue(y)) => success(IntValue(x * y))
									case (Div, IntValue(x), IntValue(y)) => 
										if (y == 0)
											fail(op, "division by zero")
										else
											success(IntValue(x / y)) 
									case (Mod, IntValue(x), IntValue(y)) =>
										if (y == 0)
											fail(op, "modulo zero")
										else
											success(IntValue(x % y))
									case (And, BoolValue(x), BoolValue(y)) => success(BoolValue(x && y))
									case (Or, BoolValue(x), BoolValue(y)) => success(BoolValue(x || y))
									case (Prepend, x, xs : TupleValue) => success(xs.prepend(x))
									case (Append, xs : TupleValue, x) => success(xs.append(x))
									case (Concat, xs : TupleValue, ys : TupleValue) => success(xs.concat(ys))
									case _ => fail(op, "binary operator "+op+" cannot be applied to values: "+left+", "+right)
								}
							case f => f
						}
					case f => f
				}
			case BinaryOperation(And, left, right) =>
				evalExpr(state, left) match {
					case Success(v @ BoolValue(false), _) => success(v)
					case Success(BoolValue(true), _) => 
						evalExpr(state, right) match {
							case su @ Success(_ : BoolValue, _) => su
							case Success(v, _) => fail(right, "Boolean expected, found: " + v)
							case f => f
						}
					case Success(v, _) => fail(left, "Boolean expected, found: " + v)
					case f => f
				}
			case BinaryOperation(Or, left, right) =>
				evalExpr(state, right) match {
					case Success(v @ BoolValue(true), _) => success(v)
					case Success(BoolValue(false), _) => 
						evalExpr(state, right) match {
							case su @ Success(_ : BoolValue, _) => su
							case Success(v, _) => fail(right, "Boolean expected, found: " + v)
							case f => f
						}					
					case Success(v, _) => fail(left, "Boolean expected, found: " + v)
					case f => f
				}
			case CmpOperation(_operators, _operands) => 
				evalExpr(state, _operands.head) match {
					case f : Failed[_] => f
					case Success(v, _) =>
						var value = v
						var operators = _operators
						var operands = _operands.tail
						while (!operators.isEmpty) {
							evalExpr(state, operands.head) match {
								case f : Failed[_] => return f
								case Success(v, _) =>
									cmp(operators.head, value, v) match {
										case f : Failed[_] => return Failed(f.pos, f.error)
										case Success(false, _) => return success(BoolValue(false))
										case Success(true, _) => value = v
									}
							} 
							operands = operands.tail
							operators = operators.tail
						}
						success(BoolValue(true))
				} 
			case Tuple(xs) =>
				var values : List[StateValue] = List()
				for (x <- xs) {
					evalExpr(state, x) match {
						case f : Failed[_] => return f
						case Success(value, _) => values = value :: values
					}
				}
				success(TupleValue(values.reverse.toVector))
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

	def evalControlFlowSwitch(state : State, controlflow : ControlFlow) : Result[State] = {
		controlflow match {
			case c : Do => evalDo(state, c)
			case c : If => evalIf(state, c)
			case c : While => evalWhile(state, c)
			case c : For => evalFor(state, c)
			case c : Match => evalMatch(state, c)
			case _ => fail(controlflow, "controlflow not implemented yet: "+controlflow)
		}
	}

	def evalDo(state : State, control : Do) : Result[State] = {
		evalSubBlock(state, control.block)
	}

	def evalIf(state : State, control : If) : Result[State] = {
		evalExpr(state.freeze, control.cond) match {
			case f : Failed[_] => fail(f)
			case Success(BoolValue(test), _) =>
				if (test) 
					evalSubBlock(state, control.thenCase) 
				else 
					evalSubBlock(state, control.elseCase)
			case Success(value, _) => fail(control.cond, "Boolean expected, found: " + value)
		}	
	}

	def evalWhile(_state : State, control : While) : Result[State] = {
		var repeat : Boolean = true
		var state = _state
		while (repeat) {
			evalExpr(state.freeze, control.cond) match {
				case f : Failed[_] => return fail(f)
				case Success(BoolValue(false), _) => repeat = false
				case Success(BoolValue(true), _) => 
					evalSubBlock(state, control.body) match {
						case f : Failed[_] => return f
						case su @ Success(s, isReturnValue) =>
							if (isReturnValue) return su
							state = state.subsume(s)
					}

			}
		}
		success(state)
	}

	def evalFor(_state : State, control : For) : Result[State] = {
		evalExpr(_state.freeze, control.coll) match {
			case f : Failed[_] => fail(f)
			case Success(TupleValue(values), _) =>
				var state = _state
				for (value <- values) {
					matchPattern(state.freeze, control.pat, value) match {
						case f : Failed[_] => return fail(f)
						case Success(None, _) => 
						case Success(Some(matchings), _) =>
							evalSubBlock(state.bind(matchings), control.body) match {
								case f : Failed[_] => return f
								case su @ Success(s, isReturnValue) =>
									if (isReturnValue) return su
									state = state.subsume(s)
							}
					}
				}
				success(state)
			case Success(v, _) => fail(control.coll, "tuple expected, found: " + v)
		}
	}

	def evalMatch(state : State, control : Match) : Result[State] = {
		val frozenState = state.freeze
		evalExpr(frozenState, control.expr) match {
			case f : Failed[_] => fail(f)
			case Success(value, _) =>
				for (matchCase <- control.cases) {
					matchPattern(frozenState, matchCase.pat, value) match {
						case f : Failed[_] => return fail(f)
						case Success(None, _) => 
						case Success(Some(matchings), _) =>
							evalSubBlock(state.bind(matchings), matchCase.body) match {
								case f : Failed[_] => return fail(f)
								case su @ Success(s, isReturnValue) =>
									if (isReturnValue) return su
									else return success(state.subsume(s))
							}
					}	
				}
				fail(control, "no match for value: " + value)
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
			case PInt(x) =>
				value match {
					case IntValue(y) if x == y => success(Some(matchings))
					case _ => success(None)
				}
			case PBool(x) =>
				value match {
					case BoolValue(y) if x == y => success(Some(matchings))
					case _ => success(None)
				}
			case PTuple(ps) =>
				value match {
					case TupleValue(xs) if xs.size == ps.size =>
						var m = matchings
						for (i <- 0 until xs.size) {
							matchPattern(state, ps(i), xs(i), m) match {
								case Success(Some(matchings_i), _) => m = matchings_i
								case r => return r
							}
						}
						success(Some(m)) 
					case _ => success(None)
				}
			case PPrepend(p, ps) =>
				value match {
					case TupleValue(xs) if !xs.isEmpty =>
						matchPattern(state, p, xs.head, matchings) match {
							case Success(Some(matchings), _) => 
								matchPattern(state, ps, TupleValue(xs.tail), matchings) 
							case r => r
						}
					case _ => success(None)
				}
			case PAppend(ps, p) =>
				value match {
					case TupleValue(xs) if !xs.isEmpty =>
						matchPattern(state, p, xs.last, matchings) match {
							case Success(Some(matchings), _) => 
								matchPattern(state, ps, TupleValue(xs.take(xs.size - 1)), matchings) 
							case r => r
						}
					case _ => success(None)
				}				
			case _ => return fail(pat, "pattern has not been implemented yet")
		}		
	}

}