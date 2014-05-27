package proofpeer.proofscript.naiveinterpreter

import proofpeer.proofscript.frontend._
import proofpeer.proofscript.logic._
import ParseTree._

sealed trait Result[T]
case class Success[T](result : T) extends Result[T]
case class Failed[T](pos : SourcePosition, error : String) extends Result[T]


class Eval(states : States, kernel : Kernel, nameresolution : NamespaceResolution[IndexedName], 
	aliases : Aliases, namespace : Namespace) 
{

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
						case Success(s) => 
							val value = s.reapCollect
							state = state.subsume(s, body.introVars, state.collect)
							matchPattern(state.freeze, pat, value) match {
								case Failed(pos, error) => return Failed(pos, error)
								case Success(None) => return fail(pat, "value " + value + " does not match pattern")
								case Success(Some(matchings)) => state = state.add(matchings)
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
						case Success(s) => state = state.addToCollect(s)
					}
				case STReturn(expr) => return fail(st, "return is currently not supported")
				case STShow(expr) => 
					evalExpr(state.freeze, expr) match {
						case Failed(pos, error) => return Failed(pos, error)
						case Success(value) => 
							val location : String = 
								st.sourcePosition.span match {
									case None => ""
									case Some(span) => ":" + (span.firstRow + 1)
								}
							println("** show ("+namespace+location+"): "+value)
					}
				case _ => return fail(st, "statement has not been implemented yet: "+st)
			}
			i = i + 1
		}
		Success(state)
	}

	def evalBlock(state : State, block : Block) : Result[State] = {
		evalStatements(state, block.statements)
	}

	def evalExpr(state : State, expr : Expr) : Result[StateValue] = {
		expr match {
			case Bool(b) => Success(BoolValue(b))
			case Integer(i) => Success(IntValue(i))
			case Id(name) =>
				state.lookup(name) match {
					case None => fail(expr, "unknown identifier")
					case Some(v) => Success(v)
				}
			case QualifiedId(_ns, name) =>
				val ns = aliases.resolve(_ns)
				states.lookup(ns) match {
					case None => fail(expr, "no such namespace: "+ns)
					case Some(state) =>
						state.lookup(name) match {
							case None => fail(expr, "identifier does not exist in namespace")
							case Some(v) => Success(v)
						} 
				}
			case UnaryOperation(op, expr) =>
				evalExpr(state, expr) match {
					case Success(value) =>
						(op, value) match {
							case (Not, BoolValue(b)) => Success(BoolValue(!b)) 
							case (Neg, IntValue(i)) => Success(IntValue(-i))
							case _ => fail(op, "unary operator "+op+" cannot be applied to: "+value)
						}
					case f => f
				}
			case BinaryOperation(op, left, right) =>
				evalExpr(state, left) match {
					case Success(left) =>
						evalExpr(state, right) match {
							case Success(right) =>
								(op, left, right) match {
									case (Add, IntValue(x), IntValue(y)) => Success(IntValue(x + y))
									case (Sub, IntValue(x), IntValue(y)) => Success(IntValue(x - y))
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
			case PAny => Success(Some(matchings))
			case PId(name) => 
				matchings.get(name) match {
					case None => Success(Some(matchings + (name -> value)))
					case Some(v) => fail(pat, "pattern is not linear")
				}
			case _ => return fail(pat, "pattern has not been implemented yet")
		}		
	}

}