package proofpeer.proofscript.naiveinterpreter

import proofpeer.proofscript.frontend._
import proofpeer.proofscript.logic._
import ParseTree._

sealed trait Result[T]
case class Success[T](result : T) extends Result[T]
case class Failed[T](pos : SourcePosition, error : String) extends Result[T]


class Eval(states : States, kernel : Kernel, nameresolution : NameResolution, 
	resolveNamespace : Namespace => Namespace, namespace : Namespace) 
{

	def fail[T](p : ParseTree, error : String) : Failed[T] = Failed(p.sourcePosition, error)

	def evalStatements(_state : State, statements : Vector[Statement], _collect : Collect) : Result[(State, Collect)] = {
		var state = _state
		var collect = _collect
		val num = statements.size
		var i = 0
		for (st <- statements) {
			st match {
				case STVal(pat, body) => 
					//evalBlock(state, )
					return fail(st, "val has not been implemented yet")
				case STReturn(expr) => return fail(st, "return is currently not supported")
				case STShow(expr) => 
					evalExpr(state.freeze, expr) match {
						case Failed(pos, error) => return Failed(pos, error)
						case Success(value) => 
							val location : String = 
								st.sourcePosition.span match {
									case None => ""
									case Some(span) => ", row " + (span.firstRow + 1)
								}
							println("** show (theory "+namespace+location+"): "+value)
					}
				case _ => return fail(st, "statement has not been implemented yet")
			}
			i = i + 1
		}
		Success((state, collect))
	}

	def evalExpr(state : State, expr : Expr) : Result[StateValue] = {
		expr match {
			case Bool(b) => Success(BoolValue(b))
			case Integer(i) => Success(IntValue(i))
			case _ => fail(expr, "don't know how to evaluate this expression")
		}
		
	}



}