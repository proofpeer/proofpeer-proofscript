package proofpeer.proofscript.naiveinterpreter

import proofpeer.proofscript.frontend._
import proofpeer.proofscript.logic._
import proofpeer.indent.Span
import ParseTree._

sealed trait SourceLabel
case object NoSourceLabel extends SourceLabel
case class AnonymousFunctionLabel(displayedValue : String) extends SourceLabel {
	override def toString : String = 
		"? applied to: " + displayedValue
}
case class DefFunctionLabel(name : String, displayedValue : String) extends SourceLabel {
	override def toString : String = 
		name + " applied to: " + displayedValue
}
object FunctionLabel {
	def apply(eval : Eval, state : State, value : StateValue) : AnonymousFunctionLabel = 
		AnonymousFunctionLabel(eval.display(state, value))
	def apply(name : String, eval : Eval, state : State, value : StateValue) : DefFunctionLabel =
		DefFunctionLabel(name, eval.display(state, value))
}

sealed trait Result[T]
case class Success[T](result : T, isReturnValue : Boolean) extends Result[T]
case class Failed[T](var trace : List[(SourcePosition, SourceLabel)], error : String) extends Result[T] {
	def addToTrace(p : SourcePosition, label : SourceLabel) : Failed[T] = {
		if (p != null) {
			trace match {
				case (q,_) :: tr =>
					if (q.source != p.source || q.span != p.span)
						trace = (p, label) :: trace
				case _ => 
					trace = List((p, label))
			}
		}
		this
	}
	def addToTrace(p : TracksSourcePosition, label : SourceLabel) : Failed[T] = {
		if (p != null) addToTrace(p.sourcePosition, label)
		this
	}
}

class Eval(completedStates : Namespace => Option[State], kernel : Kernel, 
	scriptNameresolution : NamespaceResolution[String], 
	val logicNameresolution : NamespaceResolution[IndexedName], 
	val aliases : Aliases, namespace : Namespace, output : Output) 
{

	import proofpeer.general.continuation._

	type RC[S, T] = Continuation[Result[S], T]

	def mkRC[S, T](f : Result[S] => Thunk[T]) : RC[S, T] = f

	private var evalDepths : Array[Int] = new Array[Int](128)
	private var evalDepthsPtr : Int = -1

	private def pushEvalDepth() {
		evalDepthsPtr += 1
		if (evalDepthsPtr >= evalDepths.length) {
			val depths : Array[Int] = new Array[Int](evalDepths.length * 2)
			for (i <- 0 until evalDepths.length) depths(i) = evalDepths(i)
			evalDepths = depths
		}
		evalDepths(evalDepthsPtr) = 0
	}

	private def popEvalDepth() {
		evalDepthsPtr -= 1
	}

	private def incEvalDepth() : Boolean = {
		evalDepths(evalDepthsPtr) = evalDepths(evalDepthsPtr) + 1
		evalDepths(evalDepthsPtr) > 100
	}

	private def decEvalDepth() {
		evalDepths(evalDepthsPtr) = evalDepths(evalDepthsPtr) - 1
	}

	def success[T](result : T) : Success[T] = Success(result, false)

	def fail[T](p : TracksSourcePosition, error : String) : Failed[T] = 
		if (p != null)
			Failed(List((p.sourcePosition, NoSourceLabel)), error)
		else
			Failed(List(), error)

	def fail[S,T](f : Failed[S]) : Failed[T] = Failed(f.trace, f.error)

	def evalLogicPreterm[T](_state : State, tm : LogicTerm, createFresh : Boolean, 
		cont : RC[(Preterm, State), T]) : Thunk[T] = 
	{
		var state = _state
		def inst(tm : Preterm.PTmQuote, cont : Continuation[Either[Preterm, Failed[StateValue]], T]) : Thunk[T] = 
		{
			tm.quoted match {
				case expr : Expr =>
					evalExpr[T](state.freeze, expr, {
						case failed : Failed[_] => 
							expr match {
								case Id(name) if createFresh =>
									Syntax.parsePreterm(name) match {
					          case Some(Preterm.PTmName(Name(None, indexedName), _)) =>
					            val freshName = state.context.mkFresh(indexedName)
					            val codePoints = proofpeer.general.StringUtils.codePoints(freshName.toString)
					            state = state.bind(Map(name -> StringValue(codePoints)))
					            cont(Left(Preterm.PTmName(Name(None, freshName), Pretype.PTyAny)))
					          case _ => cont(Right(failed))      										
									}
								case _ => cont(Right(failed))
							}
						case Success(TermValue(t), _) => cont(Left(Preterm.translate(t)))
						case Success(s : StringValue, _) =>
							Syntax.parsePreterm(s.toString) match {
								case None => cont(Right(fail(expr, "parse error")))
								case Some(preterm) => cont(Left(preterm))
							}
						case Success(v, _) => cont(Right(fail(expr, "term value expected, found: " + display(state, v))))
					})    	
			}
		}
		Preterm.instQuotes[Failed[StateValue], T](inst, tm.tm, {
		  case Right(f) => cont(fail(f))
			case Left(preterm) => cont(success((preterm, state)))
		})
	}

	def resolvePreterm(context : Context, preterm : Preterm) : Result[Term] = {
		val typingContext = Preterm.obtainTypingContext(aliases, logicNameresolution, context)
		Preterm.inferTerm(typingContext, preterm) match {
			case Left(tm) => success(tm)
			case Right(errors) => 
				var error = "term is not valid in current context:"
				for (e <- errors) error = error + "\n  " + e.reason
				Failed(null, error)
		}		
	}

	def evalLogicTerm[T](state : State, tm : LogicTerm, cont : RC[Term, T]) : Thunk[T] = {
		evalLogicPreterm[T](state, tm, false, {
			case failed : Failed[_] => cont(fail(failed))
			case Success((preterm, _), _) => cont(resolvePreterm(state.context, preterm))
		})
	} 

	def evalTermExpr[T](state : State, expr : Expr, cont : RC[Term, T]) : Thunk[T] = {
		evalExpr[T](state, expr, {
			case failed : Failed[_] => cont(fail(failed))
			case Success(TermValue(tm),_) => cont(success(tm))
			case Success(s : StringValue, _) =>
				cont(
					try {
						success(Syntax.parseTerm(aliases, logicNameresolution, state.context, s.toString)) 
					} catch {
						case ex : Utils.KernelException =>
							fail(expr, "parse error: " + ex.reason)	
					})
			case Success(v, _) => cont(fail(expr, "Term expected, found: "+display(state, v)))
		})
	}

	// Note that state is not frozen!!
	def evalPretermExpr[T](state : State, expr : Expr, cont : RC[(Preterm, State), T]) : Thunk[T] = {
		expr match {
			case tm : LogicTerm => 
			  // Instead of evalLogicPreterm(state, tm, true), because of 
			  // issue #31 temporarily remove quote intro feature from language:
				evalLogicPreterm[T](state, tm, false, cont)
			case _ => 
				evalExpr[T](state.freeze, expr, {
					case failed : Failed[_] => cont(fail(failed))
					case Success(TermValue(tm),_) => cont(success((Preterm.translate(tm), state)))
					case Success(s : StringValue, _) =>
						Syntax.parsePreterm(s.toString) match {
							case None => cont(fail(expr, "parse error"))
							case Some(preterm) => cont(success((preterm, state)))
						}
					case Success(v, _) => cont(fail(expr, "Preterm expected, found: "+display(state, v)))
				})
		}
	}

	def display(state : State, value : StateValue) : String = {
		StateValue.display(aliases, logicNameresolution, state.context, value)	
	}

	def recordTraceCont[T](tracks : TracksSourcePosition, cont : RC[State, T]) : RC[State, T] = { 
		case f : Failed[_] => cont(f.addToTrace(tracks, NoSourceLabel))
		case r => cont(r)
	}

	def protectOverflowCont[S, T](cont : Continuation[S, T]) : Continuation[S, T] = (s : S) =>
		try {
			if (incEvalDepth()) Thunk.computation[T](() => cont(s))
			else cont(s)
		} finally {
			decEvalDepth()
		}

	def evalStatement[T](state : State, st : Statement, isLastStatement : Boolean, _cont : RC[State, T]) : Thunk[T] = 
	{
		try {
			if (incEvalDepth()) return Thunk.computation[T](() => evalStatement[T](state, st, isLastStatement, _cont))

			val cont : RC[State, T] = protectOverflowCont(recordTraceCont(st, _cont))
			st match {
				case STValIntro(ids) =>
					if (ids.toSet.size != ids.size)
						cont(fail(st, "cannot introduce the same variable more than once"))
					else {
						var _state = state
						for (id <- ids) _state = _state.bind(Map(id.name -> NilValue))
						cont(success(_state))
					}
				case STVal(pat, body) => 
					evalBlock[T](state.setCollect(Collect.emptyOne), body, {
						case f : Failed[_] => cont(fail(f))
						case su @ Success(s, isReturnValue) => 
							if (isReturnValue) cont(su)
							else {
								val value = s.reapCollect
								val _state = state.setContext(s.context)
								matchPattern(_state.freeze, pat, value) match {
									case Failed(pos, error) => cont(Failed(pos, error))
									case Success(None, _) => cont(fail(pat, "value " + display(_state, value) + " does not match pattern"))
									case Success(Some(matchings), _) => cont(success(_state.bind(matchings)))
								}
							}
					})
				case STAssign(pat, body) =>
					if (!(pat.introVars subsetOf state.assignables)) {
						val unassignables = pat.introVars -- state.assignables
						var error = "pattern assigns to variables not in linear scope:"
						for (v <- unassignables) error = error + " " + v
						cont(fail(pat, error))
					} else {
						evalBlock[T](state.setCollect(Collect.emptyOne), body,  {
							case f : Failed[_] => cont(fail(f))
							case su @ Success(s, isReturnValue) => 
								if (isReturnValue) cont(su)
								else {
									val value = s.reapCollect
									val _state = state.setContext(s.context)
									matchPattern(_state.freeze, pat, value) match {
										case Failed(pos, error) => cont(Failed(pos, error))
										case Success(None, _) => cont(fail(pat, "value " + display(_state, value) + " does not match pattern"))
										case Success(Some(matchings), _) => cont(success(_state.rebind(matchings)))
									}
							}
						})				
					}	
				case STExpr(expr) =>
					val ok =
						state.collect match {
							case Collect.Zero => false
							case _ : Collect.One => isLastStatement
							case _ : Collect.Multiple => true
						}
					if (!ok) cont(fail(st, "cannot yield here"))
					else {
						evalExpr[T](state.freeze, expr,  {
							case f : Failed[_] => cont(fail(f))
							case Success(s, _) => cont(success(state.addToCollect(s)))
						})
					}
				case STReturn(expr) => 
					if (!state.canReturn) cont(fail(st, "cannot return here"))
					else {
						expr match {
							case None => cont(Success(State.fromValue(NilValue), true))
							case Some(expr) =>
								evalExpr[T](state.freeze, expr,  {
									case f : Failed[_] => cont(fail(f))
									case Success(s, _) => cont(Success(State.fromValue(s), true))
								})						
						}
					}
				case STShow(expr) => 
					evalExpr[T](state.freeze, expr,  {
						case f : Failed[_] => cont(fail(f)) 
						case Success(value, _) => 
							val location : String = 
								st.sourcePosition.span match {
									case None => ""
									case Some(span) => ":" + (span.firstRow + 1)
								}
							output.add(namespace, st.sourcePosition.span, OutputKind.SHOW, display(state, value))
							cont(success(state))
					})
				case STFail(None) => cont(fail(st, "fail"))
				case STFail(Some(expr)) =>
					evalExpr[T](state.freeze, expr,  {
						case f : Failed[_] => cont(fail(f))
						case Success(value, _) => cont(fail(st, "fail: "+display(state, value)))
					})
				case STAssert(expr) =>
					evalExpr[T](state.freeze, expr,  {
						case f : Failed[_] => cont(fail(f))
						case Success(BoolValue(true), _) => cont(success(state))
						case Success(BoolValue(false), _) => cont(fail(st, "Assertion does not hold"))
						case Success(value, _) => cont(fail(st, "Assertion does not hold: " + display(state, value)))
					})
				case STFailure(block) =>
					evalBlock[T](state.freeze.setCollect(Collect.emptyMultiple), block,  {
						case f : Failed[_] => 
							val location : String = 
								st.sourcePosition.span match {
									case None => ""
									case Some(span) => ":" + (span.firstRow + 1)
								}						
							output.add(namespace, st.sourcePosition.span, OutputKind.FAILURE, f.error)
							cont(success(state))
						case Success(newState, _) =>
							val value = newState.reapCollect 
							cont(fail(st, "Failure expected, but evaluates successfully to: " + display(state, value)))
					})		
				case STControlFlow(controlflow) =>
					val (changedCollect, collect) = 
						state.collect match {
							case _ : Collect.One if !isLastStatement => (true, Collect.Zero)
							case c => (false, c)
						}
					evalControlFlow[T](state.setCollect(collect), controlflow,  {
						case f : Failed[_] => cont(fail(f))
						case su @ Success(value, isReturnValue) =>
							if (isReturnValue) cont(su)
							else cont(success(if (changedCollect) value.setCollect(state.collect) else value))
					})
				case stdef : STDef =>
					lookupVars(state, stdef.freeVars) match {
						case Right(xs) =>
							var error = "definition depends on unknown free variables:"
							for (x <- xs) error = error + " " + x
							cont(fail(stdef, error))
						case Left(bindings) =>
							var functions : Map[String, RecursiveFunctionValue] = Map()
							var nonlinear = bindings
							for ((name, cs) <- stdef.cases) {
								val f = RecursiveFunctionValue(null, cs)
								nonlinear = nonlinear + (name -> f)
								functions = functions + (name -> f)
							}
							var defstate = new State(state.context, State.Env(nonlinear, Map()), Collect.emptyOne, true)
							for ((_, f) <- functions) f.state = defstate
							cont(success(state.bind(functions)))
					}
				case st if isLogicStatement(st) => 
					evalLogicStatement[T](state, st,  {
						case f : Failed[_] => cont(fail(f))
						case Success((_state, name, value), isReturnValue) =>
							if (isReturnValue) cont(Success(_state, true))
							else {
								var state = _state
								if (name.isDefined) state = state.bind(Map(name.get -> value))
								if (isLastStatement) 
									state.collect match {
										case _ : Collect.One => state = state.addToCollect(value)
										case _ => // do nothing
									}
								cont(success(state))
							}
					})
				case _ : STComment => cont(success(state))
				case _ => cont(fail(st, "statement has not been implemented yet: "+st))
			}
	  } finally {
	  	decEvalDepth()
	  }
	}

	def evalBlocki[T](state : State, block : Block, i : Int, cont : RC[State, T]) : Thunk[T] = {
		val num = block.statements.size 
		if (i >= num) {
			state.collect match {
				case Collect.One(None) => cont(fail(block, "block does not yield a value")) 
				case _ => cont(success(state))
			}						
		} else {
			evalStatement(state, block.statements(i), i == num - 1,  {
				case f : Failed[State] => cont(f)
				case s @ Success(state, isReturnValue) => 
					if (isReturnValue) cont(s)
					else evalBlocki(state, block, i + 1,  cont)
			})
		}
	}

	def evalBlock[T](state : State, block : Block,  cont : RC[State, T]) : Thunk[T] = {	
		evalBlocki[T](state, block, 0,  cont)
	}

	def evalBlockSynchronously(state : State, block : Block) : Result[State] = {		
		pushEvalDepth()
		try {
			evalBlock[Result[State]](state, block, (r : Result[State]) => Thunk.value(r))()
		} finally { 
			popEvalDepth()
		}
	}


	def isLogicStatement(st : Statement) : Boolean = {
		st match {
			case _ : STAssume => true
			case _ : STLet => true
			case _ : STChoose => true
			case _ : STTheorem => true
			case _ => false
		}
	}

	def evalLogicStatement[T](state : State, st : Statement,  
		cont : RC[(State, Option[String], StateValue), T]) : Thunk[T] = 
	{
		st match {
			case STAssume(thm_name, tm) =>
				evalTermExpr[T](state.freeze, tm, {
					case failed : Failed[_] => cont(fail(failed))
					case Success(tm, _) =>
						try {
							val thm = state.context.assume(tm)
							cont(success((state.setContext(thm.context), thm_name, new TheoremValue(thm))))
						} catch {
							case ex : Utils.KernelException =>
								cont(fail(st, "assume: "+ex.reason))
						}
				})
			case st @ STLet(thm_name, tm) =>
				evalPretermExpr(state, tm, {
					case failed : Failed[_] => cont(fail(failed))
					case Success((ptm, state), _) =>
						checkTypedName(ptm) match {
							case None => 
								letIsDef(ptm) match {
									case None =>
										cont(fail(st, "let can only handle introductions or simple definitions"))
									case Some((n, tys, right)) => cont(evalLetDef(state, st, ptm, n, tys, right))
								}
							case Some((n, tys)) => cont(evalLetIntro(state, st, n, tys))
						}
				})
			case STChoose(thm_name, tm, proof) =>
				evalPretermExpr(state, tm, {
					case failed : Failed[_] => cont(fail(failed))
					case Success((ptm, state), _) =>
						checkTypedName(ptm) match {
							case None => cont(fail(tm, "name expected"))
							case Some((n, tys)) =>
								if (n.namespace.isDefined) cont(fail(tm, "choose: constant must not have explicit namespace"))
								else {
									val name = Name(Some(state.context.namespace), n.name)
									evalProof(state, proof, {
										case failed : Failed[_] => cont(fail(failed))
										case Success(value, true) => 
											cont(Success((State.fromValue(value), thm_name, value), true))
										case Success(TheoremValue(thm), _) =>
											try {
												val liftedThm = state.context.lift(thm)
												val chosenThm = state.context.choose(name, liftedThm)
												val ty = chosenThm.context.typeOfConst(name).get
												if (!Pretype.solve(Pretype.translate(ty) :: tys).isDefined) 
													cont(fail(st, "declared type of constant does not match computed type"))
												else
													cont(success((state.setContext(chosenThm.context), thm_name, TheoremValue(chosenThm))))
											}	catch {
												case ex : Utils.KernelException =>
													cont(fail(st, "choose: " + ex.reason))
											}	
										case Success(v, _) => cont(fail(proof, "Theorem expected, found: " + display(state, v)))
									})
								}
						}
				})
			case STTheorem(thm_name, tm, proof) =>
				evalTermExpr(state.freeze, tm, {
					case f : Failed[_] => cont(fail(f))
					case Success(prop, _) =>
						if (state.context.typeOfTerm(prop) != Some(Type.Prop)) 
							cont(fail(tm, "Proposition expected, found: " + display(state, TermValue(prop))))
						else {
							evalProof(state, proof, {
								case f : Failed[_] => cont(fail(f))
								case Success(value, true) => 
									cont(Success((State.fromValue(value), thm_name, value), true))
								case Success(TheoremValue(thm), _) =>
									try {
										val ctx = state.context
										val liftedThm = ctx.lift(thm, false)
										if (!KernelUtils.betaEtaEq(prop, liftedThm.proposition)) {
											val liftedThm2 = ctx.lift(thm, true)
											if (!KernelUtils.betaEtaEq(prop, liftedThm2.proposition)) {
												if (KernelUtils.betaEtaEq(liftedThm.proposition, liftedThm2.proposition)) 
													cont(fail(proof, "Proven theorem does not match: " + display(state, TheoremValue(liftedThm))))
												else {
													val th1 = display(state, TheoremValue(liftedThm))
													val th2 = display(state, TheoremValue(liftedThm2))
													cont(fail(proof, "Proven theorem does not match, neither as:\n    "+th1+"\nnor as:\n    "+th2))
												}
											} else {
												cont(success((state, thm_name, TheoremValue(ctx.normalize(liftedThm2, prop)))))
											}
										} else 
											cont(success((state, thm_name, TheoremValue(ctx.normalize(liftedThm, prop)))))
									} catch {
										case ex: Utils.KernelException => cont(fail(st, "theorem: " + ex.reason))
									}
								case Success(v, _) => cont(fail(proof, "Theorem expected, found: " + display(state, v)))
							})
						}
				})
			case _ =>
				cont(fail(st, "internal error: statement is not a logic statement"))
		}
	}

	def evalProof[T](state : State, proof : Block, cont : RC[StateValue, T]) : Thunk[T] = {
		evalBlock(state.setCollect(Collect.emptyOne), proof, {
			case f : Failed[_] => cont(fail(f))
			case Success(state, isReturnValue) => 
				state.reapCollect match {
					case TheoremValue(th) if !isReturnValue =>
						val liftedTh = state.context.lift(th)
						cont(Success(TheoremValue(liftedTh), false))
					case value => cont(Success(value, isReturnValue))
				}
		})
	}

	def evalLetIntro(state : State, st : STLet, _name : Name, tys : List[Pretype]) : 
		Result[(State, Option[String], StateValue)] = 
	{
		val name = 
			_name.namespace match {
				case Some(ns) => return fail(st, "let intro: constant must not have explicit namespace")
				case None => Name(Some(state.context.namespace), _name.name)
			}
		Pretype.solve(tys) match {
			case None => fail(st, "let intro: inconsistent type constraints")
			case Some(ty) =>
				try {
					var s = state.setContext(state.context.introduce(name, ty))
					success((s, st.result_name, TermValue(Term.Const(name))))
				} catch {
					case ex: Utils.KernelException =>
						return fail(st, "let intro: " + ex.reason)
				}
		}
	}

	def checkTypedName(ptm : Preterm) : Option[(Name, List[Pretype])] = {
		ptm match {
			case Preterm.PTmName(n, ty) => Some((n, List(ty)))
			case Preterm.PTmTyping(tm, ty) => 
				checkTypedName(tm) match {
					case Some((n, tys)) => Some((n, ty :: tys))
					case None => None
				}
			case _ => None
		}
	}

	def letIsDef(ptm : Preterm) : Option[(Name, List[Pretype], Preterm)] = {
		import Preterm._
		ptm match {
			case PTmComb(PTmComb(PTmName(Kernel.equals, _), left, Some(true), _), right, Some(true), _) =>
				checkTypedName(left) match {
					case None => None
					case Some((n, tys)) => Some((n, tys, right))
				}	
			case _ => None		
		}
	}

	def evalLetDef(state : State, st : STLet, ptm : Preterm, _name : Name, 
		tys : List[Pretype], _rightHandSide : Preterm) : Result[(State, Option[String], StateValue)] = 
	{
		val name = 
			_name.namespace match {
				case Some(ns) => return fail(st, "let def: constant must not have explicit namespace")
				case None => Name(Some(state.context.namespace), _name.name)
			}
		var rightHandSide = _rightHandSide
		for (ty <- tys) rightHandSide = Preterm.PTmTyping(rightHandSide, ty)
		resolvePreterm(state.context, rightHandSide) match {
			case failed : Failed[_] => fail(st, "let def: ")
			case Success(tm, _) =>	
				try {
					val thm = state.context.define(name, tm)
					success((state.setContext(thm.context), st.result_name, TheoremValue(thm)))
				} catch {
					case ex: Utils.KernelException =>
						return fail(st, "let def: " + ex.reason)
				}
		}
	}	

	def evalSubBlock[T](state : State, block : Block,  cont : RC[State, T]) : Thunk[T] = {
		evalBlock[T](state, block,  {
			case f : Failed[_] => cont(f)
			case su @ Success(updatedState, isReturnValue) =>
				if (isReturnValue) cont(su)
				else cont(success(state.subsume(updatedState)))
		})
	}

	sealed trait CmpResult
	case object IsLess extends CmpResult
	case object IsLessOrEqual extends CmpResult
	case object IsEq extends CmpResult
	case object IsGreater extends CmpResult
	case object IsGreaterOrEqual extends CmpResult
	case object IsNEq extends CmpResult

	def cmp(state : State, x : StateValue, y : StateValue) : Option[CmpResult] = {
		(x, y) match {
			case (NilValue, NilValue) => Some(IsEq)
			case (IntValue(x), IntValue(y)) => 
				if (x < y) Some(IsLess) 
				else if (x > y) Some(IsGreater)
				else Some(IsEq)
			case (BoolValue(x), BoolValue(y)) =>
				if (x == y) Some(IsEq) else Some(IsNEq)
			case (x : StringValue, y : StringValue) =>
				val a = x.toString
				val b = y.toString
				if (a < b) Some(IsLess)
				else if (a > b) Some(IsGreater)
				else Some(IsEq)
			case (TupleValue(xs), TupleValue(ys)) =>
				val len = xs.size
				if (len == ys.size) {
					var has_less = false
					var has_eq = false
					var has_greater = false
					var has_neq = false
					for (i <- 0 until len)
						cmp(state, xs(i), ys(i)) match {
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
				} else Some(IsNEq)
			case (TermValue(u), TermValue(v)) => 
				import KernelUtils._
				if (betaEtaEq(u, v))
					Some(IsEq)
				else
					Some(IsNEq)
			case (TheoremValue(p), TheoremValue(q)) => 
				import KernelUtils._
				try { 
				  val u = state.context.lift(p).proposition
				  val v = state.context.lift(q).proposition
					if (betaEtaEq(u, v))
						Some(IsEq)
					else
						Some(IsNEq)				  
				} catch {
				  case e: Utils.KernelException => None
				}
			case (_ : ContextValue, _ : ContextValue) => None
			case (f, g) if StateValue.isFunction(f) && StateValue.isFunction(g) => None
			case _ => Some(IsNEq)	
		}
	}

	def cmp(state : State, op : CmpOperator, x : StateValue, y : StateValue) : Result[Boolean] = {
		cmp (state, x, y) match {
			case None => fail(op, "values cannot be compared: " + display(state, x) + ", " + display(state, y))
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

	def lookupVar(p : ParseTree, state : State, full : Boolean, namespace : Namespace, name : String) : Result[StateValue] = {
		val r = 
			if (full) 
				scriptNameresolution.fullResolution(namespace) 
			else 
				scriptNameresolution.baseResolution(namespace)
		r.get(name) match {
			case None => fail(p, "unknown identifier: "+name)
			case Some(namespaces) =>
				namespaces.size match {
					case 0 => fail(p, "unknown identifier: "+name)
					case 1 => 
						val ns = namespaces.head
						success(completedStates(ns).get.lookup(name).get)
					case n =>
						var display = ""
						for (ns <- namespaces) display = display + ns + " "
						fail(p, "ambiguous identifier " + name + ", defined in " + n + " different namespaces: " + display)
				}
		}
	}

	def lookupVars(state : State, names : Set[String]) : Either[Map[String, StateValue], Set[String]] = {
		var values : Map[String, StateValue] = Map()
		var notfound : Set[String] = Set()
		for (name <- names) {
			state.lookup(name) match {
				case Some(v) => values = values + (name -> v)
				case None =>
					lookupVar(null, state, false, namespace, name) match {
						case Success(v, _) => values = values + (name -> v)
						case _ => notfound = notfound + name
					}
			}
		}
		if (notfound.isEmpty)
			Left(values)
		else
			Right(notfound)
	}

	def evalExprSynchronously(state : State, expr : Expr) : Result[StateValue] = {
		pushEvalDepth()
		try {
			evalExpr[Result[StateValue]](state, expr, (r : Result[StateValue]) => Thunk.value(r))()
		} finally {
			popEvalDepth()
		}
	}

	def evalExpr[T](state : State, expr : Expr,  _cont : RC[StateValue, T]) : Thunk[T] = {
		try {
			val cont : RC[StateValue, T] = protectOverflowCont(_cont)
			if (incEvalDepth()) return Thunk.computation(() => evalExpr[T](state, expr, cont))
			expr match {
				case NilExpr => cont(success(NilValue))
				case Bool(b) => cont(success(BoolValue(b)))
				case Integer(i) => cont(success(IntValue(i)))
				case StringLiteral(s) => cont(success(StringValue(s)))
				case Id(name) =>
					state.lookup(name) match {
						case None => cont(lookupVar(expr, state, false, namespace, name))
						case Some(v) => cont(success(v))
					}
				case QualifiedId(_ns, name) =>
					val ns = aliases.resolve(_ns)
					if (scriptNameresolution.ancestorNamespaces(namespace).contains(ns))
						cont(lookupVar(expr, state, true, ns, name))
					else 
						cont(fail(expr, "unknown or inaccessible namespace: "+ns))
				case UnaryOperation(op, expr) =>
					evalExpr[T](state, expr,  {
						case Success(value, _) =>
							(op, value) match {
								case (Not, BoolValue(b)) => cont(success(BoolValue(!b)))
								case (Neg, IntValue(i)) => cont(success(IntValue(-i)))
								case _ => cont(fail(op, "unary operator "+op+" cannot be applied to: "+display(state, value)))
							}
						case f => cont(f)
					})
				case BinaryOperation(op, left, right) if op != And && op != Or =>
					evalExpr[T](state, left,  {
						case Success(left, _) =>
							evalExpr[T](state, right,  {
								case Success(right, _) =>
									(op, left, right) match {
										case (RangeTo, IntValue(x), IntValue(y)) => 
											cont(success(TupleValue((x to y).map(i => IntValue(i)).toVector)))
										case (RangeDownto, IntValue(x), IntValue(y)) => 
											cont(success(TupleValue((y to x).reverse.map(i => IntValue(i)).toVector)))
										case (Add, IntValue(x), IntValue(y)) => cont(success(IntValue(x + y)))
										case (Sub, IntValue(x), IntValue(y)) => cont(success(IntValue(x - y)))
										case (Mul, IntValue(x), IntValue(y)) => cont(success(IntValue(x * y)))
										case (Div, IntValue(x), IntValue(y)) => 
											if (y == 0)
												cont(fail(op, "division by zero"))
											else
												cont(success(IntValue(x / y)))
										case (Mod, IntValue(x), IntValue(y)) =>
											if (y == 0)
												cont(fail(op, "modulo zero"))
											else
												cont(success(IntValue(x % y)))
										case (And, BoolValue(x), BoolValue(y)) => cont(success(BoolValue(x && y)))
										case (Or, BoolValue(x), BoolValue(y)) => cont(success(BoolValue(x || y)))
										case (Prepend, x, xs : TupleValue) => cont(success(xs.prepend(x)))
										case (Append, xs : TupleValue, x) => cont(success(xs.append(x)))
										case (Concat, xs : TupleValue, ys : TupleValue) => cont(success(xs.concat(ys)))
										case (Concat, xs : StringValue, ys : StringValue) => cont(success(xs.concat(ys)))
										case _ => cont(fail(op, "binary operator "+op+" cannot be applied to values: "+
											display(state,left)+", "+display(state,right)))
									}
								case f => cont(f)
							})
						case f => cont(f)
					})
				case BinaryOperation(And, left, right) =>
					evalExpr[T](state, left,  {
						case Success(v @ BoolValue(false), _) => cont(success(v))
						case Success(BoolValue(true), _) => 
							evalExpr(state, right,   {
								case su @ Success(_ : BoolValue, _) => cont(su)
								case Success(v, _) => cont(fail(right, "Boolean expected, found: " + display(state, v)))
								case f => cont(f)
							})
						case Success(v, _) => cont(fail(left, "Boolean expected, found: " + display(state, v)))
						case f => cont(f)
					})
				case BinaryOperation(Or, left, right) => 
					evalExpr[T](state, left,  {
						case Success(v @ BoolValue(true), _) => cont(success(v))
						case Success(BoolValue(false), _) => 
							evalExpr[T](state, right,  {
								case su @ Success(_ : BoolValue, _) => cont(su)
								case Success(v, _) => cont(fail(right, "Boolean expected, found: " + display(state, v)))
								case f => cont(f)
							})
						case Success(v, _) => cont(fail(left, "Boolean expected, found: " + display(state, v)))
						case f => cont(f)
					})
				case CmpOperation(operators, operands) => 
					evalExpr[T](state, operands.head,  {
						case f : Failed[_] => cont(f)
						case Success(v, _) =>
							def loop(value : StateValue, operators : Seq[CmpOperator], operands : Seq[Expr],
								 cont : RC[StateValue, T]) : Thunk[T] = 
							{
								if (operators.isEmpty) 
									cont(success(BoolValue(true)))
								else {
									evalExpr[T](state, operands.head,  {
										case f : Failed[_] => cont(f)
										case Success(v, _) =>
											cmp(state, operators.head, value, v) match {
												case f : Failed[_] => cont(fail(f))
												case Success(false, _) => cont(success(BoolValue(false)))
												case Success(true, _) => loop(v, operators.tail, operands.tail,  cont)
											}
									})
								}
							}
							loop(v, operators, operands.tail,  cont)
					}) 
				case Tuple(xs) => 
					def loop(xs : Seq[Expr], values : List[StateValue],  cont : RC[StateValue, T]) : Thunk[T] = {
						if (xs.isEmpty) 
							cont(success(TupleValue(values.reverse.toVector)))
						else 
							evalExpr[T](state, xs.head,  {
								case f : Failed[_] => cont(f)
								case Success(value, _) => loop(xs.tail, value :: values,  cont)
							})
					}
					loop(xs, List(),  cont)
				case ControlFlowExpr(controlflow) => 
					val cstate = state.setCollect(Collect.emptyOne)
					evalControlFlow[T](cstate, controlflow,  {
						case f : Failed[_] => cont(fail(f))
						case Success(state, _) => cont(success(state.reapCollect))
					}) 
				case f @ Fun(param, body) => 
					lookupVars(state, f.freeVars) match {
						case Right(notFound) =>
							var error = "function has unknown free variables:"
							for (x <- notFound) error = error + " " + x
							cont(fail(f, error))
						case Left(nonlinear) =>
							val funstate = new State(state.context, State.Env(nonlinear, Map()), Collect.emptyOne, true)
							cont(success(SimpleFunctionValue(funstate, f)))
					}
				case App(u, v) =>
					evalExpr[T](state, u,  {
						case failed : Failed[_] => cont(failed)
						case Success(f : SimpleFunctionValue, _) =>
							evalExpr[T](state, v,  {
								case failed : Failed[_] => cont(failed)
								case Success(x, _) => evalApply[T](f.state.setContext(state.context), f.f.param, f.f.body, x,
									 cont)
							})
						case Success(f : RecursiveFunctionValue, _) =>
							evalExpr[T](state, v,  {
								case failed : Failed[_] => cont(failed)
								case Success(x, _) => evalApply[T](f.state.setContext(state.context), f.cases, x,  cont)
							})
						case Success(f : NativeFunctionValue, _) =>
							evalExpr[T](state, v,  {
								case failed : Failed[_] => cont(failed)
								case Success(x, _) => 
									f.nativeFunction(this, state, x) match {
										case Left(value) => cont(success(value))
										case Right(error) => cont(fail(expr, error))
									}
							})
						case Success(StringValue(s), _) =>
							evalExpr[T](state, v,  {
								case failed : Failed[_] => cont(failed)
								case Success(IntValue(i), _) =>
									if (i < 0 || i >= s.size) cont(fail(v, "index " + i + " is out of bounds"))
									else cont(success(StringValue(Vector(s(i.toInt)))))
								case Success(TupleValue(indices), _) =>
									def buildString() : Thunk[T] = {
										val len = s.size
										var codes : List[Int] = List()
										for (index <- indices) {
											index match {
												case IntValue(i) =>
													if (i < 0 || i >= len) return cont(fail(v, "index " + i + " is out of bounds"))
													else codes = s(i.toInt) :: codes
												case _ =>
													return cont(fail(v, "index expected, found: " + display(state, index)))
											}
										}
										cont(success(StringValue(codes.reverse.toVector)))									
									}
									buildString()
								case Success(value, _) =>
									cont(fail(v, "string cannot be applied to: " + display(state, value)))
							})
						case Success(TupleValue(s), _) =>
							evalExpr[T](state, v,  {
								case failed : Failed[_] => cont(failed)
								case Success(IntValue(i), _) =>
									if (i < 0 || i >= s.size) cont(fail(v, "index " + i + " is out of bounds"))
									else cont(success(s(i.toInt)))
								case Success(TupleValue(indices), _) =>
									def buildTuple() : Thunk[T] = {
										val len = s.size
										var values : List[StateValue] = List()
										for (index <- indices) {
											index match {
												case IntValue(i) =>
													if (i < 0 || i >= len) return cont(fail(v, "index " + i + " is out of bounds"))
													else values = s(i.toInt) :: values
												case _ =>
													return cont(fail(v, "index expected, found: " + display(state, index)))
											}
										}
										cont(success(TupleValue(values.reverse.toVector)))									
									}
									buildTuple()
								case Success(value, _) =>
									cont(fail(v, "string cannot be applied to: " + display(state, value)))
							})					
						case Success(v, _) => cont(fail(u, "value cannot be applied to anything: " + display(state, v)))
					})
				case tm : LogicTerm =>
					evalLogicTerm(state, tm, {
						case f : Failed[_] => cont(fail(f))
						case Success(tm, _) => cont(success(TermValue(tm)))
					})
				case Lazy(_) => cont(fail(expr, "lazy evaluation is not available (yet)"))
				case _ => cont(fail(expr, "don't know how to evaluate this expression"))
			}	
		} finally {
			decEvalDepth()
		}
	}

	def evalApply[T](state : State, pat : Pattern, body : Block, argument : StateValue, 
		 cont : RC[StateValue, T]) : Thunk[T] = 
	{
		matchPattern(state.freeze, pat, argument) match {
			case failed : Failed[_] => cont(fail(failed).addToTrace(pat, FunctionLabel(this, state, argument)))
			case Success(None, _) => 
				cont(fail(null, "function argument does not match").addToTrace(pat, 
					FunctionLabel(this, state, argument)))
			case Success(Some(matchings), _) =>
				evalBlock[T](state.bind(matchings), body,  {
					case failed : Failed[_] => cont(fail(failed).addToTrace(pat, 
						FunctionLabel(this, state, argument)))
					case Success(state, _) => cont(success(state.reapCollect))
				})
		}
	}

	def evalApply[T](state : State, cases : Vector[DefCase], argument : StateValue, 
		cont : RC[StateValue, T]) : Thunk[T] = 
	{
		val matchState = state.freeze
		for (c <- cases) {
			matchPattern(matchState, c.param, argument) match {
				case failed : Failed[_] => 
					return cont(fail(failed).addToTrace(c.param, FunctionLabel(c.name, this, state, argument)))
				case Success(None, _) =>
				case Success(Some(matchings), _) =>
					return evalBlock[T](state.bind(matchings), c.body,  {
						case failed : Failed[_] => 
							cont(fail(failed).addToTrace(c.param, FunctionLabel(c.name, this, state, argument)))
						case Success(state, _) => cont(success(state.reapCollect))
					})
			}
		}
		val c = cases.head
		cont(fail(null, "function argument does not match").addToTrace(c.param, FunctionLabel(c.name, this, state, argument)))
	}

	def producesMultiple(controlflow : ControlFlow) : Boolean = {
		controlflow match {
			case Do(_, true) => true
			case _ : While => true
			case _ : For => true
			case _ => false
		}
	}

	def evalControlFlow[T](state : State, controlflow : ControlFlow,  
		cont : RC[State, T]) : Thunk[T] = 
	{
		val wrapMultiple =
			state.collect match {
				case _ : Collect.One => producesMultiple(controlflow)
				case _ => false
			}	
		if (wrapMultiple) {
			evalControlFlowSwitch[T](state.setCollect(Collect.emptyMultiple), controlflow,  {
				case f : Failed[_] => cont(f)
				case su @ Success(state, isReturnValue) =>
					if (isReturnValue) cont(su)
					else cont(success(state.setCollect(Collect.One(Some(state.reapCollect)))))
			})
		} else 
			evalControlFlowSwitch[T](state, controlflow,  cont)
	}

	def evalControlFlowSwitch[T](state : State, controlflow : ControlFlow, 
		 cont : RC[State, T]) : Thunk[T] = 
	{
		controlflow match {
			case c : Do => evalDo[T](state, c, cont)
			case c : If => evalIf[T](state, c, cont)
			case c : While => evalWhile[T](state, c, cont)
			case c : For => evalFor[T](state, c, cont)
			case c : Match => evalMatch[T](state, c, cont)
			case c : ContextControl => evalContextControl[T](state, c,  cont)
			case _ => cont(fail(controlflow, "controlflow not implemented yet: "+controlflow))
		}
	}

	def evalDo[T](state : State, control : Do,  cont : RC[State, T]) : Thunk[T] = {
		evalSubBlock[T](state, control.block,  cont)
	}

	def evalIf[T](state : State, control : If,  cont : RC[State, T]) : Thunk[T] = {
		evalExpr[T](state.freeze, control.cond,  {
			case f : Failed[_] => cont(fail(f))
			case Success(BoolValue(test), _) =>
				if (test) 
					evalSubBlock[T](state, control.thenCase,  cont) 
				else 
					evalSubBlock[T](state, control.elseCase,  cont)
			case Success(value, _) => cont(fail(control.cond, "Boolean expected, found: " + display(state, value)))
		})
	}

	def evalWhile[T](state : State, control : While,  cont : RC[State, T]) : Thunk[T] = {
		evalExpr(state.freeze, control.cond,  {
			case f : Failed[_] => cont(fail(f))
			case Success(BoolValue(false), _) => cont(success(state))
			case Success(BoolValue(true), _) => 
				evalSubBlock[T](state, control.body,  {
					case f : Failed[_] => cont(f)
					case su @ Success(s, isReturnValue) =>
						if (isReturnValue) cont(su)
						else evalWhile[T](state.subsume(s), control,  cont)
				})
			case Success(value, _) => cont(fail(control.cond, "Boolean expected, found: " + display(state, value)))
		})
	}

	def evalFor[T](state : State, control : For,  cont : RC[State, T]) : Thunk[T] = {
		evalExpr[T](state.freeze, control.coll,  {
			case f : Failed[_] => cont(fail(f))
			case Success(TupleValue(values), _) =>
				def loop(state : State, values : Seq[StateValue],  cont : RC[State, T]) : Thunk[T] = {
					if (values.isEmpty) cont(success(state))
					else {
						matchPattern(state.freeze, control.pat, values.head) match {
							case f : Failed[_] => cont(fail(f))
							case Success(None, _) => loop(state, values.tail,  cont)
							case Success(Some(matchings), _) =>
								evalSubBlock(state.bind(matchings), control.body,  {
									case f : Failed[_] => cont(f)
									case su @ Success(s, isReturnValue) =>
										if (isReturnValue) cont(su)
										else loop(state.subsume(s), values.tail,  cont)
								})
						}
					}
				}
				loop(state, values,  cont)
			case Success(v, _) => cont(fail(control.coll, "tuple expected, found: " + v))
		})
	}

	def evalMatch[T](state : State, control : Match,  cont : RC[State, T]) : Thunk[T] = {
		val frozenState = state.freeze
		evalExpr(frozenState, control.expr,  {
			case f : Failed[_] => cont(fail(f))
			case Success(value, _) =>
				def loop(cases : Seq[MatchCase],  cont : RC[State, T]) : Thunk[T] = {
					if (cases.isEmpty) {
						cont(fail(control, "no match for value: " + display(state, value)))
					} else {
						val matchCase = cases.head
						matchPattern(frozenState, matchCase.pat, value) match {
							case f : Failed[_] => cont(fail(f))
							case Success(None, _) => loop(cases.tail,  cont)
							case Success(Some(matchings), _) =>
								evalSubBlock[T](state.bind(matchings), matchCase.body,  {
									case f : Failed[_] => cont(fail(f))
									case su @ Success(s, isReturnValue) =>
										if (isReturnValue) cont(su)
										else cont(success(state.subsume(s)))
								})
						}	
					}
				}
				loop(control.cases,  cont)
		})
	}

	def evalContextControl[T](state : State, control : ContextControl,  cont : RC[State, T]) : Thunk[T] = {
		val contWithContext : Continuation[Context, T] = { 
			case context : Context =>
				evalBlock[T](state.setContext(context).setCollect(Collect.Zero), control.body,  {
					case failed : Failed[_] => cont(failed)
					case su @ Success(updatedState, isReturnValue) =>
						if (isReturnValue) cont(su)	
						else {
							state.collect match {
								case _ : Collect.One =>
									cont(success(state.addToCollect(ContextValue(updatedState.context))))
								case _ => 
									cont(success(state))
							}
						}
				})
		}

		control.ctx match {
			case None => contWithContext(state.context)
			case Some(expr) =>
				evalExpr[T](state.freeze, expr,  {
					case failed : Failed[_] => cont(fail(failed))
					case Success(ContextValue(context), _) => contWithContext(context)
					case Success(TheoremValue(thm), _) => contWithContext(thm.context)
					case Success(v, _) => cont(fail(expr, "context or theorem expected, found: " + display(state, v)))
				})
		}
	}

	type Matchings = Map[String, StateValue]

	def matchPattern(state : State, pat : Pattern, value : StateValue) : Result[Option[Matchings]] = {
		matchPattern(state, pat, value, Map())
	}

	def matchPattern(state : State, pat : Pattern, value : StateValue, matchings : Matchings) : Result[Option[Matchings]] = {
		pat match {
			case PAny => success(Some(matchings))
			case PNil =>
				value match {
					case NilValue => success(Some(matchings))
					case _ => success(None)
				}
			case PId(name) => 
				matchings.get(name) match {
					case None => success(Some(matchings + (name -> value)))
					case Some(v) => fail(pat, "pattern is not linear, multiple use of: "+v)
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
			case PString(xs) =>
				value match {
					case StringValue(ys) if xs == ys => success(Some(matchings))
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
			case PIf(p, cond) =>
				matchPattern(state, p, value) match {
					case Success(Some(pMatchings), _) =>
						for ((id,_) <- pMatchings) {
							if (matchings.contains(id))
								return fail(p, "pattern is not linear, multiple use of: "+id)
						}
						evalExprSynchronously(state.bind(pMatchings).freeze, cond) match {
							case failed : Failed[_] => fail(failed)
							case Success(BoolValue(false), _) => success(None)
							case Success(BoolValue(true), _) => success(Some(matchings ++ pMatchings))
							case Success(v, _) => fail(cond, "Boolean expected, found: "+display(state, v))
						}
					case r => r
				}
			case PAs(p, name) =>
				matchPattern(state, p, value, matchings) match {
					case Success(Some(matchings), _) =>
						matchings.get(name) match {
							case None => success(Some(matchings + (name -> value)))
							case Some(v) => fail(pat, "pattern is not linear, multiple use of: "+v)
						}
					case r => r
				}
			case PLogic(_preterm) =>
				val term = 
					value match {
						case TermValue(value) => value
						case TheoremValue(thm) => state.context.lift(thm).proposition
						case s : StringValue =>
							try {
								Syntax.parseTerm(aliases, logicNameresolution, state.context, s.toString)
							} catch {
								case ex : Utils.KernelException =>
									return success(None)
							}
						case _ => return success(None)
					}
				val tc = Preterm.obtainTypingContext(aliases, logicNameresolution, state.context)
				val preterm = 
					Preterm.inferPattern(tc, _preterm) match {
						case Left(preterm) => preterm
						case Right(errors) => 
							var erroroutput = errors.mkString("\n")
							if (errors.size <= 1)
								return fail(pat, "ill-typed pattern: " + erroroutput)
							else
								return fail(pat, "ill-typed pattern:\n" + erroroutput)
					}
				val (hop, quotes) = HOPattern.preterm2HOP(tc, preterm)
				if (!state.context.typeOfTerm(term).isDefined)
					return fail(pat, "value to be matched is invalid in current context, value is:\n    " + display(state, value))
				HOPattern.patternMatch(state.context, hop, term) match {
					case Right(invalid) => 
						if (invalid) fail(pat, "pattern is not a higher-order pattern")
						else success(None)
					case Left(subst) => 
						var m = matchings
						for ((quoteId, term) <- subst) {
							val value = TermValue(term)
							val p = quotes(quoteId).quoted.asInstanceOf[Pattern]
							matchPattern(state, p, value, m) match {
								case Success(Some(matchings_q), _) => m = matchings_q
								case r => return r
							}
						}
						success(Some(m))
				}
			case _ => return fail(pat, "pattern has not been implemented yet")
		}		
	}

}