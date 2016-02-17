package proofpeer.proofscript.naiveinterpreter

import proofpeer.general.StringUtils
import proofpeer.proofscript.frontend._
import proofpeer.proofscript.logic._
import proofpeer.indent.Span
import proofpeer.proofscript.automation.Automation
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
	scriptTyperesolution : NamespaceResolution[String],
	val logicNameresolution : NamespaceResolution[IndexedName], 
	val aliases : Aliases, namespace : Namespace, output : Output) 
{

	import proofpeer.general.continuation._

	type RC[S, T] = Continuation[Result[S], T]

	def mkRC[S, T](f : Result[S] => Thunk[T]) : RC[S, T] = f

	private var evalDepth : Int = 0


	private def incEvalDepth() : Boolean = {
		evalDepth = evalDepth + 1
		evalDepth > 100
	}

	private def decEvalDepth() {
		evalDepth = evalDepth - 1
	}

	def success[T](result : T) : Success[T] = Success(result, false)

	def fail[T](p : TracksSourcePosition, error : String) : Failed[T] = 
		if (p != null && p.sourcePosition != null)
			Failed(List((p.sourcePosition, NoSourceLabel)), error)
		else
			Failed(List(), error)

	def fail[S,T](f : Failed[S]) : Failed[T] = Failed(f.trace, f.error)

	def evalLogicPreterm[T](_state : State, tm : Preterm, cont : RC[Preterm, T]) : Thunk[T] = 
	{
		val state = _state.freeze
		def inst(tm : Preterm.PTmQuote, cont : Continuation[Either[Preterm, Failed[StateValue]], T]) : Thunk[T] = 
		{
			tm.quoted match {
				case _ : Pattern => cont(Left(tm))
				case expr : Expr =>
					evalExpr[T](state, expr, {
						case failed : Failed[_] => cont(Right(failed))
						case Success(TermValue(t), _) => cont(Left(Preterm.translate(state.context, t)))
						case Success(s : StringValue, _) =>
							Syntax.parsePreterm(s.toString) match {
								case None => cont(Right(fail(expr, "parse error")))
								case Some(preterm) => cont(Left(preterm))
							}
						case Success(v, _) => cont(Right(fail(expr, "term value expected, found: " + display(state, v))))
					})    	
			}
		}
		Preterm.instQuotes[Failed[StateValue], T](inst, instType[T](state) _, tm, {
		  case Right(f) => cont(fail(f))
			case Left(preterm) => cont(success(preterm))
		})
	}

	def resolvePreterm(context : Context, preterm : Preterm) : Result[CTerm] = {
		val typingContext = Preterm.obtainTypingContext(aliases, logicNameresolution, context)
		Preterm.inferCTerm(typingContext, preterm) match {
			case Left(tm) => success(tm)
			case Right(errors) => 
				var error = "term is not valid in current context:"
				for (e <- errors) error = error + "\n  " + e.reason
				Failed(null, error)
		}		
	}

	def evalLogicTerm[T](state : State, tm : LogicTerm, cont : RC[CTerm, T]) : Thunk[T] = {
		evalLogicPreterm[T](state, tm.tm, {
			case failed : Failed[_] => cont(fail(failed))
			case Success(preterm, _) => cont(resolvePreterm(state.context, preterm))
		})
	} 

	private def instType[T](state : State)(ty : Pretype.PTyQuote, cont : Continuation[Either[Pretype, Failed[StateValue]], T]) : Thunk[T] = 
	{
		ty.quoted match {
			case _ : Pattern => cont(Left(ty))
			case expr : Expr =>
				evalExpr[T](state, expr, {
					case failed : Failed[_] => cont(Right(failed))
					case Success(TypeValue(t), _) => cont(Left(Pretype.translate(t)))
					case Success(s : StringValue, _) =>
						Syntax.parsePretype(s.toString) match {
							case None => cont(Right(fail(expr, "parse error")))
							case Some(pretype) => cont(Left(pretype))
						}
					case Success(v, _) => cont(Right(fail(expr, "type value expected, found: " + display(state, v))))
				})    	
		}
	}

	def evalLogicPretype[T](_state : State, ty : Pretype, cont : RC[Pretype, T]) : Thunk[T] = {
		val state = _state.freeze
		Pretype.instQuotes[Failed[StateValue], T](instType[T](state) _, ty, {
			case Right(failed) => cont(fail(failed))
			case Left(pretype) => cont(success(pretype))
		})
	} 

	def evalLogicType[T](state : State, ty : LogicType, cont : RC[Type, T]) : Thunk[T] = {
		evalLogicPretype[T](state, ty.ty, {
			case failed : Failed[_] => cont(fail(failed))
			case Success(pretype, _) => cont(success(Pretype.forceTranslate(pretype)))
		})
	}

	def evalTermExpr[T](state : State, expr : Expr, cont : RC[CTerm, T]) : Thunk[T] = {
		evalExpr[T](state, expr, {
			case failed : Failed[_] => cont(fail(failed))
			case Success(TermValue(tm),_) => cont(success(tm))
			case Success(s : StringValue, _) =>
				cont(
					try {
						success(Syntax.parseCTerm(aliases, logicNameresolution, state.context, s.toString)) 
					} catch {
						case ex : Utils.KernelException =>
							fail(expr, "parse error: " + ex.reason)	
					})
			case Success(v, _) => cont(fail(expr, "Term expected, found: "+display(state, v)))
		})
	}

	def evalOptionalTheoremExpr[T](state : State, expr : Expr, cont : RC[Either[CTerm, Either[Boolean, Theorem]], T]) : Thunk[T] = {
		evalExpr[T](state, expr, {
			case failed : Failed[_] => cont(fail(failed))
			case Success(TermValue(tm),_) => cont(success(Left(tm)))
			case Success(s : StringValue, _) =>
				cont(
					try {
						success(Left(Syntax.parseCTerm(aliases, logicNameresolution, state.context, s.toString)))
					} catch {
						case ex : Utils.KernelException =>
							fail(expr, "parse error: " + ex.reason)	
					})
			case Success(NilValue, _) => cont(success(Right(Left(false))))
			case Success(BoolValue(b), _) => cont(success(Right(Left(b))))
			case Success(TheoremValue(t), _) => cont(success(Right(Right(t))))
			case Success(v, _) => cont(fail(expr, "Term expected, found: "+display(state, v)))
		})		
	}

	def evalPretermExpr[T](state : State, expr : Expr, cont : RC[Preterm, T]) : Thunk[T] = {
		expr match {
			case tm : LogicTerm => 
				evalLogicPreterm[T](state, tm.tm, cont)
			case _ => 
				evalExpr[T](state.freeze, expr, {
					case failed : Failed[_] => cont(fail(failed))
					case Success(TermValue(tm),_) => cont(success(Preterm.translate(state.context, tm)))
					case Success(s : StringValue, _) =>
						Syntax.parsePreterm(s.toString) match {
							case None => cont(fail(expr, "parse error"))
							case Some(preterm) => cont(success(preterm))
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

	def evalStatement[T](state : State, st : Statement, toplevel : Boolean, isLastStatement : Boolean, _cont : RC[State, T]) : Thunk[T] = 
	{
		try {
			if (incEvalDepth()) return Thunk.computation[T](() => evalStatement[T](state, st, toplevel, isLastStatement, _cont))

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
								matchPattern[T](_state.freeze, pat, value, {
									case Failed(pos, error) => cont(Failed(pos, error))
									case Success(None, _) => cont(fail(pat, "value " + display(_state, value) + " does not match pattern"))
									case Success(Some(matchings), _) => cont(success(_state.bind(matchings)))
								})
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
									matchPattern[T](_state.freeze, pat, value, {
										case Failed(pos, error) => cont(Failed(pos, error))
										case Success(None, _) => cont(fail(pat, "value " + display(_state, value) + " does not match pattern"))
										case Success(Some(matchings), _) => cont(success(_state.rebind(matchings)))
									})
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
							val (ns, span) = locationOf(st)
							output.add(ns, span, OutputKind.SHOW, display(state, value))
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
							val (ns, span) = locationOf(st)
							output.add(ns, span, OutputKind.FAILURE, f.error)
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
				case stdef : STDef if !stdef.contextParam.isDefined =>
					evalSTDef[T](state, stdef, None, cont)
				case stdef : STDef =>
					val expr = stdef.contextParam.get
					evalExpr[T](state.freeze, expr, {
						case f: Failed[_] => cont(fail(f))
						case Success(ContextValue(context), _) => evalSTDef[T](state, stdef, Some(context), cont)
						case Success(TheoremValue(thm), _) => evalSTDef[T](state, stdef, Some(thm.context), cont)
						case Success(TermValue(tm), _) => evalSTDef[T](state, stdef, Some(tm.context), cont)						
						case Success(v, _) => cont(fail(expr, "context, term or theorem expected, found: " + display(state, v)))
					})
				case stdatatype : STDatatype => 
					if (toplevel)
						evalSTDatatype[T](state, stdatatype, cont)
					else
						cont(fail(st, "datatype statement only allowed at the top level"))
				case st if isLogicStatement(st) => 
					evalLogicStatement[T](state, st, {
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

	def evalSTDef[T](state : State, stdef : STDef, inContext : Option[Context], cont : RC[State, T]) : Thunk[T] = {
		lookupVars(state, stdef.defVars._1) match {
			case Right(xs) =>
				var error = "definition depends on unknown free variables:"
				for (x <- xs) error = error + " " + x
				cont(fail(stdef, error))
			case Left(bindings) =>
				var functions : Map[String, RecursiveFunctionValue] = Map()
				var nonlinear = bindings
				for ((name, cs) <- stdef.cases) {
					if (StringUtils.isASCIIUpperLetter(name(0))) {
						val error = "function names cannot start with uppercase letters: " + name
						return cont(fail(stdef, error))						
					}
					val f = RecursiveFunctionValue(null, cs, if (stdef.memoize) Map() else null, inContext)
					nonlinear = nonlinear + (name -> f)
					functions = functions + (name -> f)
				}
				val defstate = new State(state.context, State.Env(state.env.types, nonlinear, Map()), Collect.emptyOne, true)
				for ((_, f) <- functions) f.state = defstate
				cont(success(state.bind(functions)))
		}
	}

	def evalSTDatatype[T](state : State, stdatatype : STDatatype, cont : RC[State, T]) : Thunk[T] = {
		lookupVars(state, stdatatype.freeVars) match {
			case Right(xs) =>
				var error = "datatype definition depends on unknown free variables:"
				for (x <- xs) error = error + " " + x
				cont(fail(stdatatype, error))
			case Left(bindings) =>
				val typesInNamespace = state.env.types.keySet
				var constructors : Map[String, StateValue] = Map()
				var localTypes : Map[String, CustomType] = Map()
				for (dcase <- stdatatype.cases) {
					if (!StringUtils.isASCIIUpperLetter(dcase.typename(0))) {
						val error = "type names must start with an uppercase letter: " + dcase.typename
						return cont(fail(dcase, error))						
					}
					if (localTypes.get(dcase.typename).isDefined) {
						val error = "duplicate definition of type: " + dcase.typename
						return cont(fail(dcase, error))
					}
					if (typesInNamespace.contains(dcase.typename)) {
						val error = "type is already defined: " + dcase.typename
						return cont(fail(dcase, error))
					}
					val customtype = CustomType(namespace, dcase.typename)
					localTypes = localTypes + (dcase.typename -> customtype)
					var cases : Map[String, Option[Pattern]] = Map()
					for (c <- dcase.constrs) {
						if (!StringUtils.isASCIIUpperLetter(c.name(0))) {
							val error = "type constructors must start with an uppercase letter: " + c.name
							return cont(fail(c, error))						
						}
						if (constructors.get(c.name).isDefined) {
							val error = "duplicate definition of type constructor: " + c.name
							return cont(fail(c, error))
						}
						val constr =
							if (c.param.isEmpty) 
								ConstrValue(c.name, customtype)
							else
								ConstrUnappliedValue(c.name, customtype)
						constructors = constructors + (c.name -> constr)
						cases = cases + (c.name -> c.param)
					}
					customtype.cases = cases
				}
				val types = state.env.types ++ localTypes
				val nonlinear = bindings ++ constructors 
				val typestate = new State(state.context, State.Env(types, nonlinear, Map()), Collect.Zero, false)
				for ((_, customtype) <- localTypes) customtype.state = typestate
				cont(success(state.bindTypes(localTypes, constructors)))
		}
	}

	def evalBlocki[T](state : State, block : Block, toplevel : Boolean, i : Int, cont : RC[State, T]) : Thunk[T] = {
		val num = block.statements.size 
		if (i >= num) {
			state.collect match {
				case Collect.One(None) => cont(fail(block, "block does not yield a value")) 
				case _ => cont(success(state))
			}						
		} else {
			evalStatement(state, block.statements(i), toplevel, i == num - 1,  {
				case f : Failed[State] => cont(f)
				case s @ Success(state, isReturnValue) => 
					if (isReturnValue) cont(s)
					else evalBlocki(state, block, toplevel, i + 1,  cont)
			})
		}
	}

	def evalBlock[T](state : State, block : Block, cont : RC[State, T], toplevel : Boolean = false) : Thunk[T] = {	
		evalBlocki[T](state, block, toplevel, 0,  cont)
	}

	def eval(state : State, block : Block, toplevel : Boolean) : Result[State] = {		
		evalBlock[Result[State]](state, block, (r : Result[State]) => Thunk.value(r), toplevel)()
	}

	def isLogicStatement(st : Statement) : Boolean = {
		st match {
			case _ : STAssume => true
			case _ : STLet => true
			case _ : STChoose => true
			case _ : STTheorem => true
			case _ : STTheoremBy => true
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
				evalPretermExpr(state.freeze, tm, {
					case failed : Failed[_] => cont(fail(failed))
					case Success(ptm, _) =>
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
				evalPretermExpr(state.freeze, tm, {
					case failed : Failed[_] => cont(fail(failed))
					case Success(ptm, _) =>
						checkTypedName(ptm) match {
							case None => cont(fail(tm, "name expected"))
							case Some((n, tys)) =>
								if (n.namespace.isDefined) cont(fail(tm, "choose: constant must not have explicit namespace"))
								else {
									val name = Name(Some(state.context.namespace), n.name)
									evalProof(state.spawnThread, proof, {
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
				evalOptionalTheoremExpr(state.freeze, tm, {
					case f : Failed[_] => cont(fail(f))
					case Success(Left(prop_), _) =>
						val optProp = state.context.autolift(prop_)
						if (optProp.isEmpty) 
							cont(fail(tm, "Cannot automatically lift proposition into current context: " + display(state, TermValue(prop_))))
						else if (optProp.get.typeOf != Type.Prop) 
							cont(fail(tm, "Proposition expected, found: " + display(state, TermValue(prop_))))
						else {
							val prop = optProp.get
							evalProof(state.spawnThread, proof, {
								case f : Failed[_] => cont(fail(f))
								case Success(value, true) => 
									cont(Success((State.fromValue(value), thm_name, value), true))
								case Success(TheoremValue(thm), _) =>
									try {
										val ctx = state.context
										val liftedThm = ctx.lift(thm, false)
										if (!KernelUtils.betaEtaEq(ctx, prop, liftedThm.prop)) {
											val liftedThm2 = ctx.lift(thm, true)
											if (!KernelUtils.betaEtaEq(ctx, prop, liftedThm2.prop)) {
												if (KernelUtils.betaEtaEq(ctx, liftedThm.prop, liftedThm2.prop)) 
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
					case Success(Right(Left(preserve_structure)), _) =>
						evalProof(state.spawnThread, proof, {
							case f : Failed[_] => cont(fail(f))
							case Success(value, true) => 
								cont(Success((State.fromValue(value), thm_name, value), true))
							case Success(TheoremValue(thm), _) =>
								try {
									val ctx = state.context
									val liftedThm = ctx.lift(thm, preserve_structure)
									cont(success((state, thm_name, TheoremValue(liftedThm))))
								} catch {
									case ex: Utils.KernelException => cont(fail(st, "theorem: " + ex.reason))
								}
							case Success(v, _) => cont(fail(proof, "Theorem expected, found: " + display(state, v)))
						})			
					case Success(Right(Right(thm)), _) =>
						if (!proof.isEmpty)
							cont(fail(tm, "cannot be a theorem here because it is followed by a proof"))
						else {
							try {
								val ctx = state.context
								val liftedThm = ctx.lift(thm, false)
								cont(success((state, thm_name, TheoremValue(liftedThm))))
							} catch {
								case ex: Utils.KernelException => cont(fail(st, "theorem: " + ex.reason))
							}							
						}		
				})
			case STTheoremBy(thm_name, tm, means) =>
				val frozenState = state.freeze
				evalTermExpr(frozenState, tm, {
					case f : Failed[_] => cont(fail(f))
					case Success(prop_, _) =>
						val optProp = frozenState.context.autolift(prop_)
						if (optProp.isEmpty)
							cont(fail(tm, "Cannot automatically lift proposition into current context: " + display(state, TermValue(prop_))))
						else if (optProp.get.typeOf != Type.Prop) 
							cont(fail(tm, "Proposition expected, found: " + display(state, TermValue(prop_))))
						else {
							val prop = optProp.get
							def prove(thms : Vector[Theorem]) : Thunk[T] = {
								try {
									Automation.prove(state.context, prop, thms) match {
										case None =>
											cont(fail(st, "cannot prove theorem automatically: " + display(state, TermValue(prop))))
										case Some(thm) => 
											cont(success((state, thm_name, TheoremValue(thm))))
									}
								} catch {
									case ex: Utils.KernelException => cont(fail(st, "theorem (by): " + ex.reason))
								}
							}
							evalExpr(frozenState, means, {
								case f : Failed[_] => cont(fail(f))
								case Success(TupleValue(thms, _), _) if thms.forall(StateValue.isTheoremValue _) =>
									prove(thms.map(th => th.asInstanceOf[TheoremValue].value))
								case Success(NilValue, _) =>
									prove(Vector())
								case Success(TheoremValue(thm), _) =>
									prove(Vector(thm))
								case Success(f, _) if StateValue.isFunction(f) => 
									val x = TermValue(prop)
									evalAppValues(means, means, means, frozenState, f, x, {
										case f : Failed[_] => cont(fail(f))
										case Success(thm : TheoremValue, _) =>
											try {
												val ctx = state.context
												val liftedThm = ctx.lift(thm.value, false)
												if (!KernelUtils.betaEtaEq(ctx, prop, liftedThm.prop)) {
													cont(fail(means, "Proven theorem does not match: "+ display(state, TheoremValue(liftedThm))))
												} else 
													cont(success((state, thm_name, TheoremValue(ctx.normalize(liftedThm, prop)))))
											} catch {
												case ex: Utils.KernelException => cont(fail(means, "theorem: " + ex.reason))
											}
										case Success(v, _) =>
											cont(fail(means, "By method did not return a theorem but: " + display(frozenState, v)))
									})
								case Success(v, _) => cont(fail(means, "Invalid means for 'by': " + display(frozenState, v)))
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
					success((s, st.result_name, TermValue(s.context.certify(Term.Const(name)))))
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
			case (TupleValue(xs, cx), TupleValue(ys, cy)) =>
				val len = xs.size
				if (len == ys.size) {
					if (cx && cy) {
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
					} else None
				} else Some(IsNEq)
			case (SetValue(xs), SetValue(ys)) =>
				if (xs == ys) Some(IsEq) else Some(IsNEq)
			case (MapValue(xs, cx), MapValue(ys, cy)) =>
				if (xs.size == ys.size) {
					if (cx && cy) {
						if (xs == ys) Some(IsEq) else Some(IsNEq)
					} else None
				} else Some(IsNEq)
			case (TermValue(u), TermValue(v)) => 
				import KernelUtils._
				if (betaEtaEq(state.context, u, v))
					Some(IsEq)
				else
					Some(IsNEq)
			case (TypeValue(u), TypeValue(v)) =>
				if (u == v)
					Some(IsEq)
				else
					Some(IsNEq)
			case (c1 : ConstrValue, c2 : ConstrValue) =>
				if (c1 == c2) Some(IsEq) else Some(IsNEq)
			case (c1 : ConstrAppliedValue, c2 : ConstrAppliedValue) =>
				if (c1.name == c2.name && c1.customtype == c2.customtype)
					cmp(state, c1.param, c2.param)
				else 
					Some(IsNEq)
			case (c1 : ConstrUnappliedValue, c2 : ConstrUnappliedValue) =>
				if (c1 == c2) Some(IsEq) else Some(IsNEq)
			case (TheoremValue(p), TheoremValue(q)) => None
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

	def evalAppValues[T](location : TracksSourcePosition, locu : TracksSourcePosition, locx : TracksSourcePosition, state : State, u : StateValue, x : StateValue, cont : RC[StateValue, T]) : Thunk[T] = {
		u match {
			case f : SimpleFunctionValue =>
				evalSimpleApply[T](f.state.setContext(state.context), f.f.param, f.f.body, x, cont)
			case f : RecursiveFunctionValue =>
				val context = 
					f.context match {
						case None => state.context
						case Some(context) => context
					}
				if (f.cache != null) {
					if (x.isComparable) {
						f.cache.get(x) match {
							case Some(y) => cont(success(y))
							case None => 
								evalApply[T](f.state.setContext(context), f.cases, x, {
									case failed : Failed[_] => cont(failed)
									case s @ Success(y, _) => 
										f.cache = f.cache + (x -> y)
										cont(s)
								})
						}
					} else cont(fail(locx, "value cannot be a table header: " + display(state, x)))
				} else
					evalApply[T](f.state.setContext(context), f.cases, x,  cont)
			case f : NativeFunctionValue =>
				f.nativeFunction(this, state, x) match {
					case Left(value) => cont(success(value))
					case Right(error) => cont(fail(location, error))
				}
			case constr : ConstrUnappliedValue =>
				matchPattern[T](constr.state, constr.param, x, {
					case failed : Failed[_] => cont(fail(failed))
					case Success(None, _) =>
						cont(fail(locx, "constructor " + constr.name + " for type " + constr.customtype + 
							" cannot be applied to: " + display(constr.state, x)))
					case Success(Some(_), _) =>
						cont(success(ConstrAppliedValue(constr.name, x, constr.customtype, x.isComparable)))
				})
			case StringValue(s) =>
				x match {
					case IntValue(i) =>
						if (i < 0 || i >= s.size) cont(fail(locx, "index " + i + " is out of bounds"))
						else cont(success(StringValue(Vector(s(i.toInt)))))
					case TupleValue(indices, _) =>
						def buildString() : Thunk[T] = {
							val len = s.size
							var codes : List[Int] = List()
							for (index <- indices) {
								index match {
									case IntValue(i) =>
										if (i < 0 || i >= len) return cont(fail(locx, "index " + i + " is out of bounds"))
										else codes = s(i.toInt) :: codes
									case _ =>
										return cont(fail(locx, "index expected, found: " + display(state, index)))
								}
							}
							cont(success(StringValue(codes.reverse.toVector)))									
						}
						buildString()
					case value =>
						cont(fail(locx, "string cannot be applied to: " + display(state, value)))
				}
			case TupleValue(s, _) =>
				x match {
					case IntValue(i) =>
						if (i < 0 || i >= s.size) cont(fail(locx, "index " + i + " is out of bounds"))
						else cont(success(s(i.toInt)))
					case TupleValue(indices, _) =>
						def buildTuple() : Thunk[T] = {
							val len = s.size
							var values : List[StateValue] = List()
							var comparable = true
							for (index <- indices) {
								index match {
									case IntValue(i) =>
										if (i < 0 || i >= len) return cont(fail(locx, "index " + i + " is out of bounds"))
										else {
											val value = s(i.toInt)
											values = value :: values
											comparable = comparable && value.isComparable
										}
									case _ =>
										return cont(fail(locx, "index expected, found: " + display(state, index)))
								}
							}
							cont(success(TupleValue(values.reverse.toVector, comparable)))									
						}
						buildTuple()
					case value =>
						cont(fail(locx, "tuple cannot be applied to: " + display(state, value)))
				}
			case SetValue(s) =>
				if (x.isComparable) {	
					cont(success(BoolValue(s.contains(x))))
				} else cont(success(BoolValue(false))) 
			case MapValue(m, _) =>
				if (x.isComparable) {
					m.get(x) match {
						case None => cont(success(NilValue))
						case Some(v) => cont(success(v))
					}
				} else cont(success(NilValue))
			case u => cont(fail(locu, "value cannot be applied to anything: " + display(state, u)))
		}
	}

	def evalApp[T](location : TracksSourcePosition, state : State, u : Expr, v : Expr, cont : RC[StateValue, T]) : Thunk[T] = {
		evalExpr[T](state, u,  {
			case failed : Failed[_] => cont(failed)
			case Success(f, _) =>
				evalExpr[T](state, v,  {
					case failed : Failed[_] => cont(failed)
					case Success(x, _) => 
						evalAppValues(location, u, v, state, f, x, cont)
				})
		})
	}

	def lookupId(location : ParseTree, state : State, namespaceOpt : Option[Namespace], name : String) : Result[StateValue] = {
		namespaceOpt match {
			case None =>
				state.lookup(name) match {
					case None => lookupVar(location, state, false, namespace, name)
					case Some(v) => success(v)
				}
			case Some(_ns) =>
				val ns = aliases.resolve(_ns)
				if (scriptNameresolution.ancestorNamespaces(namespace).contains(ns))
					lookupVar(location, state, true, ns, name)
				else 
					fail(location, "unknown or inaccessible namespace: "+ns)			
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
				case Id(name) => cont(lookupId(expr, state, None, name))
				case QualifiedId(ns, name) => cont(lookupId(expr, state, Some(ns), name))
				case UnaryOperation(op, expr) =>
					evalExpr[T](state, expr,  {
						case Success(value, _) =>
							(op, value) match {
								case (Not, BoolValue(b)) => cont(success(BoolValue(!b)))
								case (Neg, IntValue(i)) => cont(success(IntValue(-i)))
								case (Destruct, c : ConstrAppliedValue) => cont(success(c.param))
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
											cont(success(TupleValue((x to y).map(i => IntValue(i)).toVector, true)))
										case (RangeDownto, IntValue(x), IntValue(y)) => 
											cont(success(TupleValue((y to x).reverse.map(i => IntValue(i)).toVector, true)))
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
										case (Concat, xs : SetValue, ys : SetValue) => cont(success(xs.concat(ys)))
										case (Concat, xs : MapValue, ys : MapValue) => cont(success(xs.concat(ys)))
										case (Minus, xs : SetValue, ys : SetValue) => cont(success(xs.minus(ys)))
										case (Minus, xs : MapValue, ys : SetValue) => cont(success(xs.minus(ys)))
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
					def loop(xs : Seq[Expr], values : List[StateValue],  comparable : Boolean, cont : RC[StateValue, T]) : Thunk[T] = {
						if (xs.isEmpty) 
							cont(success(TupleValue(values.reverse.toVector, comparable)))
						else 
							evalExpr[T](state, xs.head,  {
								case f : Failed[_] => cont(f)
								case Success(value, _) => loop(xs.tail, value :: values,  comparable && value.isComparable, cont)
							})
					}
					loop(xs, List(),  true, cont)
				case SetLiteral(xs) =>
					def loop(xs : Seq[Expr], values : Set[StateValue],  cont : RC[StateValue, T]) : Thunk[T] = {
						if (xs.isEmpty) 
							cont(success(SetValue(values)))
						else 
							evalExpr[T](state, xs.head, {
								case f : Failed[_] => cont(f)
								case Success(value, _) => 
									if (value.isComparable)
										loop(xs.tail, values + value, cont)
									else
										cont(fail(xs.head, "value cannot be a member of a set: " + display(state, value)))
							})
					}
					loop(xs, Set(),  cont)
				case MapLiteral(xs) =>
					def loop(xs : Seq[(Expr, Expr)], m : Map[StateValue, StateValue],  comparable : Boolean, cont : RC[StateValue, T]) : Thunk[T] = {
						if (xs.isEmpty) 
							cont(success(MapValue(m, comparable)))
						else {
							val (key, value) = xs.head
							evalExpr[T](state, key,  {
								case f : Failed[_] => cont(f)
								case Success(vkey, _) => 
									if (vkey.isComparable) {
										evalExpr[T](state, value, {
											case f : Failed[_] => cont(f)
											case Success(vvalue, _) =>
												loop(xs.tail, m + (vkey -> vvalue),  comparable && vvalue.isComparable, cont)
										})
									} else cont(fail(key, "value cannot be key of a map: " + display(state, vkey)))
							})
						}
					}
					loop(xs, Map(),  true, cont)								
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
							val funstate = new State(state.context, State.Env(state.env.types, nonlinear, Map()), Collect.emptyOne, true)
							cont(success(SimpleFunctionValue(funstate, f)))
					}
				case App(u, v) => evalApp(expr, state, u, v, cont)
				case TypeCast(expr, valuetype) =>
					evalExpr[T](state, expr,  {
						case failed : Failed[_] => cont(failed)
						case Success(value, _) =>
							convertValueType(state, value, valuetype) match {
								case None => cont(fail(expr, "cannot type cast value: " + display(state, value)))
								case Some(value) => cont(success(value))
							}
					})
				case tm : LogicTerm =>
					evalLogicTerm(state, tm, {
						case f : Failed[_] => cont(fail(f))
						case Success(tm, _) => cont(success(TermValue(tm)))
					})
				case ty : LogicType =>
					evalLogicType(state, ty, {
						case f : Failed[_] => cont(fail(f))
						case Success(ty, _) => cont(success(TypeValue(ty)))
					})
				case Lazy(_) => cont(fail(expr, "lazy evaluation is not available (yet)"))
				case _ => cont(fail(expr, "don't know how to evaluate this expression"))
			}	
		} finally {
			decEvalDepth()
		}
	}

	def evalSimpleApply[T](state : State, pat : Pattern, body : Block, argument : StateValue, 
		 cont : RC[StateValue, T]) : Thunk[T] = 
	{
		matchPattern[T](state.freeze, pat, argument, {
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
		})
	}

	def evalApply[T](state : State, cases : Vector[DefCase], argument : StateValue, 
		cont : RC[StateValue, T]) : Thunk[T] = 
	{
		val matchState = state.freeze
		def loop(cs : Seq[DefCase]) : Thunk[T] = {
			if (cs.isEmpty) {
				val c = cases.head
				cont(fail(null, "function argument does not match").addToTrace(c.param, FunctionLabel(c.name, this, state, argument)))
			} else {
				val c = cs.head
				matchPattern[T](matchState, c.param, argument, {
					case failed : Failed[_] => 
						cont(fail(failed).addToTrace(c.param, FunctionLabel(c.name, this, state, argument)))
					case Success(None, _) => loop(cs.tail)
					case Success(Some(matchings), _) =>
						evalBlock[T](state.bind(matchings), c.body,  {
							case failed : Failed[_] => 
								cont(fail(failed).addToTrace(c.param, FunctionLabel(c.name, this, state, argument)))
							case Success(state, _) => 
								val returnValue = state.reapCollect
								c.returnType match {
									case None => cont(success(returnValue))
									case Some(returnType) =>
										matchValueType(state, returnValue, returnType) match {
											case Left(false) => cont(fail(c, "return value does not type check: " + display(state, returnValue)))
											case Left(true) => cont(success(returnValue))
											case Right(error) => cont(fail(c, "invalid return type: " + error))
										}
								}
						})
				})				
			}
		}
		loop(cases.toSeq)
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
			evalControlFlowSwitch[T](state.setCollect(Collect.emptyMultiple), controlflow, {
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
			case c : Timeit => evalTimeit[T](state, c, cont)
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

	def evalForLoop[T](state : State, control : For, cont : RC[State, T], values : Seq[StateValue]) : Thunk[T] = {
		def loop(state : State, values : Seq[StateValue]) : Thunk[T] = {
			if (values.isEmpty) cont(success(state))
			else {
				matchPattern[T](state.freeze, control.pat, values.head, {
					case f : Failed[_] => cont(fail(f))
					case Success(None, _) => loop(state, values.tail)
					case Success(Some(matchings), _) =>
						evalSubBlock(state.bind(matchings), control.body,  {
							case f : Failed[_] => cont(f)
							case su @ Success(s, isReturnValue) =>
								if (isReturnValue) cont(su)
								else loop(state.subsume(s), values.tail)
						})
				})
			}
		}
		loop(state, values)
	}

	def evalFor[T](state : State, control : For,  cont : RC[State, T]) : Thunk[T] = {
		evalExpr[T](state.freeze, control.coll,  {
			case f : Failed[_] => cont(fail(f))
			case Success(TupleValue(values, _), _) => evalForLoop[T](state, control, cont, values)
			case Success(SetValue(s), _) => evalForLoop[T](state, control, cont, s.toSeq)
			case Success(MapValue(m, _), _) => 
				val values = m.toSeq.map({case (k, v) => TupleValue(Vector(k, v), k.isComparable && v.isComparable)})
				evalForLoop[T](state, control, cont, values)
			case Success(v, _) => cont(fail(control.coll, "tuple, set or map expected, found: " + v))
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
						matchPattern[T](frozenState, matchCase.pat, value, {
							case f : Failed[_] => cont(fail(f))
							case Success(None, _) => loop(cases.tail,  cont)
							case Success(Some(matchings), _) =>
								evalSubBlock[T](state.bind(matchings), matchCase.body,  {
									case f : Failed[_] => cont(fail(f))
									case su @ Success(s, isReturnValue) =>
										if (isReturnValue) cont(su)
										else cont(success(state.subsume(s)))
								})
						})
					}
				}
				loop(control.cases,  cont)
		})
	}

	def evalContextControl[T](state : State, control : ContextControl,  cont : RC[State, T]) : Thunk[T] = {
		val contWithContext : Continuation[Context, T] = { 
			case context : Context =>
				evalBlock[T](state.setContext(context).setCollect(Collect.Zero).spawnThread, control.body,  {
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
				evalExpr[T](state.freeze, expr, {
					case failed : Failed[_] => cont(fail(failed))
					case Success(ContextValue(context), _) => contWithContext(context)
					case Success(TheoremValue(thm), _) => contWithContext(thm.context)
					case Success(TermValue(tm), _) => contWithContext(tm.context)
					case Success(v, _) => cont(fail(expr, "context, term or theorem expected, found: " + display(state, v)))
				})
		}
	}

	def locationOf(t : TracksSourcePosition) : (Namespace, Option[Span]) = {
		if (t == null || t.sourcePosition == null)
			(namespace, None)
		else 
			(t.sourcePosition.source.namespace, t.sourcePosition.span)
	}

	def evalTimeit[T](state : State, control : Timeit, cont : RC[State, T]) : Thunk[T] = {
		val startTime = System.currentTimeMillis
		def reportTime() {
			val stopTime = System.currentTimeMillis
			val (ns, span) = locationOf(control)
			output.addTiming(ns, span, stopTime - startTime)
		}
		val timingState = 
			state.collect match {
				case Collect.Zero => state.setCollect(Collect.emptyMultiple)
				case _ : Collect.One => state.setCollect(Collect.emptyMultiple)
				case _ : Collect.Multiple => state 
			}
		evalBlock[T](timingState, control.body, {
			case f: Failed[_] => 
				reportTime()
				cont(f)
			case su@(Success(updatedState, isReturnValue)) =>
				reportTime()
				if (isReturnValue) cont(su) 
				else {
					state.collect match {
						case Collect.Zero => 
							cont(success(state.setContext(updatedState.context)))
						case _ : Collect.One => 
							updatedState.reapCollect match {
								case TupleValue(value, _) if !value.isEmpty =>
									val c = Collect.One(Some(value(value.size - 1)))
									cont(success(state.setContext(updatedState.context).setCollect(c)))
								case _ => 
									cont(fail(control, "timeit did not yield a value"))
							}
						case _ : Collect.Multiple => 
							cont(success(state.subsume(updatedState)))
					}
				}
		})
	}

	type Matchings = Map[String, StateValue]

	def matchPattern[T](state : State, pat : Pattern, value : StateValue, cont : RC[Option[Matchings], T]) : Thunk[T] = {
		matchPatternCont[T](state, pat, value, Map(), cont)
	}

	def matchPatternCont[T](state : State, pat : Pattern, value : StateValue, matchings : Matchings,
		cont : RC[Option[Matchings], T]) : Thunk[T] = 
	{
		pat match {
			case PAny => cont(success(Some(matchings)))
			case PNil =>
				value match {
					case NilValue => cont(success(Some(matchings)))
					case _ => cont(success(None))
				}
			case PId(name) => 
				matchings.get(name) match {
					case None => cont(success(Some(matchings + (name -> value))))
					case Some(_) => cont(fail(pat, "pattern is not linear, multiple use of: "+name))
				}
			case PInt(x) =>
				value match {
					case IntValue(y) if x == y => cont(success(Some(matchings)))
					case _ => cont(success(None))
				}
			case PBool(x) =>
				value match {
					case BoolValue(y) if x == y => cont(success(Some(matchings)))
					case _ => cont(success(None))
				}
			case PString(xs) =>
				value match {
					case StringValue(ys) if xs == ys => cont(success(Some(matchings)))
					case _ => cont(success(None))
				}
			case PTuple(ps) =>
				value match {
					case TupleValue(xs, _) if xs.size == ps.size =>
						matchPatterns[T](state, ps, xs, matchings, cont)
					case _ => cont(success(None))
				}
			case PPrepend(p, ps) =>  
				value match {
					case TupleValue(xs, comparable) if !xs.isEmpty =>
						matchPatternCont[T](state, p, xs.head, matchings, {
							case Success(Some(matchings), _) => 
								val tail = xs.tail
								val c = 
									if (comparable || xs.head.isComparable)
										comparable
									else
										tail.forall(x => x.isComparable)
								matchPatternCont[T](state, ps, TupleValue(tail, c), matchings, cont) 
							case r => cont(r)
						})
					case _ => cont(success(None))
				}
			case PAppend(ps, p) =>
				value match {
					case TupleValue(xs, comparable) if !xs.isEmpty =>
						matchPatternCont[T](state, p, xs.last, matchings, {
							case Success(Some(matchings), _) => 
								val prefix = xs.take(xs.size - 1)
								val c = 
									if (comparable || xs.last.isComparable)
										comparable
									else
										prefix.forall(x => x.isComparable)
								matchPatternCont[T](state, ps, TupleValue(prefix, c), matchings, cont) 
							case r => cont(r)
						})
					case _ => cont(success(None))
				}	
			case PIf(p, cond) =>
				matchPattern[T](state, p, value, {
					case Success(Some(pMatchings), _) =>
						pMatchings.find(m => matchings.contains(m._1)) match {
							case Some(m) => cont(fail(p, "pattern is not linear, multiple use of: "+m._1))
							case None =>
								evalExpr[T](state.bind(pMatchings).freeze, cond, {
									case failed : Failed[_] => cont(fail(failed))
									case Success(BoolValue(false), _) => cont(success(None))
									case Success(BoolValue(true), _) => cont(success(Some(matchings ++ pMatchings)))
									case Success(v, _) => cont(fail(cond, "Boolean expected, found: "+display(state, v)))
								})							
						}
					case r => cont(r)
				})
			case PAs(p, name) =>
				matchPatternCont[T](state, p, value, matchings, {
					case Success(Some(matchings), _) =>
						matchings.get(name) match {
							case None => cont(success(Some(matchings + (name -> value))))
							case Some(v) => cont(fail(pat, "pattern is not linear, multiple use of: "+v))
						}
					case r => cont(r)
				})
			case PType(p, valuetype) =>
				matchValueType(state, value, valuetype) match {
					case Left(false) => cont(success(None))
					case Left(true) => matchPatternCont[T](state, p, value, matchings, cont)
					case Right(error) => cont(fail(valuetype, "invalid type pattern: " + error))
				}
			case PConstr(name, arg) =>
				val ns = name.namespace
				val n = name.name.toString
				lookupId(pat, state, ns, n) match {
					case failed : Failed[_] => cont(fail(pat, "unknown constructor: " + name))	
					case Success(constr, _) =>
						(constr, arg) match {
							case (c : ConstrValue, None) =>
								if (c == value) 
									cont(success(Some(matchings)))
								else 
									cont(success(None))
							case (c : ConstrUnappliedValue, Some(arg)) =>
								value match {
									case v : ConstrAppliedValue if v.name == c.name && v.customtype == c.customtype =>
										matchPatternCont[T](state, arg, v.param, matchings, cont)
									case _ => 
										cont(success(None))
								}
							case _ => cont(fail(pat, "invalid constructor pattern"))
						}
				}
			case PDestruct(name, arg) =>
				value match {
					case c: ConstrAppliedValue =>
						matchPatternCont[T](state, arg, c.param, matchings, {
							case Success(Some(matchings), _) =>
								matchings.get(name) match {
									case None => 
										val constr = ConstrUnappliedValue(c.name, c.customtype)
										cont(success(Some(matchings + (name -> constr))))
									case Some(_) => cont(fail(pat, "pattern is not linear, multiple use of: " + name))
								}
							case result => cont(result)
						})
					case _ => cont(success(None))
				}
			case PLogicTerm(_preterm) =>
				evalLogicPreterm(state.freeze, _preterm, {
					case failed : Failed[_] => cont(fail(failed))
					case Success(_preterm, _) =>
						val term_ : CTerm = 
							value match {
								case TermValue(value) => value
								case TheoremValue(thm) => state.context.lift(thm).prop
								case s : StringValue =>
									try {
										Syntax.parseCTerm(aliases, logicNameresolution, state.context, s.toString)
									} catch {
										case ex : Utils.KernelException =>
											return cont(success(None))
									}
								case _ => return cont(success(None))
							}
						val optTerm = state.context.autolift(term_)
						if (optTerm.isEmpty) return cont(fail(pat, "cannot automatically lift term into context: " + display(state, TermValue(term_))))
						val term = optTerm.get
						val tc = Preterm.obtainTypingContext(aliases, logicNameresolution, state.context)
						val (preterm, typeQuotes, typesOfTypeQuotes) = 
							Preterm.inferPattern(tc, _preterm) match {
								case Left(result) => result
								case Right(errors) => 
									var erroroutput = errors.mkString("\n")
									if (errors.size <= 1)
										return cont(fail(pat, "ill-typed pattern: " + erroroutput))
									else
										return cont(fail(pat, "ill-typed pattern:\n" + erroroutput))
							}
						val (hop, quotes) = HOPattern.preterm2HOP(tc, preterm)
						HOPattern.patternMatch(state.context, hop, term) match {
							case Right(invalid) => 
								if (invalid) cont(fail(pat, "pattern is not a higher-order pattern"))
								else cont(success(None))
							case Left((subst, typeSubst)) => 
								val f = typeSubst.get _
								val types = typesOfTypeQuotes.mapValues(pretype => Pretype.translate(Pretype.subst(f, pretype)))
								def loop(idTerms : Seq[(Utils.Integer, CTerm)], matchings : Matchings) : Thunk[T] = {
									if (idTerms.isEmpty)
										cont(success(Some(matchings)))
									else {
										val (quoteId, term) = idTerms.head
										val value = TermValue(term)
										val p = quotes(quoteId).quoted.asInstanceOf[Pattern]
										matchPatternCont[T](state, p, value, matchings, {
											case Success(Some(matchings_q), _) => loop(idTerms.tail, matchings_q)
											case r => cont(r)
										})																
									}
								}
								def loopTypes(idTypes : Seq[(Utils.Integer, Type)], matchings : Matchings) : Thunk[T] = {
									if (idTypes.isEmpty)
										loop(subst.toSeq, matchings)
									else {
										val (quoteId, ty) = idTypes.head
										val value = TypeValue(ty)
										val p = typeQuotes(quoteId).quoted.asInstanceOf[Pattern]
										matchPatternCont[T](state, p, value, matchings, {
											case Success(Some(matchings_q), _) => loopTypes(idTypes.tail, matchings_q)
											case r => cont(r)
										})																
									}
								}						
								loopTypes(types.toSeq, matchings)
						}
				})
			case PLogicType(pretype) =>
				evalLogicPretype(state.freeze, pretype, {
					case failed : Failed[_] => cont(fail(failed))
					case Success(pretype, _) =>
						value match {
							case TypeValue(ty) => 
								val (pat, quotes) = Pretype.pretype2Pattern(pretype)
								Pretype.patternMatch(pat, ty) match {
									case None => cont(success(None))
									case Some(subst) =>
										def loop(idTypes : Seq[(Utils.Integer, Type)], matchings : Matchings) : Thunk[T] = {
											if (idTypes.isEmpty)
												cont(success(Some(matchings)))
											else {
												val (quoteId, ty) = idTypes.head
												val value = TypeValue(ty)
												val quote = quotes.get(quoteId)
												if (quote.isDefined) {
													val p = quote.get.quoted.asInstanceOf[Pattern]
													matchPatternCont[T](state, p, value, matchings, {
														case Success(Some(matchings_q), _) => loop(idTypes.tail, matchings_q)
														case r => cont(r)
													})							
												}	else {
													loop(idTypes.tail, matchings)
												}								
											}
										}
										loop(subst.toSeq, matchings)								
								}
							case _ => cont(success(None))
						}
				})
			case PError(msg) => cont(fail(pat, "invalid pattern: " + msg))
			case _ => cont(fail(pat, "pattern has not been implemented yet"))
		}		
	}

	def matchValueType(state : State, value : StateValue, valuetype : ParseTree.ValueType) : Either[Boolean, String] = {
		(value, valuetype) match {
			case (_, TyAny) => Left(true)
			case (NilValue, TyNil) => Left(true)
			case (NilValue, TyOption(_)) => Left(true)
			case (value, TyOption(vty)) => matchValueType(state, value, vty)
			case (value, TyUnion(vty1, vty2)) => 
				matchValueType(state, value, vty1) match {
					case Left(false) =>
						matchValueType(state, value, vty2)
					case result =>
						result
				}
			case (_ : ContextValue, TyContext) => Left(true)
			case (_ : TheoremValue, TyTheorem) => Left(true)
			case (_ : TermValue, TyTerm) => Left(true)
			case (_ : TypeValue, TyType) => Left(true)
			case (_ : BoolValue, TyBoolean) => Left(true)
			case (_ : IntValue, TyInteger) => Left(true)
			case (_ : StringValue, TyString) => Left(true)
			case (_ : TupleValue, TyTuple) =>	Left(true)	
			case (_ : MapValue, TyMap) => Left(true)
			case (_ : SetValue, TySet) =>	Left(true)
			case (f, TyFunction) if StateValue.isFunction(f) => Left(true)
			case (f, ty : TyCustom) => 
				resolveCustomType(state, ty.namespace, ty.name) match {
					case None => 
						val typename = if (ty.namespace.isDefined) ty.namespace.get.append(ty.name).toString else ty.name
						Right("unknown type " + typename)
					case Some(ty) => Left(matchCustomType(f, ty)) 
				}
			case _ => Left(false)
		}
	}

	def resolveCustomType(state : State, ns : Option[Namespace], name : String) : Option[CustomType] = {
		def make(namespaces : Set[Namespace]) : Option[CustomType] = {
			namespaces.size match {
				case 1 => completedStates(namespaces.head).get.env.types.get(name)
				case _ => None
			}
		}
		if (ns.isEmpty) {
			state.env.types.get(name) match {
				case s : Some[CustomType] => s
				case None => make(scriptTyperesolution.baseResolution(namespace)(name))
			}
		} else {
			val _ns = aliases.resolve(ns.get)
			if (_ns == namespace) resolveCustomType(state, None, name)
			else {
				make(scriptTyperesolution.fullResolution(_ns)(name))
			}
		}
	}

	def matchCustomType(value : StateValue, customtype : CustomType) : Boolean = {
		value match {
			case c : ConstrValue => c.customtype == customtype
			case c : ConstrAppliedValue => c.customtype == customtype
			case _ => false
		}
	}

	private def toSetValue(seq : Seq[StateValue]) : Option[SetValue] = {
		if (seq.forall(x => x.isComparable))
			Some(SetValue(seq.toSet))
		else 
			None
	}
	private def asSeq(value : SetValue) : Seq[StateValue] = value.value.toSeq

	private def toTupleValue(seq : Seq[StateValue]) : Option[TupleValue] = {
		val comparable = seq.forall(x => x.isComparable)
		Some(TupleValue(seq.toVector, comparable))
	}
	private def asSeq(value : TupleValue) : Seq[StateValue] = value.value.toSeq

	private def toMapValue(seq : Seq[StateValue]) : Option[MapValue] = {
		var m : Map[StateValue, StateValue] = Map()
		var comparable = true
		for (elem <- seq) {
			elem match {
				case TupleValue(Vector(k, v), _) =>
					if (!k.isComparable) return None
					comparable = comparable && v.isComparable
					m = m + (k -> v)
				case _ => return None
			}
		}
		Some(MapValue(m, comparable))
	}
	private def asSeq(value : MapValue) : Seq[StateValue] = 
		value.value.toSeq.map({case (k, v) => TupleValue(Vector(k, v), v.isComparable)})

	def convertValueType(state : State, value : StateValue, valuetype : ParseTree.ValueType) : Option[StateValue] = {
		import StateValue.mkStringValue
		(value, valuetype) match {
			case (_, TyAny) => Some(value)
			case (NilValue, TyNil) => Some(value)
			case (NilValue, TyOption(_)) => Some(value)
			case (value, TyOption(vty)) => convertValueType(state, value, vty)
			case (value, TyUnion(vty1, vty2)) =>
				convertValueType(state, value, vty1) match {
					case None =>
						convertValueType(state, value, vty2)
					case result =>
						result
				}
			case (_ : ContextValue, TyContext) => Some(value)
			case (_ : TheoremValue, TyTheorem) => Some(value)
			case (_ : TermValue, TyTerm) => Some(value)
			case (_ : TypeValue, TyType) => Some(value)
			case (_ : BoolValue, TyBoolean) => Some(value)
			case (_ : IntValue, TyInteger) => Some(value)
			case (f, TyFunction) if StateValue.isFunction(f) => Some(value)
			case (_ : StringValue, TyString) => Some(value)
			case (_ : TupleValue, TyTuple) =>	Some(value)	
			case (_ : MapValue, TyMap) => Some(value)
			case (_ : SetValue, TySet) =>	Some(value)
			case (IntValue(i), TyString) => Some(mkStringValue(i.toString))
			case (TypeValue(ty), TyString) => Some(mkStringValue(Syntax.printType(ty)))
			case (TermValue(tm), TyString) => 
				state.context.autolift(tm) match {
					case None => None
					case Some(tm) => 
						Some(mkStringValue(Syntax.checkprintTerm(aliases, logicNameresolution, state.context, tm)))				
				}
			case (TheoremValue(thm), TyString) =>
				try {
					val liftedTh = state.context.lift(thm)
					val tm = liftedTh.proposition
					Some(mkStringValue(Syntax.checkprintTerm(aliases, logicNameresolution, state.context, tm)))					
				} catch {
					case _ : Utils.KernelException => None
				}
			case (s : StringValue, TyInteger) =>
			  try {
			    val i = BigInt(s.toString, 10)
			    Some(IntValue(i))
			  } catch {
			    case e:Exception => None
			  }	
			case (s : StringValue, TyType) => 
				try {
					Syntax.parsePretype(s.toString) match {
						case None => None
						case Some(ty) => Some(TypeValue(Pretype.translate(ty)))
					}
				} catch {
					case _ : Utils.KernelException => None					
				}
			case (tm : TermValue, TyType) => 
				try {
					state.context.autolift(tm.value) match {
						case None => None
						case Some(tm) => Some(TypeValue(tm.typeOf))
					}
				} catch {
					case _ : Utils.KernelException => None
				}							
			case (s : StringValue, TyTerm) =>
				try {
					Some(TermValue(Syntax.parseCTerm(aliases, logicNameresolution, state.context, s.toString)))
				} catch {
					case _ : Utils.KernelException => None
				}				
			case (thm : TheoremValue, TyTerm) => 
				try {
					val liftedThm = state.context.lift(thm.value)
					val tm = liftedThm.prop
					Some(TermValue(tm))					
				} catch {
					case _ : Utils.KernelException => None
				}			
			case (v : TupleValue, TySet) => toSetValue(asSeq(v))
			case (v : TupleValue, TyMap) => toMapValue(asSeq(v))
			case (v : SetValue, TyTuple) => toTupleValue(asSeq(v))
			case (v : SetValue, TyMap) => toMapValue(asSeq(v))
			case (v : MapValue, TyTuple) => toTupleValue(asSeq(v))
			case (v : MapValue, TySet) => toSetValue(asSeq(v))
			case (f, ty : TyCustom) => 
				resolveCustomType(state, ty.namespace, ty.name) match {
					case None => None
					case Some(ty) => if (matchCustomType(f, ty)) Some(f) else None 
				}
			case _ => None
		}
	}

	def matchPatterns[T](state : State, pats : Seq[Pattern], values : Seq[StateValue], matchings : Matchings,
		cont : RC[Option[Matchings], T]) : Thunk[T] = 
	{
		if (pats.isEmpty || values.isEmpty) {
			if (pats.isEmpty && values.isEmpty)
				cont(success(Some(matchings)))
			else
				cont(success(None))
		} else {
			matchPatternCont[T](state, pats.head, values.head, matchings, {
				case Success(Some(m), _) => matchPatterns[T](state, pats.tail, values.tail, m, cont)
				case r => cont(r)
			})			
		}
	}

}
