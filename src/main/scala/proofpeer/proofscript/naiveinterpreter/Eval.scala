package proofpeer.proofscript.naiveinterpreter

import proofpeer.proofscript.frontend._
import proofpeer.proofscript.logic._
import ParseTree._

sealed trait Result[T]
case class Success[T](result : T, isReturnValue : Boolean) extends Result[T]
case class Failed[T](pos : SourcePosition, error : String) extends Result[T]

class Eval(states : States, kernel : Kernel, 
	scriptNameresolution : NamespaceResolution[String], 
	val logicNameresolution : NamespaceResolution[IndexedName], 
	val aliases : Aliases, namespace : Namespace) 
{

	def success[T](result : T) : Success[T] = Success(result, false)

	def fail[T](p : TracksSourcePosition, error : String) : Failed[T] = Failed(p.sourcePosition, error)

	def fail[S,T](f : Failed[S]) : Failed[T] = Failed(f.pos, f.error)

	def evalLogicPreterm(state : State, tm : LogicTerm) : Result[Preterm] = {
		def inst(tm : Preterm.PTmQuote) : Either[Preterm, Failed[StateValue]] = {
			tm.quoted match {
				case expr : Expr =>
					evalExpr(state, expr) match {
						case failed : Failed[_] => Right(failed)
						case Success(TermValue(t), _) => Left(Preterm.translate(t))
						case Success(s : StringValue, _) =>
							Syntax.parsePreterm(s.toString) match {
								case None => Right(fail(expr, "parse error"))
								case Some(preterm) => Left(preterm)
							}
						case Success(v, _) => Right(fail(expr, "term value expected, found: " + display(state, v)))
					}    	
			}
		}
		Preterm.instQuotes(inst, tm.tm) match {
		  case Right(f) => fail(f)
			case Left(preterm) => success(preterm)
		}
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

	def evalLogicTerm(state : State, tm : LogicTerm) : Result[Term] = {
		evalLogicPreterm(state, tm) match {
			case failed : Failed[_] => fail(failed)
			case Success(preterm, _) => resolvePreterm(state.context, preterm)
		}
	} 

	def evalTermExpr(state : State, expr : Expr) : Result[Term] = {
		evalExpr(state, expr) match {
			case failed : Failed[_] => fail(failed)
			case Success(TermValue(tm),_) => success(tm)
			case Success(s : StringValue, _) =>
				try {
					success(Syntax.parseTerm(aliases, logicNameresolution, state.context, s.toString)) 
				} catch {
					case ex : Utils.KernelException =>
						fail(expr, "parse error: " + ex.reason)	
				}
			case Success(v, _) => fail(expr, "Term expected, found: "+display(state, v))
		}
	}

	def evalPretermExpr(state : State, expr : Expr) : Result[Preterm] = {
		expr match {
			case tm : LogicTerm => evalLogicPreterm(state, tm)
			case _ => 
				evalExpr(state, expr) match {
					case failed : Failed[_] => fail(failed)
					case Success(TermValue(tm),_) => success(Preterm.translate(tm))
					case Success(s : StringValue, _) =>
						Syntax.parsePreterm(s.toString) match {
							case None => fail(expr, "parse error")
							case Some(preterm) => success(preterm)
						}
					case Success(v, _) => fail(expr, "Preterm expected, found: "+display(state, v))
				}
		}
	}

	def display(state : State, value : StateValue) : String = {
		StateValue.display(aliases, logicNameresolution, state.context, value)	
	}

	def evalBlock(_state : State, block : Block) : Result[State] = {
		val statements = block.statements
		var state = _state
		val num = statements.size
		var i = 0
		for (st <- statements) {
			st match {
				case STValIntro(ids) =>
					if (ids.toSet.size != ids.size)
						return fail(st, "cannot introduce the same variable more than once")
					else 
						for (id <- ids) state = state.bind(Map(id.name -> NilValue))
				case STVal(pat, body) => 
					evalBlock(state.setCollect(Collect.emptyOne), body) match {
						case f : Failed[_] => return fail(f)
						case su @ Success(s, isReturnValue) => 
							if (isReturnValue) return su
							val value = s.reapCollect
							state = state.setContext(s.context)
							matchPattern(state.freeze, pat, value) match {
								case Failed(pos, error) => return Failed(pos, error)
								case Success(None, _) => return fail(pat, "value " + display(state, value) + " does not match pattern")
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
								case Success(None, _) => return fail(pat, "value " + display(state, value) + " does not match pattern")
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
					expr match {
						case None => return Success(State.fromValue(NilValue), true)
						case Some(expr) =>
							evalExpr(state.freeze, expr) match {
								case f : Failed[_] => return fail(f)
								case Success(s, _) => return Success(State.fromValue(s), true)
							}						
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
							println("** show ("+namespace+location+"): "+display(state, value))
					}
				case STFail(None) => return fail(st, "fail")
				case STFail(Some(expr)) =>
					evalExpr(state.freeze, expr) match {
						case f : Failed[_] => return fail(f)
						case Success(value, _) => return fail(st, "fail: "+display(state, value))
					}		
				case STAssert(expr) =>
					evalExpr(state.freeze, expr) match {
						case f : Failed[_] => return fail(f)
						case Success(BoolValue(true), _) => // do nothing
						case Success(BoolValue(false), _) => return fail(st, "Assertion does not hold")
						case Success(value, _) => return fail(st, "Assertion does not hold: " + display(state, value))
					}
				case STFailure(block) =>
					evalBlock(state.freeze.setCollect(Collect.emptyMultiple), block) match {
						case f : Failed[_] => 
							val location : String = 
								st.sourcePosition.span match {
									case None => ""
									case Some(span) => ":" + (span.firstRow + 1)
								}						
							println("** failure intercepted ("+namespace+location+"): "+f.error)
						case Success(newState, _) =>
							val value = newState.reapCollect 
							return fail(st, "Failure expected, but evaluates successfully to: " + display(state, value))
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
				case stdef : STDef =>
					lookupVars(state, stdef.freeVars) match {
						case Right(xs) =>
							var error = "definition depends on unknown free variables:"
							for (x <- xs) error = error + " " + x
							return fail(stdef, error)
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
							state = state.bind(functions)
					}
				case st if isLogicStatement(st) => 
					evalLogicStatement(state, st) match {
						case f : Failed[_] => return fail(f)
						case Success((_state, name, value), isReturnValue) =>
							if (isReturnValue) return Success(_state, true)
							state = _state
							if (name.isDefined) state = state.bind(Map(name.get -> value))
							if (i == num - 1) 
								state.collect match {
									case _ : Collect.One => state = state.addToCollect(value)
									case _ => // do nothing
								}
					}
				case _ : STComment => // ignore comment and do nothing
				case _ => return fail(st, "statement has not been implemented yet: "+st)
			}
			i = i + 1
		}
		state.collect match {
			case Collect.One(None) => fail(block, "block does not yield a value") 
			case _ => success(state)
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

	def evalLogicStatement(state : State, st : Statement) : Result[(State, Option[String], StateValue)] = {
		st match {
			case STAssume(thm_name, tm) =>
				evalTermExpr(state.freeze, tm) match {
					case failed : Failed[_] => fail(failed)
					case Success(tm, _) =>
						try {
							val thm = state.context.assume(tm)
							success((state.setContext(thm.context), thm_name, new TheoremValue(thm)))
						} catch {
							case ex : Utils.KernelException =>
								fail(st, "assume: "+ex.reason)
						}
				}
			case st @ STLet(thm_name, tm) =>
				evalPretermExpr(state.freeze, tm) match {
					case failed : Failed[_] => fail(failed)
					case Success(ptm, _) =>
						checkTypedName(ptm) match {
							case None => 
								letIsDef(ptm) match {
									case None =>
										fail(st, "let can only handle introductions or simple definitions")
									case Some((n, tys, right)) => evalLetDef(state, st, ptm, n, tys, right)
								}
							case Some((n, tys)) => evalLetIntro(state, st, n, tys) 
						}
				}
			case STChoose(thm_name, tm, proof) =>
				evalPretermExpr(state.freeze, tm) match {
					case failed : Failed[_] => fail(failed)
					case Success(ptm, _) =>
						checkTypedName(ptm) match {
							case None => fail(tm, "name expected")
							case Some((n, tys)) =>
								if (n.namespace.isDefined) return fail(tm, "choose: constant must not have explicit namespace")
								val name = Name(Some(state.context.namespace), n.name)
								evalProof(state, proof) match {
									case failed : Failed[_] => fail(failed)
									case Success(value, true) => 
										Success((State.fromValue(value), thm_name, value), true)	
									case Success(TheoremValue(thm), _) =>
										try {
											val liftedThm = state.context.lift(thm, false)
											val chosenThm = state.context.choose(name, liftedThm)
											val ty = chosenThm.context.typeOfConst(name).get
											if (!Pretype.solve(Pretype.translate(ty) :: tys).isDefined) 
												return fail(st, "declared type of constant does not match computed type")
											success((state.setContext(chosenThm.context), thm_name, TheoremValue(chosenThm)))
										}	catch {
											case ex : Utils.KernelException =>
												return fail(st, "choose: " + ex.reason)
										}	
									case Success(v, _) => fail(proof, "Theorem expected, found: " + display(state, v))
								} 
						}
				}
			case STTheorem(thm_name, tm, proof) =>
				evalTermExpr(state.freeze, tm) match {
					case f : Failed[_] => fail(f)
					case Success(prop, _) =>
						if (state.context.typeOfTerm(prop) != Some(Type.Prop)) 
							return fail(tm, "Proposition expected, found: " + display(state, TermValue(prop)))
						evalProof(state, proof) match {
							case f : Failed[_] => fail(f)
							case Success(value, true) => 
								Success((State.fromValue(value), thm_name, value), true)
							case Success(TheoremValue(thm), _) =>
								try {
									val ctx = state.context
									var liftedThm = ctx.lift(thm, false)
									if (!KernelUtils.betaEtaEq(prop, liftedThm.proposition)) {
										val liftedThm2 = ctx.lift(thm, true)
										if (!KernelUtils.betaEtaEq(prop, liftedThm2.proposition)) 
											return fail(proof, "Proven theorem does not match: " + display(state, TheoremValue(liftedThm)))
										liftedThm = liftedThm2
									}
									success((state, thm_name, TheoremValue(ctx.normalize(liftedThm, prop))))
								} catch {
									case ex: Utils.KernelException => return fail(st, "theorem: " + ex.reason)
								}
							case Success(v, _) => fail(proof, "Theorem expected, found: " + display(state, v))
						}
				}
			case _ =>
				fail(st, "internal error: statement is not a logic statement")
		}
	}

	def evalProof(state : State, proof : Block) : Result[StateValue] = {
		evalBlock(state.setCollect(Collect.emptyOne), proof) match {
			case f : Failed[_] => fail(f)
			case Success(state, isReturnValue) => Success(state.reapCollect, isReturnValue)
		}
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
						success(states.lookup(ns).get.lookup(name).get)
					case n =>
						var display = ""
						for (ns <- namespaces) display = display + ns + " "
						fail(p, "ambiguous identifier " + name + ", defined in "+n+" different namespaces: "+display)
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

	def evalExpr(state : State, expr : Expr) : Result[StateValue] = {
		expr match {
			case NilExpr => success(NilValue)
			case Bool(b) => success(BoolValue(b))
			case Integer(i) => success(IntValue(i))
			case StringLiteral(s) => success(StringValue(s))
			case Id(name) =>
				state.lookup(name) match {
					case None => lookupVar(expr, state, false, namespace, name)
					case Some(v) => success(v)
				}
			case QualifiedId(_ns, name) =>
				val ns = aliases.resolve(_ns)
				if (scriptNameresolution.ancestorNamespaces(namespace).contains(ns))
					lookupVar(expr, state, true, ns, name)
				else 
					fail(expr, "unknown or inaccessible namespace: "+ns)
			case UnaryOperation(op, expr) =>
				evalExpr(state, expr) match {
					case Success(value, _) =>
						(op, value) match {
							case (Not, BoolValue(b)) => success(BoolValue(!b)) 
							case (Neg, IntValue(i)) => success(IntValue(-i))
							case _ => fail(op, "unary operator "+op+" cannot be applied to: "+display(state, value))
						}
					case f => f
				}
			case BinaryOperation(op, left, right) if op != And && op != Or =>
				evalExpr(state, left) match {
					case Success(left, _) =>
						evalExpr(state, right) match {
							case Success(right, _) =>
								(op, left, right) match {
									case (RangeTo, IntValue(x), IntValue(y)) => 
										success(TupleValue((x to y).map(i => IntValue(i)).toVector))
									case (RangeDownto, IntValue(x), IntValue(y)) => 
										success(TupleValue((y to x).reverse.map(i => IntValue(i)).toVector))
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
									case (Concat, xs : StringValue, ys : StringValue) => success(xs.concat(ys))
									case _ => fail(op, "binary operator "+op+" cannot be applied to values: "+
										display(state,left)+", "+display(state,right))
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
							case Success(v, _) => fail(right, "Boolean expected, found: " + display(state, v))
							case f => f
						}
					case Success(v, _) => fail(left, "Boolean expected, found: " + display(state, v))
					case f => f
				}
			case BinaryOperation(Or, left, right) =>
				evalExpr(state, right) match {
					case Success(v @ BoolValue(true), _) => success(v)
					case Success(BoolValue(false), _) => 
						evalExpr(state, right) match {
							case su @ Success(_ : BoolValue, _) => su
							case Success(v, _) => fail(right, "Boolean expected, found: " + display(state, v))
							case f => f
						}					
					case Success(v, _) => fail(left, "Boolean expected, found: " + display(state, v))
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
									cmp(state, operators.head, value, v) match {
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
			case f @ Fun(param, body) => 
				lookupVars(state, f.freeVars) match {
					case Right(notFound) =>
						var error = "function has unknown free variables:"
						for (x <- notFound) error = error + " " + x
						fail(f, error)
					case Left(nonlinear) =>
						val funstate = new State(state.context, State.Env(nonlinear, Map()), Collect.emptyOne, true)
						success(SimpleFunctionValue(funstate, f))
				}
			case App(u, v) =>
				evalExpr(state, u) match {
					case failed : Failed[_] => failed
					case Success(f : SimpleFunctionValue, _) =>
						evalExpr(state, v) match {
							case failed : Failed[_] => failed
							case Success(x, _) => evalApply(f.state, f.f.param, f.f.body, x)
						}
					case Success(f : RecursiveFunctionValue, _) =>
						evalExpr(state, v) match {
							case failed : Failed[_] => failed
							case Success(x, _) => evalApply(f.state, f.cases, x)
						}
					case Success(f : NativeFunctionValue, _) =>
						evalExpr(state, v) match {
							case failed : Failed[_] => failed
							case Success(x, _) => 
								f.nativeFunction(this, state, x) match {
									case Left(value) => success(value)
									case Right(error) => fail(expr, error)
								}
						}
					case Success(StringValue(s), _) =>
						evalExpr(state, v) match {
							case failed : Failed[_] => failed
							case Success(IntValue(i), _) =>
								if (i < 0 || i >= s.size) fail(v, "index " + i + " is out of bounds")
								else success(StringValue(Vector(s(i.toInt))))
							case Success(TupleValue(indices), _) =>
								val len = s.size
								var codes : List[Int] = List()
								for (index <- indices) {
									index match {
										case IntValue(i) =>
											if (i < 0 || i >= len) return fail(v, "index " + i + " is out of bounds")
											else codes = s(i.toInt) :: codes
										case _ =>
											return return fail(v, "index expected, found: " + display(state, index))
									}
								}
								success(StringValue(codes.reverse.toVector))
							case Success(value, _) =>
								fail(v, "string cannot be applied to: " + display(state, value))
						}
					case Success(TupleValue(s), _) =>
						evalExpr(state, v) match {
							case failed : Failed[_] => failed
							case Success(IntValue(i), _) =>
								if (i < 0 || i >= s.size) fail(v, "index " + i + " is out of bounds")
								else success(s(i.toInt))
							case Success(TupleValue(indices), _) =>
								val len = s.size
								var values : List[StateValue] = List()
								for (index <- indices) {
									index match {
										case IntValue(i) =>
											if (i < 0 || i >= len) return fail(v, "index " + i + " is out of bounds")
											else values = s(i.toInt) :: values
										case _ =>
											return return fail(v, "index expected, found: " + display(state, index))
									}
								}
								success(TupleValue(values.reverse.toVector))
							case Success(value, _) =>
								fail(v, "string cannot be applied to: " + display(state, value))
						}					
					case Success(v, _) => fail(u, "value cannot be applied to anything: " + display(state, v))
				}
			case tm : LogicTerm =>
				evalLogicTerm(state, tm) match {
					case f : Failed[_] => fail(f)
					case Success(tm, _) => success(TermValue(tm))
				}
			case Lazy(_) => fail(expr, "lazy evaluation is not available (yet)")
			case _ => fail(expr, "don't know how to evaluate this expression")
		}	
	}

	def evalApply(state : State, pat : Pattern, body : Block, argument : StateValue) : Result[StateValue] = {
		matchPattern(state.freeze, pat, argument) match {
			case failed : Failed[_] => fail(failed)
			case Success(None, _) => fail(pat, "pattern does not match function argument: " + display(state, argument))
			case Success(Some(matchings), _) =>
				evalBlock(state.bind(matchings), body) match {
					case failed : Failed[_] => fail(failed)
					case Success(state, _) => success(state.reapCollect)
				}
		}
	}

	def evalApply(state : State, cases : Vector[DefCase], argument : StateValue) : Result[StateValue] = {
		val matchState = state.freeze
		for (c <- cases) {
			matchPattern(matchState, c.param, argument) match {
				case failed : Failed[_] => return fail(failed)
				case Success(None, _) =>
				case Success(Some(matchings), _) =>
					evalBlock(state.bind(matchings), c.body) match {
						case failed : Failed[_] => return fail(failed)
						case Success(state, _) => return success(state.reapCollect)
					}
			}
		}
		val c = cases.head
		fail(c.param, "function " + c.name + " cannot be applied to: " + display(state, argument))
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
			case c : ContextControl => evalContextControl(state, c)
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
			case Success(value, _) => fail(control.cond, "Boolean expected, found: " + display(state, value))
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
				fail(control, "no match for value: " + display(state, value))
		}	
	}

	def evalContextControl(state : State, control : ContextControl) : Result[State] = {
		val context =
			control.ctx match {
				case None => state.context
				case Some(expr) =>
					evalExpr(state.freeze, expr) match {
						case failed : Failed[_] => return fail(failed)
						case Success(ContextValue(context), _) => context
						case Success(TheoremValue(thm), _) => thm.context
						case Success(v, _) => return fail(expr, "context or theorem expected, found: " + display(state, v))
					}
			}
		evalBlock(state.setContext(context).setCollect(Collect.Zero), control.body) match {
			case failed : Failed[_] => failed
			case su @ Success(updatedState, isReturnValue) =>
				if (isReturnValue) return su 	
				state.collect match {
					case _ : Collect.One =>
						success(state.addToCollect(ContextValue(updatedState.context)))
					case _ => 
						success(state)
				}
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
						evalExpr(state.bind(pMatchings).freeze, cond) match {
							case failed : Failed[_] => fail(failed)
							case Success(BoolValue(false), _) => success(None)
							case Success(BoolValue(true), _) => success(Some(matchings ++ pMatchings))
							case Success(v, _) => fail(cond, "Boolean expected, found: "+display(state, v))
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
						case Right(errors) => return fail(pat, "ill-typed pattern")
					}
				val (hop, quotes) = HOPattern.preterm2HOP(tc, preterm)
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