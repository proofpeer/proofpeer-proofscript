package proofpeer.proofscript.naiveinterpreter

import java.io.File
import proofpeer.proofscript.frontend._
import proofpeer.proofscript.logic._

object Interpreter {

	val MAX_TRACE_LENGTH = 1000

	class FileSource(val f : File) extends Source {
		override def toString : String = {
			return f.toString
		}
	}

	var numTheories = 0

	var processed : Set[String] = Set()

	def addTheory(f : File) {
		if (f.exists) {
			val fileid = f.getAbsolutePath()
			if (processed.contains(fileid)) return
			processed = processed + fileid
			println("processing theory file: "+f)
			numTheories = numTheories + 1
			val source = scala.io.Source.fromFile(f)
			val code = source.getLines.mkString("\n")
			source.close()
			val t1 = System.currentTimeMillis
			val result = Parser.parseFromSource(new FileSource(f), code)
			val t2 = System.currentTimeMillis
			println("  parsed in " + (t2 - t1) + "ms")
			result match {
				case Parser.SuccessfulParse(tree) =>
					addTheory(f, tree)
				case Parser.AmbiguousParse(pos) =>
					println("  cannot add theory, ambiguous parse tree")
				case Parser.FailedParse(pos) =>
					println("  cannot add theory, parse error at:")
					if (pos.span.isDefined) {
						val span = pos.span.get
						println("  row = "+(span.firstRow + 1)+", column = "+(span.leftMostFirst + 1))
					} else {
						println("  unknown position")
					}
			} 
		} else {
			println("theory file not found: "+f)
		}
	}

	def findTheoriesInDirectory(dir : File) {
		for (f <- dir.listFiles) {
			if (f.isDirectory)
				findTheoriesInDirectory(f)
			else if (f.getName().endsWith(".thy")) 
				addTheory(f)
		}
	}

	case class Theory(source : Source, namespace : Namespace, parents : Set[Namespace], aliases : Aliases, statements : Vector[ParseTree.Statement])

	var theories : Map[Namespace, Theory] = Map()

	def addTheory(f : File, thy : ParseTree.Block) {
		if (thy.statements.isEmpty) {
			println("  theory is empty and will be ignored")
		} else {
			thy.statements.head match {
				case ParseTree.STTheory(namespace, _aliases, parents) =>
					val ns = namespace.absolute
					val aliases = new Aliases(ns.parent.get, _aliases.map(a => Alias(a._1.name, a._2)))
					val ps = parents.map (aliases.resolve(_))
					val theory = Theory(new FileSource(f), ns, ps.toSet, aliases, thy.statements.tail)
					theories.get(ns) match {
						case None =>
							theories = theories + (ns -> theory)
							println("  added theory: "+ns)
						case Some(_) =>
							println("  theory has already been defined, this theory file will be ignored")
					}
				case _ =>
					println("  theory header is missing, theory will be ignored")
			}
		}
	}

	def topsort(theories : Map[Namespace, Theory]) : List[Theory] = {
		var sorted : List[Theory] = List()
		var sortedNamespaces : Set[Namespace] = Set()
		var unsorted : Map[Namespace, Theory] = theories

		def sort(initial : Boolean) : Boolean = {
			var did_something = false
			var sorted_ns = sortedNamespaces
			for ((ns, thy) <- unsorted) {
				if (thy.parents subsetOf sorted_ns) {
					sorted = thy :: sorted
					sortedNamespaces = sortedNamespaces + ns
					unsorted = unsorted - ns	
					did_something = true
				}
				if (!initial) sorted_ns = sortedNamespaces
			}
			did_something
		}

		if (!sort(true)) {
			println("theory graph has no root")
			return List()
		} else if (sorted.size != 1) {
			println("theory graph has more than one root:")
			for (thy <- sorted) {
				println("  " + thy.namespace)
			}
			return List()
		} else if (sorted.head.namespace != Kernel.root_namespace) {
			println("theory graph has invalid root: " + sorted.head.namespace)
			return List()
		} 

		while (sort(false)) {}

		if (!unsorted.isEmpty) { 
			println("these theories have invalid dependencies and will not be processed:")
			for ((ns, _) <- unsorted) {
				println("  " + ns)
			}
		} 

		sorted.reverse
	}

	def rootState : State = {
		val environment : Map[String, StateValue] =
			NativeFunctions.environment.mapValues(v => NativeFunctionValue(v))
		new State(Root.context, State.Env(environment, Map()), Collect.Zero, false)
	}

	def makeState(states : States, namespace : Namespace, parentNamespaces : Set[Namespace], aliases : Aliases) : Option[State] = {
		for (p <- parentNamespaces) {
			if (!states.lookup(p).isDefined) return None
		}
		val context = Root.kernel.createNewNamespace(namespace, parentNamespaces, aliases)
		Some(new State(context, State.Env(Map(), Map()), Collect.Zero, false))
	} 

	var executionSucceeded = 0
	var executionFailed = 0
	var executionSkipped = 0

	def evalTheory(states : States, thy : Theory, nr : NamespaceResolution[String]) {
		val evaluator = new Eval(states, Root.kernel, nr, Root.nr, thy.aliases, thy.namespace)
		val state : State = 
			if (thy.namespace == Kernel.root_namespace) 
				rootState
			else {
				makeState(states, thy.namespace, thy.parents, thy.aliases) match {
					case None =>
						println("skipping theory "+thy.namespace)
						executionSkipped = executionSkipped + 1
						return
					case Some(state) =>
						state
				}
			}
		println("executing theory "+thy.namespace+" ...")
		evaluator.evalBlock(state, ParseTree.Block(thy.statements)) match {
			case Failed(trace, error) =>
				def describePosition(pos : SourcePosition, label : SourceLabel) : String = {
					val labelDescr =
						label match {
							case NoSourceLabel => ""
							case _ => " (" + label +")"
						}
					if (pos == null) "unknown location" + labelDescr
					else {
						val theory = {
								val src = if (pos.source != null) pos.source.toString else "?"
								"in " + src
							}
						pos.span match {
							case None => 
								theory + " at unknown location" + labelDescr
							case Some(span) => 
								theory + " at row "+(span.firstRow + 1)+", column "+(span.leftMostFirst + 1) + labelDescr
						}
					}
				}
				println("failed executing theory "+thy.namespace+": "+error)
				var trace_overflow = false
				var positions = trace.reverse
				if (positions.size > MAX_TRACE_LENGTH) {
					trace_overflow = true
					positions = positions.take(MAX_TRACE_LENGTH)
				}
				for (pos <- positions) {
					println("  "+describePosition(pos._1, pos._2))
				}
				if (trace_overflow) println("  ... "+(trace.size - MAX_TRACE_LENGTH)+" more")
				executionFailed = executionFailed + 1
			case Success(state, _) => {
				if (state.context.hasAssumptions && state.context.namespace != Kernel.root_namespace) {
					println("theory "+thy.namespace+" fails because it introduces axioms")
					executionFailed = executionFailed + 1
				} else {
					val completed = Root.kernel.completeNamespace(state.context)
					states.register(thy.namespace, new State(completed, state.env.freeze, Collect.Zero, false))
					println("successfully executed theory "+thy.namespace)
					executionSucceeded = executionSucceeded + 1
				}
			}
		}
	}

	def oldmain(args : Array[String]) {
		for (arg <- args) {
			val f = new File(arg)
			if (f.isDirectory) findTheoriesInDirectory(f)
			else addTheory(f)
		}
		val sorted_theories = topsort(theories)	
		if (sorted_theories.isEmpty) return
		val states = States.empty
		def localNames(namespace : Namespace) : Set[String] = {
			states.lookup(namespace) match {
				case None => throw new RuntimeException("internal error: localNames of "+namespace)
				case Some(state) => state.env.freeze.nonlinear.keySet
			}
		}
		val nr = new NamespaceResolution[String](Root.parentsOfNamespace _, localNames _)
		println("\n------------------------------------------------------------\n")
		for (thy <- sorted_theories) evalTheory(states, thy, nr)
		println("\n------------------------------------------------------------\n")
		println("Processed "+numTheories+" theories:")
		val numExecution = executionSucceeded + executionFailed + executionSkipped
		println("  "+executionSucceeded+" theories executed successfully")
		println("  "+(numTheories - numExecution)+" theories failed during preprocessing")		
		println("  "+executionFailed+" theories failed during execution")
		println("  "+executionSkipped+" theories were skipped because of failed/skipped parent theories")
		println("")
	}

}