package proofpeer.proofscript.naiveinterpreter

import java.io.File
import proofpeer.proofscript.frontend._
import proofpeer.proofscript.logic._

object Interpreter {

	class FileSource(val f : File) extends Source 

	def addTheory(f : File) {
		if (f.exists) {
			println("processing theory file: "+f)
			val source = scala.io.Source.fromFile(f)
			val code = source.getLines.mkString("\n")
			source.close()
			val result = Parser.parseFromSource(new FileSource(f), code)
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

	case class Theory(source : Source, namespace : Namespace, parents : Set[Namespace], statements : Vector[ParseTree.Statement],
										resolve : Namespace => Namespace)

	var theories : Map[Namespace, Theory] = Map()

	def addTheory(f : File, thy : ParseTree.Block) {
		if (thy.statements.isEmpty) {
			println("  theory is empty and will be ignored")
		} else {
			thy.statements.head match {
				case ParseTree.STTheory(namespace, parents) =>
					val ns = namespace.absolute
					val master_ns = ns.parent
					def resolve_ns(m : Namespace) = m.absolute(master_ns)
					val ps = parents.map (resolve_ns _)
					val theory = Theory(new FileSource(f), ns, ps.toSet, thy.statements.tail, resolve_ns _)
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
		var values : Map[String, StateValue] = Map()
		for ((n, th) <- Root.axioms) {
			values = values + (n -> TheoremValue(th))
		}
		new State(Root.context, values, Set(), Collect.Zero)
	}

	def makeState(states : States, namespace : Namespace, parentNamespaces : Set[Namespace]) : Option[State] = {
		for (p <- parentNamespaces) {
			if (!states.lookup(p).isDefined) return None
		}
		val context = Root.kernel.createNewNamespace(namespace, parentNamespaces)
		Some(new State(context, Map(), Set(), Collect.Zero))
	} 

	def evalTheory(states : States, thy : Theory) {
		val evaluator = new Eval(states, Root.kernel, Root.nr, thy.resolve, thy.namespace)
		val state : State = 
			if (thy.namespace == Kernel.root_namespace) 
				rootState
			else {
				makeState(states, thy.namespace, thy.parents) match {
					case None =>
						println("skipping theory "+thy.namespace)
						return
					case Some(state) =>
						state
				}
			}
		evaluator.evalStatements(state, thy.statements) match {
			case Failed(pos, error) =>
				println("failed executing theory "+thy.namespace)
				if (pos != null) {
					pos.span match {
						case None =>
						case Some(span) =>
							println("row = "+(span.firstRow + 1)+", column = "+(span.leftMostFirst + 1))				
					}
				}
				println(error)
			case Success(state) => {
				val completed = Root.kernel.completeNamespace(state.context)
				states.register(thy.namespace, new State(completed, state.values, Set(), Collect.Zero))
				println("successfully executed theory "+thy.namespace)
			}
		}
	}

	def main(args : Array[String]) {
		for (arg <- args) {
			val f = new File(arg)
			if (f.isDirectory) findTheoriesInDirectory(f)
			else addTheory(f)
		}
		val sorted_theories = topsort(theories)	
		if (sorted_theories.isEmpty) return
		Root.setupRoot
		val states = States.empty
		for (thy <- sorted_theories) evalTheory(states, thy)
	}

}