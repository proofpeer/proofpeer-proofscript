package proofpeer.proofscript.naiveinterpreter

import java.io.File
import proofpeer.proofscript.frontend._
import proofpeer.proofscript.logic.Namespace

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

	def main(args : Array[String]) {
		for (arg <- args) {
			val f = new File(arg)
			if (f.isDirectory) findTheoriesInDirectory(f)
			else addTheory(f)
		}
	}

}