package proofpeer.proofscript.naiveinterpreter 

import proofpeer.proofscript.frontend._
import proofpeer.proofscript.logic._
import proofpeer.general.Bytes
import java.io.File

class LocalExecutionEnvironment(compileDir : File, _theories : Seq[ExecutionEnvironment.Theory]) extends ExecutionEnvironment {

  if (!compileDir.exists) {
    if (!compileDir.mkdir()) throw new RuntimeException("cannot create compile directory '" + compileDir + "'")    
  } else if (!compileDir.isDirectory) throw new RuntimeException("compile directory '" + compileDir + "' is not a directory")

  import ExecutionEnvironment._
  import LocalExecutionEnvironment._

  private var theories : Map[Namespace, Theory] = Map()

  for (thy <- _theories) theories = theories + (thy.namespace -> thy)

  def lookupTheory(namespace : Namespace) : Option[Theory] = {
    theories.get(namespace)
  }

  def allTheoriesIn(namespace : Namespace, recursive : Boolean) : Set[Namespace] = {
    var col : List[Namespace] = List()
    if (recursive) {
      for ((ns, thy) <- theories) {
        if (namespace.isAncestorOf(ns))  col = ns :: col
      }
    } else throw new RuntimeException("non-recursive listing not supported")
    col.toSet
  }

  private def updateTheory(thy : Theory) : Theory = {
    theories = theories + (thy.namespace -> thy)
    thy
  }

  def addFaults(namespace : Namespace, faults : Vector[Fault]) : Theory = {
    lookupTheory(namespace) match {
      case Some(thy : LocalTheory) =>
        updateTheory(LocalTheory(thy.namespace, thy.source, thy.content, thy.contentKey, thy.faults ++ faults))
      case Some(thy : LocalRootedTheory) =>
        updateTheory(LocalRootedTheory(thy.namespace, thy.source, thy.content, thy.contentKey, thy.faults ++ faults, thy.parents, 
          thy.aliases, thy.compileKey, thy.proofscriptVersion))
      case Some(thy : LocalCompiledTheory) =>
        updateTheory(LocalCompiledTheory(thy.namespace, thy.source, thy.content, thy.contentKey, thy.faults ++ faults, thy.parents,
          thy.aliases, thy.compileKey, thy.proofscriptVersion, thy.parseTree, thy.compiledBytes))
      case _ =>
        throw new RuntimeException("cannot add faults to theory '" + namespace + "'")
    }
  }

  def finishedRooting(namespace : Namespace, parents : Set[Namespace], aliases : Aliases, proofscriptVersion : Option[String]) : RootedTheory = {
    lookupTheory(namespace) match {
      case Some(thy : LocalTheory) =>
        var version = proofscriptVersion
        var parentCompileKeys : Vector[Bytes] = Vector()
        val vparents = parents.toVector.sortBy(p => p.toString.toLowerCase)
        for (parent <- vparents) {
          lookupTheory(parent) match {
            case Some(parentThy : RootedTheory) =>
              version = Some(parentThy.proofscriptVersion)
              parentCompileKeys = parentCompileKeys :+ parentThy.compileKey
            case _ =>
              throw new RuntimeException("cannot finish rooting of theory '" + namespace + "' because of parent theory '" + parent + "'")
          }
        }
        if (parents.isEmpty && namespace != Namespace.root) throw new RuntimeException("theory '" + namespace + "' does not have any parent theories")
        if (version.isEmpty) throw new RuntimeException("theory '" + namespace + "' doesn't have a version of ProofScript associated with it")
        val compileKey = Bytes.encode((thy.contentKey, parentCompileKeys)).sha256
        val rootedTheory = LocalRootedTheory(thy.namespace, thy.source, thy.content, thy.contentKey, thy.faults, parents, aliases, compileKey, version.get)
        updateTheory(rootedTheory)
        rootedTheory
      case _ => 
        throw new RuntimeException("cannot finish rooting of theory '" + namespace + "'")
    }
  }

  def finishedCompiling(namespace : Namespace, parseTree : ParseTree.Block, compiledBytes: Bytes) : CompiledTheory = {
    lookupTheory(namespace) match {
      case Some(thy : LocalRootedTheory) =>
        val compiledTheory = LocalCompiledTheory(thy.namespace, thy.source, thy.content, thy.contentKey, thy.faults, thy.parents, 
          thy.aliases, thy.compileKey, thy.proofscriptVersion, parseTree, compiledBytes)
        updateTheory(compiledTheory)
        compiledTheory
      case _ => throw new RuntimeException("cannot finish compiling of theory '" + namespace + "'")
    }
  }

}

object LocalExecutionEnvironment {

  import ExecutionEnvironment._
  import proofpeer.general.Bytes
  import java.io.File

  private case class LocalTheory(namespace : Namespace, source : Source, content : String, contentKey : Bytes, faults : Vector[Fault]) extends Theory 

  private case class LocalRootedTheory(namespace : Namespace, source : Source, content : String, contentKey : Bytes, faults : Vector[Fault],
    parents : Set[Namespace], aliases : Aliases, compileKey : Bytes, proofscriptVersion : String) extends RootedTheory

  private case class LocalCompiledTheory(namespace : Namespace, source : Source, content : String, contentKey : Bytes, faults : Vector[Fault],
    parents : Set[Namespace], aliases : Aliases, compileKey : Bytes, proofscriptVersion : String, parseTree : ParseTree.Block, compiledBytes : Bytes) extends CompiledTheory

  def sourceFromFile(f : File) = new Source(Namespace(""), f.toString)

  def create(compileDir : File, directories : Seq[String]) : LocalExecutionEnvironment = {
    var theoryFiles : List[Theory] = List()
    val rootNamespace = Namespace("\\")
    for (directory <- directories) {
      val f = new File(directory)
      if (f.isDirectory)
        theoryFiles = findTheoriesInDirectory(rootNamespace, f, theoryFiles)
      else throw new RuntimeException("'" + f + "' is not a directory")
    }
    new LocalExecutionEnvironment(compileDir, theoryFiles)
  }

  private def findTheoriesInDirectory(namespace : Namespace, dir : File, files : List[Theory]) : List[Theory] = {
    var theoryFiles = files
    for (f <- dir.listFiles) {
      if (f.isDirectory)
        theoryFiles = findTheoriesInDirectory(Namespace(f.getName()).relativeTo(namespace), f, theoryFiles)
      else if (f.getName().endsWith(".thy")) {
        val theoryName = f.getName().substring(0, f.getName().length - 4)
        val ns = Namespace(theoryName).relativeTo(namespace)
        val source = scala.io.Source.fromFile(f)
        val code = source.getLines.mkString("\n")
        source.close()
        val key = Bytes.fromString(code).sha256
        theoryFiles = LocalTheory(ns, sourceFromFile(f), code, key, Vector()) :: theoryFiles
      }
    }
    theoryFiles
  }

}