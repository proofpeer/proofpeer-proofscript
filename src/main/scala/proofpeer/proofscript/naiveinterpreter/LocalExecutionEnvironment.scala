package proofpeer.proofscript.naiveinterpreter 

import proofpeer.proofscript.frontend._
import proofpeer.proofscript.logic._
import proofpeer.general.Bytes
import proofpeer.proofscript.serialization._
import java.io.File

class LocalExecutionEnvironmentAdapter(compileDir : File, theoryFiles : List[LocalExecutionEnvironment.TheoryFile]) extends ExecutionEnvironmentAdapter {

  if (!compileDir.exists) compileDir.mkdir()
  if (!(compileDir.exists && compileDir.isDirectory)) throw new RuntimeException("invalid compilation directory: " + compileDir)

  private var theories : Map[Namespace, LocalExecutionEnvironment.TheoryFile] = Map()
  private var dataOfTheories : Map[Namespace, Bytes] = Map()

  for (f <- theoryFiles) theories = theories + (f.namespace -> f)

  def lookupTheory(namespace : Namespace) : Option[(Source, Bytes, String, Option[Bytes])] = {
    theories.get(namespace) match {
      case None => None
      case Some(f) => Some((f.source, f.contentKey, f.content, dataOfTheories.get(namespace)))
    }
  }

  def storeTheoryData(namespace : Namespace, theoryData : Bytes) {
    dataOfTheories = dataOfTheories + (namespace -> theoryData)
  }

  private def compileKeyFile(category : CompileKeyDataCategory, compileKey : Bytes) : File = {
    import CompileKeyDataCategory._
    val suffix =
      category match {
        case PARSETREE => ".parsetree"
        case OUTPUT => ".output"
        case STATE => ".state"
      }
    new File(compileDir, compileKey.asHex + suffix)
  }

  def loadCompileKeyData(category : CompileKeyDataCategory, compileKey : Bytes) : Option[Bytes] = {
    val f = compileKeyFile(category, compileKey)
    if (f.exists) Some(BytesInFiles.loadBytes(f)) else None
  }

  def storeCompileKeyData(category : CompileKeyDataCategory, compileKey : Bytes, data : Bytes) {
    BytesInFiles.writeBytes(compileKeyFile(category, compileKey), data)
  }

}

object BytesInFiles {

  import java.io._

  def writeBytes(f : File, b : Bytes, bufferSize : Int = 10 * 1024) {
    val out = new BufferedOutputStream(new FileOutputStream(f), bufferSize)
    val len = b.length
    for (i <- 0 until len) {
      out.write(b(i))
    }
    out.flush()
    out.close()
  }

  def loadBytes(f : File, bufferSize : Int = 10 * 1024) : Bytes = {
    val in = new BufferedInputStream(new FileInputStream(f), bufferSize)
    var bytes : Vector[Byte] = Vector()
    do {
      val b = in.read()
      if (b >= 0) bytes = bytes :+ (b.toByte)
      else {
        in.close()
        return Bytes(bytes)
      }
    } while(true)
    throw new RuntimeException("internal error in loadBytes")
  }

}

object LocalExecutionEnvironment {

  import proofpeer.general.Bytes
  import java.io.File

  case class TheoryFile(namespace : Namespace, source : Source, content : String, contentKey : Bytes)

  private def sourceFromFile(f : File) = new Source(Namespace(""), f.toString)

  def create(compileDir : File, directories : Seq[String]) : (ExecutionEnvironment, Set[Namespace]) = {
    var theoryFiles : List[TheoryFile] = List()
    val rootNamespace = Namespace("\\")
    for (directory <- directories) {
      val f = new File(directory)
      if (f.isDirectory)
        theoryFiles = findTheoriesInDirectory(rootNamespace, f, theoryFiles)
      else throw new RuntimeException("'" + f + "' is not a directory")
    }
    val adapter = new LocalExecutionEnvironmentAdapter(compileDir, theoryFiles)
    (new ExecutionEnvironmentImpl(adapter), theoryFiles.map(_.namespace).toSet)
  }

  private def findTheoriesInDirectory(namespace : Namespace, dir : File, files : List[TheoryFile]) : List[TheoryFile] = {
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
        theoryFiles = TheoryFile(ns, sourceFromFile(f), code, key) :: theoryFiles
      }
    }
    theoryFiles
  }

}

