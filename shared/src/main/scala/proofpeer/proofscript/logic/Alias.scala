package proofpeer.proofscript.logic

import proofpeer.proofscript.serialization.UniquelyIdentifiable

case class Alias(alias : String, namespace : Namespace) extends UniquelyIdentifiable

class Aliases(val base : Namespace, val aliases : List[Alias]) extends UniquelyIdentifiable {
  if (!base.isAbsolute) throw new RuntimeException("base of aliases must be absolute")

  private type Renaming = Map[String, Namespace]
  
  private def resolve(renaming : Renaming, ns : Namespace) : Namespace = {
    if (ns.isAbsolute || ns.components.isEmpty)
      ns.relativeTo(base)
    else 
      renaming.get(ns.components(0)) match {
        case None => ns.relativeTo(base)
        case Some(b) => ns.tail.get.relativeTo(b)
      }
  }

  private def computeRenaming : Renaming = {
    var r : Renaming = Map()
    for (a <- aliases) {
      val ns = resolve(r, a.namespace)
      r = r + (a.alias -> ns)
    }
    r
  }

  private val renaming = computeRenaming

  def resolve(ns : Namespace) : Namespace = resolve(renaming, ns)
    
}
