package proofpeer.proofscript.logic

import proofpeer.scala.lang._

sealed class Namespace(private val namespace : String) {
  override def toString : String = namespace
  override def hashCode : Int = namespace.toLowerCase.hashCode
  override def equals(other : Any): Boolean = {
    other match {
      case that: Namespace => namespace.toLowerCase == that.toString.toLowerCase
      case _ => false
    }
  }
  def isAbsolute : Boolean = startsWith(namespace, "\\")
  def absolute : Namespace = if (isAbsolute) this else new Namespace("\\" + namespace)
  def absolute(parent : Namespace) : Namespace = {
    if (isAbsolute) 
      this
    else {
      (new Namespace(parent.namespace + "\\" + namespace)).absolute
    }
  }
  def parent : Namespace = {
    val i = namespace.lastIndexOf("\\")
    if (i < 0) {
      new Namespace("")
    } else {
      new Namespace(namespace.substring(0, i))
    }
  }
}

object NamespaceResolution {
  type Resolution[N] = Map[N, Set[Namespace]] 
}

class NamespaceResolution[N](
  parentsOf : Namespace => Set[Namespace],
  localNames : Namespace => Set[N]) 
{

  import NamespaceResolution._

  type R = Resolution[N]

  private def add(a : R, b : R) : R = {
    var m = a
    for ((i, ns) <- b) {
      a.get(i) match {
        case None => 
          m = m + (i -> ns)
        case Some(namespaces) =>
          m = m + (i -> (namespaces ++ ns))
      }
    }
    m
  }

  private var base_resolutions : Map[Namespace, R] = Map()
  private var resolutions : Map[Namespace, R] = Map()

  private var ancestors : Map[Namespace, Set[Namespace]] = Map()

  def baseResolution(namespace : Namespace) : R = {
    base_resolutions.get(namespace) match {
      case Some(r) => r
      case None =>
        var r : R = Map()
        for (parentNamespace <- parentsOf(namespace)) {
          r = add(r, fullResolution(parentNamespace))
        }
        base_resolutions = base_resolutions + (namespace -> r)
        r
    }
  }

  def fullResolution(namespace : Namespace) : R = {
    resolutions.get(namespace) match {
      case Some(r) => r
      case None =>
        var r = baseResolution(namespace)
        val locals = localNames(namespace)
        val ns = Set(namespace)
        for (localname <- locals) r = r + (localname -> ns)
        resolutions = resolutions + (namespace -> r)
        r
    }
  }

  def ancestorNamespaces(namespace : Namespace) : Set[Namespace] = {
    ancestors.get(namespace) match {
      case Some(ns) => ns
      case None => 
        var namespaces : Set[Namespace] = Set()
        for (p <- parentsOf(namespace)) namespaces = namespaces ++ ancestorNamespaces(p)
        ancestors = ancestors + (namespace -> namespaces)
        namespaces
    }
  }

}

