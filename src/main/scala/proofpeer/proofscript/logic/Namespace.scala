package proofpeer.proofscript.logic

import proofpeer.general.StringUtils._
import proofpeer.general._
import proofpeer.proofscript.serialization.UniquelyIdentifiable

object Namespace {
  def apply(namespace : String) : Namespace = {
    val isAbsolute = startsWith(namespace, "\\")
    val components = split_nonempty(namespace, "\\").toVector
    new Namespace(isAbsolute, components)
  }
  def apply(isAbsolute : Boolean, components : Vector[String]) : Namespace = {
    new Namespace(isAbsolute, components)
  }
}

sealed class Namespace (val isAbsolute : Boolean, val components : Vector[String]) extends UniquelyIdentifiable {
  private val namespace = computeString 
  private def computeString : String = {
    var ns = if (isAbsolute) "\\" else ""
    var count = components.size
    for (c <- components) {
      ns = ns + c
      count = count - 1
      if (count > 0) ns = ns + "\\"
    }
    ns
  }
  override def toString : String = namespace
  override def hashCode : Int = toString.toLowerCase.hashCode
  override def equals(other : Any): Boolean = {
    other match {
      case that: Namespace => toString.toLowerCase == that.toString.toLowerCase
      case _ => false
    }
  }
  def absolute : Namespace = if (isAbsolute) this else Namespace(true, components)
  def relativeTo(parent : Namespace) : Namespace = {
    if (isAbsolute) 
      this
    else 
      Namespace(parent.isAbsolute, parent.components ++ components)
  }
  def parent : Option[Namespace] = {
    if (components.size == 0) return None
    val parent_components = components.toList.reverse.tail.reverse.toVector
    Some(Namespace(isAbsolute, parent_components))
  }
  def tail : Option[Namespace] = {
    if (components.size == 0) return None
    Some(Namespace(isAbsolute, components.toList.tail.toVector))
  }
  def lastComponent : String = components(components.size - 1)
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
        for (p <- parentsOf(namespace)) namespaces = (namespaces + p) ++ ancestorNamespaces(p)
        ancestors = ancestors + (namespace -> namespaces)
        namespaces
    }
  }

}

