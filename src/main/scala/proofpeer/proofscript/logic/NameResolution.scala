package proofpeer.proofscript.logic

// NameResolution depends on the kernel, and on a function that computes the local names for a given context.
class NameResolution(kernel : Kernel, localNames : Context => Set[Name]) {

	private type ResolutionWithConflicts = Map[IndexedName, Option[Name]]
	type Resolution = Map[IndexedName, Name]

	private def add(a : ResolutionWithConflicts, b : Resolution) : ResolutionWithConflicts = {
		var m = a
		for ((i, v) <- b) {
			a.get(i) match {
				case None => 
				  m = m + (i -> Some(v))
				case Some(None) =>
				  // do nothing
				case Some(u) =>
				  if (u != Some(v)) m = m + (i -> None)
			}
		}
		m
	}

	private def removeConflicts(r : ResolutionWithConflicts) : Resolution = {
		var m : Resolution = Map()
		for ((i, n) <- r) {
			if (n.isDefined) m = m + (i -> n.get)
		}
		m
	}

	private var resolutions : Map[String, Resolution] = Map()

	private def computeBaseResolution(context : Context) : Resolution = {
		var r : ResolutionWithConflicts = Map()
		for (parentNamespace <- context.parentNamespaces) {
			r = add(r, resolveCompletedNamespace(parentNamespace))
		}
		removeConflicts(r)
	}

	private def resolveCompletedNamespace(namespace : String) : Resolution = {
		resolutions.get(namespace) match {
		  case Some(r) => r
			case None =>
				kernel.contextOfNamespace(namespace) match {
					case None => Utils.failwith("No completed namespace '"+namespace+"' for name resolution found.")
					case Some(context) => 
						var r = computeBaseResolution(context)
						val locals = localNames(context.parentContext.get)
						for (localname <- locals) {
							if (localname.namespace.isDefined)
								r = r + (localname.name -> localname)
						  else
						    r = r - localname.name
						}
						resolutions = resolutions + (namespace -> r)
						r
				}
		}
	}

	def resolveContext(context : Context) : Resolution = {
		context.kind match {
			case ContextKind.Complete => 
			  resolveCompletedNamespace(context.namespace)
			case _ =>
				var r = computeBaseResolution(context)
				val locals = localNames(context)
				for (localname <- locals) {
						r = r + (localname.name -> localname)
				}
				r
		}
	}

}