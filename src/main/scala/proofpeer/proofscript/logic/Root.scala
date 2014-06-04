package proofpeer.proofscript.logic

object Root {
	val kernel = Kernel.createDefaultKernel()

	def parentsOfNamespace(namespace : Namespace) : Set[Namespace] =
		kernel.parentsOfNamespace(namespace) match {
			case None => Utils.failwith("no such namespace: "+namespace)
			case Some(namespaces) => namespaces
		}

	private def localNames(namespace : Namespace) : Set[IndexedName] =
		kernel.contextOfNamespace(namespace) match {
			case None => Utils.failwith("no completed context for namespace: "+namespace)
			case Some(context) => 
				var locals : Set[IndexedName] = Set()
				for (name <- context.localConstants) {
					if (name.namespace.isDefined) locals = locals + name.name
				}
				locals
		}

	val nr = new NamespaceResolution[IndexedName](parentsOfNamespace _, localNames _)

	def parse(context : Context, s : String) : Term = {
		Syntax.parsePreterm(s) match {
			case None => Utils.failwith("cannot parse as preterm: '"+s+"'")
			case Some(ptm) => 
				val aliases = kernel.aliasesOfNamespace(context.namespace).get
				val typingContext = Preterm.obtainTypingContext(aliases, nr, context)
				Preterm.inferTerm(typingContext, ptm) match {
					case Left(tm) => tm
					case Right(errors) =>
						for (e <- errors) {
							println("error: "+e.reason)
						}
						Utils.failwith("cannot convert preterm to term, "+errors.size+" errors")
				}
		}
	}

	var context : Context = kernel.createNewNamespace(Kernel.root_namespace, Set(), 
		new Aliases(Kernel.root_namespace.parent.get, List()))	

	def read(s : String) : Term = parse(context, s)	

	def test(s : String) {
		println("")
		println("input:\n  " + s)
		val t = read(s)
		println("parsed:\n  " + checkPrinting(context, t))
	}

	def checkPrinting(context : Context, tm : Term) : String = {
		val aliases = kernel.aliasesOfNamespace(context.namespace).get
		val u = Syntax.printTerm(Preterm.obtainNameResolution(aliases, nr, context), tm)
		val tm2 = parse(context, u)
		if (!KernelUtils.alpha_equivalent(tm, tm2))
			Utils.failwith("term '"+u+"' is not a correct representation of: "+tm)
		else
			u
	}

	def testScope() {
		import Term._
		import Type._
		val c = context.introduce(Name(None, IndexedName("x", None)), Universe)
		val r = parse(c, "y ↦ x y")
		val s = Abs(IndexedName("x",None),Universe,Comb(Comb(Const(Name(Some(Namespace("\\root")),IndexedName("apply",None))),Const(Name(None,IndexedName("x",None)))),Var(IndexedName("x",None))))
		println("s = "+checkPrinting(c, s))
		val th_r = c.reflexive(r)
		val th_s = c.reflexive(s)
		val th = c.transitive(th_r, th_s)
		println("th = "+checkPrinting(c, th.proposition)) 
	}

}