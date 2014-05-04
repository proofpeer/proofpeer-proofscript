package proofpeer.proofscript.logic

object Root {
	val kernel = Kernel.createDefaultKernel()
	val nr = new NameResolution(kernel, c => c.localConstants)

	def parse(context : Context, s : String) : Term = {
		TermSyntax.parsePreterm(s) match {
			case None => Utils.failwith("cannot parse as preterm: '"+s+"'")
			case Some(ptm) => 
				val typingContext = Preterm.obtainTypingContext(nr, context)
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

	var context : Context = kernel.createNewNamespace(Kernel.root_namespace, Set())	

	def read(s : String) : Term = parse(context, s)	

	def test(s : String) {
		println("")
		println("input:\n  " + s)
		val t = read(s)
		println("parsed:\n  " + TermSyntax.printTerm(t))
	}

	def setupRoot() {
		val ty_set0 = Type.Universe
		val ty_set1 = Type.Fun(ty_set0, ty_set0)
		val ty_set2 = Type.Fun(ty_set0, ty_set1)
		val ty_log0 = Type.Prop
		val ty_log1 = Type.Fun(ty_log0, ty_log0)
		val ty_log2 = Type.Fun(ty_log0, ty_log1)
		def intro(name : Name, ty : Type) {
			context = context.introduce(name, ty)
		}
		intro(Kernel.logical_and, ty_log2)
		intro(Kernel.logical_or, ty_log2)
		intro(Kernel.logical_not, ty_log1)
		intro(Kernel.logical_true, ty_log0)
		intro(Kernel.logical_false, ty_log0)
		intro(Kernel.empty_set, ty_set0)
		intro(Kernel.set_difference, ty_set2)
		intro(Kernel.set_union, ty_set2)
		intro(Kernel.set_intersection, ty_set2)
		intro(Kernel.set_bigunion, ty_set1)
		intro(Kernel.set_bigintersection, ty_set1)
		intro(Kernel.set_power, ty_set1)
		intro(Kernel.set_singleton, ty_set1)
		intro(Kernel.set_separation, 
			Type.Fun(ty_set0, Type.Fun(Type.Fun(ty_set0, ty_log0), ty_set0)))
		intro(Kernel.set_replacement, 
			Type.Fun(ty_set0, Type.Fun(Type.Fun(ty_set0, ty_set0), ty_set0)))
		intro(Kernel.fun, 
			Type.Fun(ty_set0, Type.Fun(Type.Fun(ty_set0, ty_set0), ty_set0)))
		intro(Kernel.funapply, ty_set2)
		intro(Kernel.forallin, 
			Type.Fun(ty_set0, Type.Fun(Type.Fun(ty_set0, ty_log0), ty_log0)))
		intro(Kernel.existsin, 
			Type.Fun(ty_set0, Type.Fun(Type.Fun(ty_set0, ty_log0), ty_log0)))
	}
	
	def main(args : Array[String]) {
		setupRoot()
		test("root\\forall")
		test("root\\forall : ((_ → 𝒫) → 𝒫) → 𝒫")
	  test("forall : ((_ → 𝒫) → 𝒫) → 𝒫")
	  test("∀ x, y. x y = y")
	  test("∀ x, y : 𝒫. x y = y")
	  test("∀ x, y. x y")	
	  test("forallin")  
	  test("∀ x. x = forallin")
	}


}