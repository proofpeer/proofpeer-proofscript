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
		val ty_set2 = Type.Fun(Type.Universe, ty_set1)
		context = context.introduce(Kernel.funapply, ty_set2)
	}
	
	def main(args : Array[String]) {
		setupRoot()
		test("root\\forall")
		test("root\\forall : ((_ → 𝒫) → 𝒫) → 𝒫")
	  test("forall : ((_ → 𝒫) → 𝒫) → 𝒫")
	  test("∀ x, y. x y = y x")
	  test("∀ x, y : 𝒫. x y = y")
	  test("∀ x, y. x y")	  
	}


}