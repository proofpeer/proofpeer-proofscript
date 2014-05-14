package proofpeer.proofscript.logic

object Root {
	val kernel = Kernel.createDefaultKernel()
	val nr = new NameResolution(kernel, c => c.localConstants)

	def parse(context : Context, s : String) : Term = {
		Syntax.parsePreterm(s) match {
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
		println("parsed:\n  " + checkPrinting(context, t))
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
		def axiom(name : String, ax : String) {
			val t = read(ax)
			val th = context.assume(Kernel.rootname(name), t)
			context = th.context
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
		intro(Kernel.pair, ty_set2)
		intro(Kernel.fun, 
			Type.Fun(ty_set0, Type.Fun(Type.Fun(ty_set0, ty_set0), ty_set0)))
		intro(Kernel.funapply, ty_set2)
		intro(Kernel.set_elementOf,
			Type.Fun(ty_set0, Type.Fun(ty_set0, ty_log0)))
		intro(Kernel.set_subsetOf,
			Type.Fun(ty_set0, Type.Fun(ty_set0, ty_log0)))		
		intro(Kernel.forallin, 
			Type.Fun(ty_set0, Type.Fun(Type.Fun(ty_set0, ty_log0), ty_log0)))
		intro(Kernel.existsin, 
			Type.Fun(ty_set0, Type.Fun(Type.Fun(ty_set0, ty_log0), ty_log0)))

		axiom("trueDef", "((p : ℙ ↦ p) = (p : ℙ ↦ p))")
		axiom("falseDef", "⊥ = (∀ p. p)")
		axiom("notDef", "∀ p. (¬ p) = (p → ⊥)")
		axiom("andDef", "∀ x, y. (x ∧ y) = ((f ↦ f x y) = (f ↦ f ⊤ ⊤))")
		axiom("impliesDef", "∀ x, y. (x → y) = ((x ∧ y) = x)")
		axiom("orDef", "∀ x, y. (x ∨ y) = (∀ z. (x → z) → (y → z) → z)")
		axiom("empty", "∀ x. x ∉ ∅")
		axiom("ext", "∀ x, y. (x = y) = (∀ z. z ∈ x = z ∈ y)")
		axiom("Union", "∀ z, x. z ∈ ⋃ x = (∃ y ∈ x. z ∈ y)")
		axiom("union", "∀ x, y, z. (z ∈ x ∪ y) = (z ∈ x ∨ z ∈ y)")
		axiom("Intersection", "∀ z, x. z ∈ ⋂ x = (∀ y ∈ x. z ∈ y)")
		axiom("intersection", "∀ x, y, z. z ∈ x ∩ y = (z ∈ x ∧ z ∈ y)")
		axiom("difference", "∀ x, y, z. z ∈ x ∖ y = (z ∈ x ∧ z ∉ y)")
		axiom("subset", "∀ x, y. x ⊂ y = (∀ z ∈ x. z ∈ y)")
		axiom("singleton", "∀ x, y. y ∈ {x} = (y = x)")
		axiom("power", "∀ x, y. x ∈ 𝒫 y = x ⊂ y")
		axiom("repl", "∀ A, f, b. b ∈ repl A f = (∃ a ∈ A. b = f a)")
		axiom("sep", "∀ A, p, a. a ∈ sep A p = (a ∈ A ∧ p a)")
		axiom("regularity", "∀ A. A ≠ ∅ → (∃ x ∈ A. x ∩ A = ∅)")
		axiom("infinity", "∃ X. ∅ ∈ X ∧ (∀ x ∈ X. x ∪ {x} ∈ X)")
		axiom("forallin", "∀ X, P. forallin X P = (∀ x. x ∈ X → P x)")
		axiom("existsin", "∀ X, P. existsin X P = (∃ x. x ∈ X ∧ P x)")
		axiom("pair", "∀ x, y. (x, y) = {{x}, {x, y}}")
		axiom("fun", "∀ X, f. fun X f = {(x, f x)| x ∈ X}")
		axiom("apply", "∀ X, f, x ∈ X. fun X f x = f x")
	}

	def checkPrinting(context : Context, tm : Term) : String = {
		val u = Syntax.printTerm(nr.resolveContext(context), tm)
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
		val s = Abs(IndexedName("x",None),Universe,Comb(Comb(Const(Name(Some(new Namespace("root")),IndexedName("apply",None))),Const(Name(None,IndexedName("x",None)))),Var(IndexedName("x",None))))
		println("s = "+checkPrinting(c, s))
		val th_r = c.reflexive(r)
		val th_s = c.reflexive(s)
		val th = c.transitive(th_r, th_s)
		println("th = "+checkPrinting(c, th.proposition)) 
	}
	
	def main(args : Array[String]) {
		setupRoot()
		test("root\\forall")
		test("root\\forall : ((_ → ℙ) → ℙ) → ℙ")
	  test("forall : ((_ → ℙ) → ℙ) → ℙ")
	  test("∀ x, y. x y = y")
	  test("∀ x, y : ℙ. x y = y")
	  test("∀ x, y. x y")	
	  test("forallin")  
	  test("∀ x. x = forallin")
	  test("∀ x, y. x x = y")
	  test("x ↦ y ↦ x y")
	  test("x ↦ x x")
	  test("r ↦ ∀P. (∀x. (∀y. r y x  → P y) → P x) → (∀x. P x)")
	  test("∀ x. x ∉ ∅")
	  test("∀ x, y. (x = y) = (∀ z. z ∈ x = z ∈ y)")
	  test("∀ z, x. z ∈ ⋃ x = (∃ y. z ∈ y ∧ y ∈ x)")
	  test("∀ y, x. y ∈ 𝒫 x = y ⊂ x")
	  test("∀ b, A, f. b ∈ repl A f = (∃ a ∈ A. b = f a)")
	  test("∀ A, p, a. a ∈ sep A p = (a ∈ A ∧ p a)")
	  test("subsetof = (x ↦ y ↦ (∀ z ∈ x. z ∈ y))")
	  test("∀ x, y. x ⊂ y = (∀ z ∈ x. z ∈ y)")
	  test("∀ A. A ≠ ∅ → (∃ x ∈ A. x ∩ A = ∅)")
	  test("∃ X. ∅ ∈ X ∧ (∀ x ∈ X. x ∪ {x} ∈ X)")
	  test("∀ x, y. y ∈ {x} = (y = x)")
	  test("∀ X, P. forallin X P = (∀ x. x ∈ X → P x)")
	  test("x ↦ x = fun")
	  test("∀ x, y. (x, y) = {{x}, {x, y}}")
	  test("x ↦ y ↦ z ↦ (x, y, z)")
	  test("∀ X, f. fun X f = {(x, f x)| x ∈ X}")
	  test("x ↦ y ↦ z ↦ x y z")
	  test("∀ X, f, x ∈ X. fun X f x = f x")
	  test("A, p ↦ {x | x ∈ A. p x}")
	  test("∀ X f x. fun X f x = f x")
	  test("∀ X ∀ f ∀ x ∈ X. fun X f x = f x")	 
	  test("root\\forallin") 
	  test("Root\\forallin") 
	  test("∀ x y z. x (y z) = (x y) z")
	  test("∀ a b c d. a b c d")	  
	  test("∀ a b c d. a b c d ∧ b c d")
	  test("∀ a b c d. a b c d ∧ b c d ∧ c d")
	  test("a b c d ↦ a b c d ∧ b c d ∧ c d ∧ d")
	  test("∀ a b c d. a b c d ∧ d")
	  test("a b c d ↦ a b c d")
	  test("a b c d ↦ a b c d ∧ b")


	  //test("∀ x y z. x (y z) → (x y) z")
	  testScope()
	}

}