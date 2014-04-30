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
						Utils.failwith("cannot convert preterm to term, "+errors.size+" errors")
				}
		}
	}

	var context : Context = kernel.createNewNamespace(Kernel.root_namespace, Set())	
	
	def read(s : String) : Term = parse(context, s)	

	def main(args : Array[String]) {

		val t = read("root.forall")

	}


}