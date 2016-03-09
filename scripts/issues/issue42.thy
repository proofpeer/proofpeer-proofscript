theory issue42
extends \root

theorem '∀x. x = x'
  val (ctx,x,_) = destabs 'x ↦ x'
  val foo
  context <ctx>
    foo = reflexive x
  foo

theorem '∀x. ⊤ = ⊤'
  val (ctx,x,_) = destabs 'x ↦ ⊤'
  val foo
  context <ctx>
    foo = reflexive '⊤'
  lift! foo