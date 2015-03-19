theory issue50 extends \bootstrap\conversions

let 'p : 𝒰 → 𝒰 → ℙ'
val p = 'p'

def rand fx =
  match destcomb fx
    case (f, x) => x 

theorem right: '(∃f. ∀x. ‹p› x (f x)) → (∀x. ∃y. ‹p› x y)'
  val c1 = context
  show c1
  assume asm: '∃f. ∀x. ‹p› x (f x)'
  let x: '‹fresh "x"›'  
  theorem '∃y. ‹p› x y'
    val c2 = context
    choose ch:'‹fresh "f"›' asm
    val fx = rand (instantiate (ch,x): Term)
    show fx
    let ydef: 'y = ‹fx›'
    val th = convRule (randConv (subsConv (gsym ydef)), instantiate (ch,x))
    context<c2>
      show th
    th
