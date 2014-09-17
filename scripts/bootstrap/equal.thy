theory Equal
extends root

# Very basic derived theorems and rules concerning equality

val [symThm,sym] =
  theorem symThm: '∀ x:ℙ, y. x = y → y = x'
    let 'x:ℙ'
    let 'y:ℙ'
    assume asm:'x = y'
    modusponens (reflexive 'x',combine (reflexive '(z ↦ z = x)', asm))
  [symThm, (thm =>
              match term thm
              case '‹x›=‹y›' => modusponens(thm,instantiate (symThm,x,y)))]

val truth =
  theorem '⊤'
    modusponens (reflexive '(p : ℙ ↦ p)',sym trueDef)

val eqTrueElim = thm => modusponens (truth,sym thm)

val eqTrueIntro =
  val eqTrue =
    theorem '∀ p. p → p = ⊤'
      let 'p:ℙ'
      assume p:'p:ℙ'
      equivalence ((do
                      assume 'p:ℙ'
                      theorem '⊤' truth),
                   (do
                      assume '⊤'
                      theorem 'p:ℙ' p))
  thm => modusponens (thm,instantiate (eqTrue, term thm))

val apThm = (thm <+ terms) =>
  combine (thm <+ (for t in terms do
                     reflexive t))
                     
val eqFalseElim =
  theorem eqFalse:'∀ p. p = ⊥ → ¬p'
    let p:'p:ℙ'
    assume eq:'p = ⊥'
    theorem imp:'p → ⊥'
      assume p:'p:ℙ'
      modusponens [p,eq]
    modusponens [imp,sym (apThm [notDef,p])]
  thm => (match term thm
            case '‹p› = ‹_›' => modusponens [thm,instantiate [eqFalse,p]])
