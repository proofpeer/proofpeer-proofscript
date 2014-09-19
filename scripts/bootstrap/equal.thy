theory Equal
extends root

# Very basic derived theorems and rules concerning equality

val sym =
  theorem symThm: '∀ x:ℙ, y. x = y → y = x'
    let 'x:ℙ'
    let 'y:ℙ'
    assume asm:'x = y'
    modusponens (reflexive 'x',combine (reflexive '(z ↦ z = x)', asm))
  '‹x›=‹y›' as thm => modusponens(thm,instantiate (symThm,x,y))

theorem truth:'⊤'
  modusponens (reflexive '(p : ℙ ↦ p)',sym trueDef)

def eqTrueElim thm = modusponens (truth,sym thm)

val eqTrueIntro =
  theorem eqTrue:'∀ p. p → p = ⊤'
    let 'p:ℙ'
    assume p:'p:ℙ'
    equivalence ((do
                    assume 'p:ℙ'
                    theorem '⊤' truth),
                 (do
                    assume '⊤'
                    theorem 'p:ℙ' p))
  thm => modusponens (thm,instantiate (eqTrue, term thm))

def apThm (thm <+ terms) =
  combine (thm <+ (for t in terms do
                     reflexive t))
                     
val eqFalseElim =
  theorem eqFalse:'∀ p. p = ⊥ → ¬p'
    let p:'p:ℙ'
    assume eq:'p = ⊥'
    theorem imp:'p → ⊥'
      assume p:'p:ℙ'
      modusponens (p,eq)
    modusponens (imp,sym (apThm (notDef,p)))
  '‹p› = ‹_›' as thm => modusponens (thm,instantiate (eqFalse,p))
