theory Equal
extends root

# Very basic derived theorems and rules concerning equality

def
  sym ('‹x› = ‹y›' as thm) =
    theorem symThm: '‹x› = ‹y› → ‹y› = ‹x›'
      assume asm: '‹x› = ‹y›'
      modusponens (reflexive '‹x›',combine (reflexive '(z ↦ z = ‹x›)', asm))
    modusponens(thm,symThm,x,y)

def
  trans [thm] = thm
  trans (('‹x›=‹_›' as xy) <+ yz <+ eqs) =
    trans (modusponens (xy,combine (reflexive ('s ↦ ‹x› = s'),yz)) <+ eqs)

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
