theory Equal
extends List

# Very basic derived theorems and rules concerning equality

# Fail if nil
def assertNotNil x =
  if x == nil then assert false else x

# Fail if not a theorem. Return nil.
def assertThm thm =
  val norm = normalize (term thm)
  val _    = modusponens (thm, norm)
  nil

# '‹x› = ‹y›' ↦ '‹y› = ‹x›'
# Returns nil if theorem is not of the correct form.
# Fails if not given a theorem.
def
  sym ('‹x› = ‹y›' as thm) =
    modusponens (reflexive '‹x›',combine (reflexive '(z ↦ z = ‹x›)', thm))
  sym thm = assertThm thm

# As "transitive", which is thus derivable.
# Returns the same result of trans, or else nil if any theorem is not an equality.
# Fails if not given a list of theorems.
def
  trans (('‹x›=‹_›' as xy) <+ yz <+ eqs) =
    trans (modusponens (xy,combine (reflexive ('s ↦ ‹x› = s'),yz)) <+ eqs)
  trans ['‹_›=‹_›' as thm] =
    val _ = assertThm thm
    thm
  trans ps =
    val _ = map (assertThm,ps)
    nil

theorem truth:'⊤'
  modusponens (reflexive '(p : ℙ ↦ p)',sym trueDef)

# '‹P›' ↦ '‹P› = T'
# Fails if not given a theorem.
val eqTrueIntro =
  theorem eqTrue:
    let 'p:ℙ'
    assume p:'p:ℙ'
    equivalence ((
      do
        assume 'p:ℙ'
        lift truth),(
      do
        assume '⊤'
        lift p))
  thm => assertNotNil (modusponens (thm,instantiate (eqTrue, term thm)))

# '‹P› = ⊤' ↦ '‹P›'
# Returns nil if theorem is not of the correct form.
# Fails if not given a theorem.
def
  eqTrueElim ('‹_› = ⊤') as thm =
    modusponens (truth,sym thm)
  eqTrueElim thm = assertThm thm

# ['‹f = g›', '‹x = y›, ...] ↦ '‹f x ...› = ‹g y ...›'
# Returns nil if theorems are not of the correct form.
# Fails of not given a list of theorems.
def apThm (thm <+ terms) =
  val _ = assertThm thm
  combine (thm <+ (for t in terms do
                     reflexive t))

theorem trivImp:'∀ p. p → p'
  let 'p:ℙ'
  assume 'p:ℙ'

theorem notFalse:'¬⊥'
  modusponens (instantiate [trivImp,'⊥'],sym (apThm [notDef,'⊥']))

# '‹P› = ⊥' ↦ '¬‹P›'
# Returns nil if theorem is not of the correct form.
# Fails if not given a theorem.
val eqFalseElim =
  theorem eqFalse:
    let p:'p:ℙ'
    assume eq:'p = ⊥'
    theorem imp:
      assume p:'p:ℙ'
      modusponens (p,eq)
    modusponens (imp,sym (apThm (notDef,p)))
  thm =>
    match thm
      case '‹p› = ‹_›' =>
        modusponens (thm,instantiate (eqFalse,p))
      case thm => assertThm thm

# As sym, but descends through universal quantifiers first.
def
  gsym '‹x› = ‹y›' as thm = sym thm
  gsym '∀x. ‹p› x' as thm =
    val [ctx,x,eq] = destabs p
    val symthm
    context <ctx>
      symthm = gsym (instantiate (thm,x))
    lift (symthm,true)
  gsym thm = assertThm thm
