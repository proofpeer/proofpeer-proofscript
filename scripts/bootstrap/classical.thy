theory Classical
extends Connectives Match

choose choiceDef:'epsilon:(ℙ → ℙ) → ℙ'
  let 'p:ℙ → ℙ'
  assume ex:'∃x. p x'
  choose 'chosen:ℙ' ex

theorem choice:'∀ p x. (p:ℙ → ℙ) (x:ℙ) → p (epsilon p)'
  let p:'p:ℙ → ℙ'
  let 'x:ℙ'
  assume assum:'p x'
  theorem pExists:'∃ x:ℙ. p x'
    let ydef:'y:ℙ = x'
    modusponens (assum,combine (reflexive p,sym ydef))
  modusponens (pExists,instantiate (choiceDef,'p:ℙ → ℙ'))

theorem excludedMiddle: '∀p. p ∨ ¬p'
  let 'p:ℙ'
  val u = '(x ↦ x ∨ p)'
  val v = '(x ↦ ¬x ∨ p)'
  theorem lemma:'(epsilon ‹u› ∧ ¬(epsilon ‹v›)) → p → ⊥'
    assume asm:'epsilon ‹u› ∧ ¬(epsilon ‹v›)'
    assume p:'p:ℙ'
    val eq =
      trans (treeConv (rewrConv [eqTrueIntro p,orRightZero]) 'epsilon ‹u›' 0,
             sym (treeConv (rewrConv [eqTrueIntro p,orRightZero]) 'epsilon ‹v›' 0))
    val [contr] = convRule (treeConv (rewrConv [eq]),asm)
    modusponens (conjuncts contr 0,
                 matchmp (notDefEx, conjuncts contr 1))
  theorem lemma2: '(epsilon ‹u› ∧ ¬(epsilon ‹v›)) → p ∨ ¬p'
    assume asm:'epsilon ‹u› ∧ ¬(epsilon ‹v›)'
    orIntroR ('p:ℙ',convRule (treeConv (rewrConv [impliesNot]),
                              modusponens (asm,lemma)) 0)
  theorem lemma3: 'p → p ∨ ¬p'
    assume p:'p:ℙ'
    orIntroL (p,'¬p')
  val factored = matchmp
        (sym (instantiate (orAndDistrib2,
              'epsilon ‹u›',
              '¬(epsilon ‹v›)',
              'p:ℙ')),
         andIntro (matchmp (instantiate (choice,u), orIntroL (truth,'p:ℙ')),
                   matchmp (instantiate (choice,v), orIntroL (notFalse,'p:ℙ'))))
  matchmp (orDefEx, factored, lemma2, lemma3)

theorem orComplement: '∀p. (p ∨ ¬p) = ⊤'
  let p:'p:ℙ'
  eqTrueIntro (instantiate (excludedMiddle,p))

theorem boolCases: '∀p. p = ⊤ ∨ p = ⊥'
  convRule (randConv (absConv (binaryConv (rewrConv [simpP], rewrConv [simpNP]))),
            excludedMiddle) 0

# Remove all outer universal quantifiers, returning the variables and a context in
# which those variables have been defined.
def
  stripForall '∀x. ‹p› x' =
    val [ctx,x,body] = destabs p
    context <ctx>
      match stripForall body
        case [ctx,xs,body] =>
          context <ctx>
            return [ctx,x <+ xs,body]
        case [body]        => return [ctx,[x],body]
  stripForall '‹x›' = [x]

def symConv '‹x› = ‹y›' =
  theorem left:
    assume asm:'‹x› = ‹y›'
    sym asm
  theorem right:
    assume asm:'‹y› = ‹x›'
    sym asm
  [equivalence (left,right)]

def taut tm =
  val [ctx,xs,body] = stripForall tm
  val basicRewrites =
    [notFalseTrue,notTrueFalse,
     orRightZero,orLeftZero,orRightId,orLeftId,
     andRightZero,andLeftZero,andRightId,orLeftId,
     eqTrueEq,eqFalseEq,
     convRule (randConv (absConv (landConv symConv)), eqTrueEq),
     convRule (randConv (absConv (landConv symConv)), eqFalseEq),
     topDefEq,impliesNotEqFalse,point,botDefEq]
  def
    tautAux [tm,(x <+ xs),rewrsAcc] =
      val '‹p› ∨ ‹notp›' as caseSplit = instantiate (boolCases,x)
      theorem tautology:
        theorem pCase:
          assume p:p
          tautAux (body, xs, (p <+ rewrsAcc))
        theorem notpCase:
          assume notp:notp
          tautAux (body, xs, (notp <+ rewrsAcc))
        matchmp (orDefEx,caseSplit,pCase,notpCase)
    tautAux ['‹p›:ℙ',[],rewrsAcc] =
      eqTrueElim (treeConv (rewrConv rewrsAcc) p 0)
  context <ctx>
    return tautAux (tm, xs, basicRewrites)

show taut '∀p q. (¬(p ∧ q)) = (¬p ∨ ¬q)'

# theorem orDeMorgan: '∀p q. (¬(p ∧ q)) = (¬p ∨ ¬q)'
#   let 'p:ℙ'
#   let 'q:ℙ'
#   let 'r:ℙ'
#   theorem left:
#     assume asm:'¬(p ∧ q)'
#     theorem qnotp:
#       assume q:'q:ℙ'
#       theorem notp:
#         assume p:'p:ℙ'
#         matchmp (andComplement,andIntro(andIntro (p,q),asm))
#       matchmp (impliesNot,notp)
#     # TODO: Need to intro disjunctions
#     matchmp (orDefEx,
#              instantiate (excludedMiddle,'q:ℙ'),
#              qnotp,
#              instantiate (trivImp,'¬q:ℙ'))
#   theorem right:
#     assume asm:'¬p ∨ ¬q'
#     theorem notpq:
#       assume pq:'p ∧ q'
#       theorem notp:
#         assume notp:'¬p'
#         matchmp (andComplement,andIntro(conjuncts pq 0,notp))
#       theorem notq:
#         assume notp:'¬q'
#         matchmp (andComplement,andIntro(conjuncts pq 1,notq))
#       matchmp (orDef,asm,notp,notq)
#     matchmp (impliesNot,notpq)

# def
#   transImp ['‹p› → ‹q›' as thm] =
#     val _ = assertThm thm
#     thm
#   transImp (('‹p› → ‹q›' as imp) <+ imps) =
#     theorem thm:
#       assume p:'‹p›'
#       modusponens (modusponens (p,imp),transImp imps)
#     thm

# theorem negInvolve: '∀p. (¬(¬p)) = p'
#   let 'p:ℙ'
#   theorem left:
#     assume nnp:'¬(¬p)'
#     theorem npp:
#       assume np:'¬p'
#       matchmp (andComplement, andIntro (np,nnp))
#     matchmp (\bootstrap\Connectives\orDef,
#              instantiate (excludedMiddle, 'p:ℙ'),
#              instantiate (trivImp, 'p:ℙ'),
#              transImp (npp, instantiate (botDef, 'p:ℙ')))
#   theorem right:
#     assume asm:'p:ℙ'
#     theorem npp:
#       assume np:'¬p'
#       matchmp (andComplement, andIntro (asm,np))
#     matchmp (gsym notDefEx, npp)
#   equivalence (left,right)

# choose hilbertChoiceDef: 'epsilonU:(𝒰 → ℙ) → 𝒰'
#   let 'p:𝒰 → ℙ'
#   assume ex:'∃x. p x'
#   choose 'chosen' ex

# theorem hilbertChoice:'∀ p x. p x → p (epsilonU p)'
#   let p:'p:𝒰 → ℙ'
#   let 'x'
#   assume assum:'p x'
#   theorem pExists:'∃ x. p x'
#     let ydef:'y = x'
#     modusponens (assum,combine (reflexive p,sym ydef))
#   modusponens (pExists,instantiate (hilbertChoiceDef,'p'))
