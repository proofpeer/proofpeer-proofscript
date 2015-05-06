theory Redundancies2
extends Lift

let upairDef: 'upair = (x y ↦ repl two (z ↦ ifThenElse (z = ∅) x y))'

theorem upair:'∀x y z. z ∈ upair x y = (z = x ∨ z = y)'
  let 'x'
  let 'y'
  theorem '∀z. z ∈ upair x y = (z = x ∨ z = y)'
    by metisGen (seqConv [rewriteConv upairDef, metisPreConv],
                 [ifTrue, ifFalse, oneNotZero, two,
                  instantiate (repl, 'two', 'z ↦ ifThenElse (z = ∅) x y')])

let singleDef: 'single = (x ↦ upair x x)'

theorem single: '∀x y. y ∈ single x = (x = y)'
  by metisGen (seqConv [rewriteConv singleDef, metisPreConv], [upair])

let comprehensionDef:
  'comprehend = (A ↦ p ↦ ⋃ (repl A (x ↦ ifThenElse (p x) (single x) ∅)))'

# Lots of conversion needed here. Replacement is used as an argument to Union,
# so the lambda won't be eliminated unless we unfold the union axiom.
theorem comprehension: '∀p A. ∀x. x ∈ comprehend A p = (x ∈ A ∧ p x)'
  let 'p:𝒰 → ℙ'
  let 'A:𝒰'
  theorem '∀x. (x ∈ comprehend A p) = (x ∈ A ∧ p x)'
    by metisGen
      (seqConv [treeConv (sumConv [rewrConv [comprehensionDef, Union],
                                   expandForallIn, expandExistsIn]),
                metisPreConv],
      [ifTrue, ifFalse, empty, single,
       instantiate (repl,'A','x ↦ ifThenElse (p x) (single x) ∅')])

let unionDef: 'finunion = (x ↦ y ↦ ⋃ (upair x y))'

# METIS receives
#
#   fof(0, unknown, element(k(V00,V1,V2),union(upair(f(V00,V1,V2),g(V00,V1,V2)))) | element(k(V00,V1,V2),g(V00,V1,V2)) | element(k(V00,V1,V2),f(V00,V1,V2))).
#   fof(1, unknown, ~ element(k(V00,V1,V2),union(upair(f(V00,V1,V2),g(V00,V1,V2)))) | ~ element(k(V00,V1,V2),g(V00,V1,V2))).
#   fof(2, unknown, ~ element(k(V00,V1,V2),union(upair(f(V00,V1,V2),g(V00,V1,V2)))) | ~ element(k(V00,V1,V2),f(V00,V1,V2))).
#   fof(3, unknown, element(V2,upair(V00,V1)) | ~ V2=V00).
#   fof(4, unknown, element(V2,upair(V00,V1)) | ~ V2=V1).
#   fof(5, unknown, ~ element(V2,upair(V00,V1)) | V2=V1 | V2=V00).
#   fof(6, unknown, ~ element(V2,V1) | ~ element(V00,V2) | element(V00,union(V1))).
#   fof(7, unknown, element(V00,h(V00,V1)) | ~ element(V00,union(V1))).
#   fof(8, unknown, element(h(V00,V1),V1) | ~ element(V00,union(V1))).
#
# SPASS and Vampire claim that this (negated) conjecture is unsatisfiable (and thus
# theorem holds) METIS doesn't get a solution before exhausting all sammon's memory.
# E as provided by the TPTP server times out.
#
# theorem badUnion: '∀x y z. z ∈ finunion x y = (z ∈ x ∨ z ∈ y)'
#   by metisGen
#     (seqConv [rewriteConv unionDef, metisPreConv], [Union,upair])

# METIS can prove this version, assisted by initial simplification steps.
theorem finUnion: '∀x y z. z ∈ finunion x y = (z ∈ x ∨ z ∈ y)'
  by metisGen
    (treeConv (sumConv [rewrConv [unionDef, Union], expandForallIn, expandExistsIn]),
              [upair])
