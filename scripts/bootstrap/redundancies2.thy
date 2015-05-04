theory Redundancies2
extends Lift

let upairDef: 'upair = (x y ↦ repl two (z ↦ ifThenElse (z = ∅) x y))'

theorem upair:'∀x y z. z ∈ upair x y = (z = x ∨ z = y)'
  let 'x'
  let 'y'
  theorem '∀z. z ∈ upair x y = (z = x ∨ z = y)'
    by metisGen (seqConv [upConv (rewrConv upairDef), metisPreConv],
                 [ifTrue, ifFalse, oneNotZero, two,
                  instantiate (repl, 'two', 'z ↦ ifThenElse (z = ∅) x y')])

let singleDef: 'single = (x ↦ upair x x)'

theorem single: '∀x y. y ∈ single x = (x = y)'
  by metisGen (seqConv [upConv (rewrConv singleDef), metisPreConv], [upair])
