theory Syntax
extends root

# Basic term tools

val destconj = '‹p› ∧ ‹q›' => [p, q]

val desteq = tm =>
  match tm
    case '‹p› = ‹q›' => [[p,q]]
    case _           => []

val lhs = tm =>
  for [l,_] in desteq tm do
    l

val rhs = tm =>
  for [_,r] in desteq tm do
    r

