theory issue49 extends \root

val u = ': 𝒰'
val p = ': ℙ'

def fun(domain, range) = ': ‹domain› → ‹range›'

assert fun(fun(u, u), p) == ': (‹u› → ‹u›) → ‹p›' == ': (𝒰 → 𝒰) → ℙ'

assert 'union' == 'union : ‹fun(u, fun(u, u))›'

let 'x : ‹fun(u, fun(u, p))›'

assert 'x' == 'x : 𝒰 → 𝒰 → ℙ'