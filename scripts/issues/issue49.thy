theory issue49 extends \root

val u = ': 𝒰'
val p = ': ℙ'

def fun(domain, range) = ': ‹domain› → ‹range›'

assert fun(fun(u, u), p) == ': (‹u› → ‹u›) → ‹p›' == ': (𝒰 → 𝒰) → ℙ'

assert 'union' == 'union : ‹fun(u, fun(u, u))›'

let 'x : ‹fun(u, fun(u, p))›'

assert 'x' == 'x : 𝒰 → 𝒰 → ℙ'

match fun(u, p)
  case ': ‹domain› → ‹range›' =>
    assert domain == u
    assert range == p
  case _ =>
    assert false

def typeOf '‹_› : ‹ty›' = ty

match 'x'
  case 'x : ‹domain› → ‹range› : ‹xty›' =>
    assert domain == u
    assert range == ': 𝒰 → ℙ'
    assert xty == ': 𝒰 → 𝒰 → ℙ'
  case _ =>
    assert false

assert typeOf 'x' == ': 𝒰 → 𝒰 → ℙ'

