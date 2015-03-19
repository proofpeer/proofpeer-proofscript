theory issue52 extends \root

let p: 'p : 𝒰 → 𝒰 → ℙ'

val v = ': 𝒰 → ℙ'

match p 
  case '‹_› : ‹v› → ‹u›' =>
    assert u == ': 𝒰 → ℙ'
    assert v == ': 𝒰'

match p 
  case '‹_› : ‹v› → «v»' =>
    assert v == ': 𝒰'

let x: 'x'
let y: 'y'

val px = 'p x'

match 'p x y'
  case '«px» ‹a›' =>
    assert a == 'y'


