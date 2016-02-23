theory Bar extends Foo

def checkType (ty : Type) : Boolean = 
  'someEntity' == 'someEntity : ‹ty›'

def<context> checkTypeHere (ty : Type) : Boolean = 
  checkType ty  

assert checkType ': 𝒰'
assert checkTypeHere ': 𝒰'

let 'someEntity : ℙ'

def checkType2 (ty : Type) : Boolean = 
  'someEntity' == 'someEntity : ‹ty›'

assert checkType2 ': ℙ'
assert checkType ': 𝒰'
assert checkTypeHere ': 𝒰'


