theory Automation extends \root

context
  assume t: '∀ p. p → p'
  theorem s : t 
  show s

failure theorem imp: '∀ p. p → p' .

failure theorem '∀ p. p → p' by nil 

failure theorem '∀ q. q → q' by imp

