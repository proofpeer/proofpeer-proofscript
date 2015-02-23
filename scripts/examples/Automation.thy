theory Automation extends \root

failure theorem imp: '∀ p. p → p' .

failure theorem '∀ p. p → p' by nil

failure theorem '∀ q. q → q' by [imp]

failure theorem '∀ q. q → q' by imp
