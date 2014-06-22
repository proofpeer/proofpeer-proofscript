theory \examples\DataTypes extends \root

# These are the boolean literals:
show true
show false

# These are some integer literals:
show 42
show -1

# These are a few strings,
  some of them contain unicode characters specified
  by their codepoint:
show "Hello World"
show "symbol for universal type: \U0001D4B0"
show "symbol for type of propositions: \U00002119"
show "again, the symbol for the type of propositions: \u2119"
show "this namespace: \\examples\\DataTypes"
show "you can also have \n and \" in a string"

# This is a vector literal
show [1, 2, "hello", false]

# This is a vector literal denoting the same vector
show (1, 2, "hello", false)

# This is a single element vector containing 7
show [7] 

# and this is just the number 7, not a vector
show (7)
