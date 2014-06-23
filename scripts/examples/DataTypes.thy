theory \examples\DataTypes extends \root

# This is the nil literal:
show nil

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
assert (1, 2, "hello", false) == [1, 2, "hello", false]

# This is a single element vector containing 7
show [7] 

# and this is just the number 7, not a vector
show (7)

# This is a function literal
show x => x * x

# here we apply this function literal to 7
show (x => x * x) 7

# You can convert integers into strings 
assert string (2 - 5) == "-3" 

# This is a comparison chain, which is true if every single member of the chain is true
assert 1 < 3 < 5 < 7 < 7 * 7 == 49 < 50 <= 50 <= 100 > 99

# The order for strings is lexicographic 
assert "ac" < "b"

# But for vectors it is elementwise
assert not ["a", "c"] <= ["b"]
assert not ["a", "c"] >= ["b"]
assert ["a", "c"] < ["b", "d"]

# Comparisons between values of different types always yields false, except for
  inequality, which always yields true
assert not 1 <= "1"
assert not 1 < "1"
assert not 1 == "1"
assert 1 <> "1"
assert nil <> (x => x)

# Functions cannot be compared with each other
failure (x => x) == (x => x)
failure (x => x) <> (x => x)