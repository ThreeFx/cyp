<Datatype>
# Tree a = Leaf | Node a (Tree a) (Tree a)
<Datatype>
<Sym>
# (++)
# (+)
# tail
# length
# reverse
<Sym>
<Def>
<Def>
<Lemma>

<Lemma>
<Induction>
length (reverse t) = length t
<Induction>
<Over>
t
<Over>
<Leaf>
length (reverse Leaf) = length Leaf
<Leaf>
<Node>
length (reverse (Node 0 a b)) = length (Node 0 a b)
<Node>
