### Lab 2 - Data Structures

Implemented Red Black Tree in Coq

Supports:

- `insert` in O(logn)
- `lookup` in O(logn)
- `min/max` in O(logn)
- `union` in O(mlog(n/m + 1))
- `delete` via `split` + `union`
- `elements` into `list (k*V)` conversion
- `foldr` for tree traversal
- `rbtree_eqb` for tree comparison on equality

Some prooven theorems:

- `(Red_black_tree, union)` is monoid, with `nil` as neutral. (TODO)
- `Red_black_tree` has `Binary Search Tree` invariant (TODO)
- `Red_black_tree` has `Balanced` invariant (TODO)


Based on 
- [Implementation of basic RBtree](https://koerbitz.me/posts/Red-Black-Trees-In-Coq-Part-0.html)
- [Basic RBtree from book](https://softwarefoundations.cis.upenn.edu/vfa-current/Redblack.html)
- [Wiki page on RBtrees](https://en.wikipedia.org/wiki/Red%E2%80%93black_tree)
- [Verified RBtrees](https://www.cs.princeton.edu/~appel/papers/redblack.pdf)