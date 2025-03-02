## Verified Red Black Tree

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

- `Red_black_tree` preserves `Binary Search Tree` invariant on `nil` and inserts
- `elements` prooven correct and complete
- `elements` has `sorted` invariant
- `Red_black_tree` has `Balanced` invariant (TODO)


Based on 
- [Implementation of basic RBtree](https://koerbitz.me/posts/Red-Black-Trees-In-Coq-Part-0.html)
- [Basic RBtree from book](https://softwarefoundations.cis.upenn.edu/vfa-current/Redblack.html)
- [Wiki page on RBtrees](https://en.wikipedia.org/wiki/Red%E2%80%93black_tree)
- [Verified RBtrees](https://www.cs.princeton.edu/~appel/papers/redblack.pdf)