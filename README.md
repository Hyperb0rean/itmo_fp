# ITMO_FP

Сосновцев Григорий Алексеевич P34102

## Information

- Lab 1 - Project Euler
    - Largest palindrom-product of n-digits numbers
    - Largest prime factor of given number
- Lab 2 - Data Structures
    - Binary Tree


### Lab 1 - Project Euler

#### Largest Palindrome Product

[link](https://projecteuler.net/problem=4)
<p>A palindromic number reads the same both ways. The largest palindrome made from the product of two 2-digit numbers is $9009 = 91 x 99.</p>
<p>Find the largest palindrome made from the product of two 3-digit numbers.</p>


#### Largest Palindrome Product

[link](https://projecteuler.net/problem=3)
<p>The prime factors of 13195 are 5, 7, 13 and 29.</p>
<p>What is the largest prime factor of the number 600851475143?</p>


Turned out that calculating of such big number produces stackoverflow, so I fallbacked to smaller ones.

### Lab 2 - Data Structures

Implemented Red Black Tree in Coq

Supports:

- `insert` in O(logn)
- `lookup` in O(logn)
- `min/max` in O(logn)
- `union` in O(mlog(n/m + 1))
- `delete` via `split` + `union`
- `elements` into `list (k*V)` conversion


Based on 
- [Implementation of basic RBtree](https://koerbitz.me/posts/Red-Black-Trees-In-Coq-Part-0.html)
- [Basic RBtree from book](https://softwarefoundations.cis.upenn.edu/vfa-current/Redblack.html)
- [Wiki page on RBtrees](https://en.wikipedia.org/wiki/Red%E2%80%93black_tree)

### Materials

- [Software Foundations](https://softwarefoundations.cis.upenn.edu/)
- [Coq in a Hurry](https://cel.hal.science/inria-00001173) 
- [Why every programming student should learn Coq](https://rubber-duck-typing.com/posts/2018-03-11-why-every-programming-student-should-learn-coq.html) 