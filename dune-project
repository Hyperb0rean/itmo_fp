(lang dune 3.16)

(using coq 0.9)

(name rbtree)

(generate_opam_files true)

(source
 (github hyperb0rean/rbtree))

(authors "hyperb0rean")

(maintainers "hyperb0rean")

(license LICENSE)

(package
 (name rbtree)
 (synopsis "Verified rbtree")
 (description "see README.md")
 (depends ocaml dune)
 (tags
  (topics "to describe" your project)))
