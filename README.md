# E-categories in Martin-Löf Type Theory

A little libray on e-categories with the aim of formalising the exact completion of a category with weak finite limits.
Hence the material is mainly about regular and exact categories, exact and left covering functors and projective covers.

The formalisation is in Agda 2.5.4.1 with the option `--without-K`.
The formalisation requires two universes which are taken to be the first two universes in Agda's hierarchy.

The repository contains:

tt-basics/  
Basic stuff in type theory needed for the theory of e-categories, including the definitions of setoid, extensional map etc.

ecats/basic-defs/  
Definition of e-category in ecategory.agda, some notation for it,
definitions of regular and exact e-category and definitions of some properties of arrrows in a category.

ecats/basic-props/  
Some basic properties of some of the stuff defined in ecats/basic-defs/.

ecats/finite-limits/
Definitions of the main finite (weak) limits together with notation and basic properties.

ecats/functors/  
Definition, notation and basic properties of functors, exact and left covering functors, projective covers and natural transformations. The file props/basic-props.agda contains a proof that two essentially equivalent e-categories are equivalent.

ecats/constructions/  
Definition of the e-category of small e-categories. Definition of the e-category of equivalence relations of an e-category, and proof that an exact e-category is a retract of its e-category of equivalence relations.

ecats/exact-completion/  
Construction of the exact completion. Proof that it is exact, that the embedding is a projective cover and that it is universal among left covering functors into exact categories. Chracterisation of exact completions as exact categories with enough projectives.
