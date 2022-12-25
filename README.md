# E-categories in Martin-Löf Type Theory

A little libray on e-categories with the aim of formalising stuff about the exact completion of a category with weak finite limits.
Hence the material is mainly about regular and exact categories, exact and left covering functors and projective covers.

The formalisation is in Agda 2.6.1 with the option `--without-K`.
The formalisation requires two universes which are taken to be the first two universes in Agda's hierarchy.

The repository contains:

tt-basics/  
Basic stuff in type theory needed for the theory of e-categories, including the definitions of setoid, extensional maps etc.

ecats/basic-defs/  
Definition of e-category in ecategory.agda, some notation for it, and definitions of several classes of arrows in a category. Definition of regular and exact category.

ecats/basic-props/  
Some properties of some of the stuff defined in ecats/basic-defs/.

ecats/concr-ecats/  
The categories of closed types and of setoids.

ecats/constructions/  
The ecategory of ecategories and that of (pseudo) equivalence relations. Proof that an exact category is a retract of its category of equivalence relations.

ecats/exact-completion/  
Definition of exact completion, Carboni and Vitale's construction and proof that exact completions are the embedding of projectives in exact categories with enough projectives.

ecats/finite-limits/  
Definitions of the main finite (weak) limits together with notation and some properties.

ecats/functors/  
Definition, notation and some properties of functors, exact and left covering functors, projective covers and natural transformations. The file props/basic-props.agda contains a proof that two essentially equivalent e-categories are equivalent.

