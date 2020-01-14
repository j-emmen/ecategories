# E-categories in Martin-Löf Type Theory

A little libray on e-categories with the aim of formalising the exact completion of a category with weak finite limits. Hence the material is mainly about regular and exact categories, left covering functors and projective covers.

The formalisation is in Agda 2.5.4.1.

The repository contains:

tt-basics/  
Basic stuff in type theory, including the definitions of setoid, extensional map etc.

ecats/basic-defs/  
Contains the definition of e-category in ecategory.agda, some notation for it,
definitions of regular and exact e-category and definitions of some properties of arrrows in a category.

ecats/basic-props/  
Some basic properties of some of the stuff defined in ecats/basic-defs/.

ecats/finite-limits/  
Definitions of the main finite limits together with notation and basic properties.

ecats/functors/  
Definition, notation and basic properties of functors, exact and left coverinf functors and projective covers.
The file props/basic-props.agda contains a proof that an essential equivalence of e-categories is an equivalence.

ecats/exact-completion/  
Construction of the exact completion, proof that it is exact and proof that the embedding is a projective cover.
