# Simply-Typed Lambda Calculus

The primary development is `Stlc.v` which features:

- preservation
- progress
- strong normalization

`Dep.v` & `Has.v` are partial developments
of the simply-typed lambda-calculus
with type-correct-by-construction syntax.
`Dep.v` is meant to be friendly for extraction
where identifiers are numbers
whereas `Has` is closer to
[Programming Language Foundations in Agda](https://plfa.github.io/DeBruijn/).