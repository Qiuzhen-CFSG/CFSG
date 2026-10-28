module

public import CFSG.Quasithin.ChapterK.Section01To04.Symplectic.TensorGeometry.Outer.ModelGeometry.ScalarExtension
public import CFSG.Quasithin.ChapterK.Section01To04.Symplectic.TensorGeometry.Outer.ModelGeometry.Sections
public import CFSG.Quasithin.ChapterK.Section01To04.Symplectic.TensorGeometry.Outer.ModelGeometry.CommonFixed

/-!
# Geometry of the genuine Hermitian symplectic tensor model

The canonical scalar-extension equivalence intertwines the Hermitian action
with the literal twisted matrix action. The model, field-fixed space,
displacement and fixed/displacement quotient have dimensions 16, 10, 6 and 4.
The native field centralizer acts faithfully on both sections; diagonal
coordinates identify the middle section with the coefficient-Frobenius
natural four-space through an injective entrywise descent.

The actual section filtration bounds the common fixed dimension by eight
for every nontrivial native subgroup, strictly below eight at order `|k|³`.
This includes the binary base field. Scalar restriction gives fixed dimension
`10s` and common-fixed codimension at least `8s`, strictly greater at maximal
native rank. Original-module transport and ambient subgroup placement remain
with the outer-action assembly.

Source: Aschbacher–Smith, K.3.4.2, printed pp.456–457, and H.4.4(6), p.381.
-/
