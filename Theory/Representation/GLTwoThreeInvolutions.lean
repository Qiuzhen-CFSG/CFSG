module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Tactic

/-!
# Scalar inversion in an elementary order-four matrix group

Two distinct commuting nonidentity involutory two-by-two matrices over
the field of three elements generate a group of order four containing
the scalar matrix `-1`. Equivalently, one of the two matrices or their
product is `-1`. Their involution equations imply invertibility, so no
additional unit hypotheses are needed.

The proof is a kernel-checked finite calculation on the 81 matrices.
The scoped synthesis bound accommodates the decidability instance for
the multiple explicit hypotheses; no native evaluation axiom is used.

This supplies the inversion element in an elementary order-four group
acting faithfully on an elementary group of order nine, used in the
group identification in Stellmacher (1.6), journal p.18,
`refs/latex/stellmacher-n-group.tex`.
-/

set_option synthInstance.maxSize 256 in
/-- A commuting pair of distinct nonidentity involutions in two dimensions
over `ZMod 3` generates the scalar inversion. -/
public theorem Matrix.commuting_distinct_involutions_two_three_neg_one
    (a b : Matrix (Fin 2) (Fin 2) (ZMod 3))
    (ha : a * a = 1) (hb : b * b = 1) (hab : a * b = b * a)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hne : a ≠ b) :
    a = -1 ∨ b = -1 ∨ a * b = -1 := by
  revert a b
  decide +kernel
