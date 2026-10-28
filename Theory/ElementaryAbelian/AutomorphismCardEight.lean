module

public import Theory.ElementaryAbelian.AutomorphismLinearModelEight
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.Tactic.NormNum

/-!
# Automorphism count for an elementary abelian group of order eight

The full automorphism group of a finite elementary abelian two-group of order
eight has order 168. This standard elementary-group calculation is used in
the small elementary-core analysis of Stellmacher Section 11 and in the
normalizer recognition of (9.1)(c); it needs no campaign hypotheses.

The shared `elementaryEight_mulAut_equiv_GL` theorem identifies automorphisms
with `GL₃(𝔽₂)` using the actual group and its associated vector space. Transport
cardinality along that equivalence and apply `Matrix.card_GL_field`, which
counts ordered bases. The three successive choices give
`(8 - 1) * (8 - 2) * (8 - 4) = 168`.
-/

universe u

/-- An elementary abelian two-group of order eight has 168 automorphisms. -/
public theorem card_mulAut_of_elementary_eight
    (E : Type u) [Group E] [Finite E] [IsElementaryAbelian 2 E]
    (hE : Nat.card E = 8) : Nat.card (MulAut E) = 168 := by
  obtain ⟨equiv⟩ := elementaryEight_mulAut_equiv_GL E hE
  rw [Nat.card_congr equiv.toEquiv, Matrix.card_GL_field]
  norm_num [Fin.prod_univ_succ, ZMod.card]
