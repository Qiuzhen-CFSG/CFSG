module

public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.OddFourClosure.Reduction
public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

/-!+# The marked block-pair geometry for the SU₄ two-primary calculation

The stabilizer of an unordered orthogonal decomposition into two planes is
`(SL₂(q) × SL₂(q)) ⋊ D_{2(q+1)}`. In identity coordinates its dihedral
rotation is `diag(a,1,a⁻¹,1)`, for a generator a of the norm-one units,
and its reflection interchanges the two planes. The rotation lies in a
third SU₂, on the first and third coordinates. Both reflection generators
are conjugate in SU₄ to the sign on the first plane.

This module specifies those actual embeddings and conjugacies. It assumes
neither a covering lift nor an index assertion. Construction of this data,
and the independent proof that the displayed range has odd index, remain
geometric obligations. The conditional lifting and transfer application is
in `OddFourClosure.TwoPrimary`.

Source: the two-primary part of Aschbacher--Smith I.1.4(3), printed p.408
of `refs/quasithin.pdf`, citing GLS3 §6.1. The additional norm-one torus
is essential: the symplectic plane-pair subgroup alone has even index.
-/

public section

open BenderSuzuki.MatrixGroups

namespace Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.OddFourClosure.TwoPrimary

/-- The rank-one factor, over the actual prime field. -/
abbrev RankOne (q : ℕ) [Fact q.Prime] := Matrix.SpecialLinearGroup (Fin 2) (ZMod q)

/-- The concrete block-pair embedding, its transverse rank-one torus, and
the two involution fusions. Existence is not asserted by this definition. -/
structure BlockModel {F : Type*} [Field F] (J : HermitianForm 4 F)
    (q : ℕ) [Fact q.Prime] where
  action : DihedralGroup (q + 1) →* MulAut (RankOne q × RankOne q)
  inclusion : (RankOne q × RankOne q) ⋊[action] DihedralGroup (q + 1) →*
    J.specialSubgroup
  injective : Function.Injective inclusion
  transverse : RankOne q →* J.specialSubgroup
  transverse_injective : Function.Injective transverse
  torus : RankOne q
  torus_pow : torus ^ (q + 1) = 1
  rotation_eq : transverse torus = inclusion (SemidirectProduct.inr (.r 1))
  reflection_zero_conjugate : IsConj (inclusion (SemidirectProduct.inl (-1, 1)))
    (inclusion (SemidirectProduct.inr (.sr 0)))
  reflection_one_conjugate : IsConj (inclusion (SemidirectProduct.inl (-1, 1)))
    (inclusion (SemidirectProduct.inr (.sr 1)))

end Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.OddFourClosure.TwoPrimary
