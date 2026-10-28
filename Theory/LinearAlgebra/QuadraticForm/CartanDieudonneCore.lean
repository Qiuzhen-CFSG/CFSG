module

public import Theory.LinearAlgebra.QuadraticForm.Wall

/-!
# Cartan--Dieudonne factorization over arbitrary fields

This module proves the existence core of Cartan--Dieudonne for a finite-dimensional
nondegenerate quadratic space over a field where `2` is invertible.  Every quadratic
isometry is an ordered product of at most the ambient dimension many anisotropic
reflections, using the reflection definition from `Reflection`.

The proof follows Wall's residual-form reduction.  When the Wall form is
nonalternating, a carefully selected anisotropic moved vector lowers the moved-space
rank by one while preserving nonalternation until rank zero; induction therefore
uses exactly the original moved rank many reflections.  When the Wall form is
alternating, the moved space is totally isotropic.  Wall's exceptional adjustment
adds one preliminary reflection and raises the rank by one to enter the
nonalternating branch; the isotropic-space estimate `rank + 2 <= dim V` absorbs this
two-reflection detour.  This is the arbitrary-field step absent from fixed-space
proofs specialized to positive-definite real forms, and is the classical
Cartan--Dieudonne argument in Wall's residual-form formulation.
-/

open Module
open QuadraticMap

namespace QuadraticForm

variable {k V : Type*} [Field k] [Invertible (2 : k)]
variable [AddCommGroup V] [Module k V] [FiniteDimensional k V]

omit [FiniteDimensional k V] in
private theorem reflection_mul_of_eq_reflection_apply
    (Q : QuadraticForm k V) (g h : Q.IsometryEquiv Q)
    (v : V) (hv : Q v ≠ 0)
    (hh : ∀ x, h x = anisotropicReflection Q v hv (g x)) :
    g.toLinearEquiv = anisotropicReflection Q v hv * h.toLinearEquiv := by
  ext x
  change g x = anisotropicReflection Q v hv (h x)
  rw [hh]
  exact (anisotropicReflection_involutive Q v hv (g x)).symm

private theorem factorNonalternating
    (Q : QuadraticForm k V) (hQ : Q.Nondegenerate)
    (g : Q.IsometryEquiv Q) (hnotAlt : ¬(wallForm Q g).IsAlt) :
    ∃ vs : List {v : V // Q v ≠ 0},
      vs.length = finrank k (wallMovedSpace Q g) ∧
      g.toLinearEquiv = anisotropicReflectionsProduct Q vs := by
  induction hdim : finrank k (wallMovedSpace Q g) using Nat.strong_induction_on generalizing g with
  | h n ih =>
      obtain ⟨u, hu, h, hh, hrank, hpreserve⟩ :=
        exists_wallRankDrop_preserving_not_isAlt Q hQ g hnotAlt
      by_cases hzero : finrank k (wallMovedSpace Q h) = 0
      · have hgRank : finrank k (wallMovedSpace Q g) = 1 := by omega
        have hrefl : h = QuadraticMap.IsometryEquiv.refl Q :=
          eq_refl_of_finrank_wallMovedSpace_eq_zero Q h hzero
        refine ⟨[⟨u, hu⟩], by exact hgRank.symm.trans hdim, ?_⟩
        rw [anisotropicReflectionsProduct_cons, anisotropicReflectionsProduct_nil]
        have heq := reflection_mul_of_eq_reflection_apply Q g h (u : V) hu hh
        rw [hrefl] at heq
        exact heq
      · have hpos : 0 < finrank k (wallMovedSpace Q h) := Nat.pos_of_ne_zero hzero
        have hlt : finrank k (wallMovedSpace Q h) < n := by omega
        obtain ⟨vs, hlen, heq⟩ := ih _ hlt h (hpreserve hpos) rfl
        refine ⟨⟨(u : V), hu⟩ :: vs, ?_, ?_⟩
        · simp [hlen]
          omega
        · rw [anisotropicReflectionsProduct_cons, ← heq]
          exact reflection_mul_of_eq_reflection_apply Q g h (u : V) hu hh

/-- **Cartan--Dieudonne, existence form.**  A quadratic isometry of a
finite-dimensional nondegenerate quadratic space is a product of at most the
ambient dimension many anisotropic reflections. -/
public theorem cartanDieudonne
    (Q : QuadraticForm k V) (hQ : Q.Nondegenerate)
    (g : V ≃ₗ[k] V) (hg : ∀ x, Q (g x) = Q x) :
    ∃ vs : List {v : V // Q v ≠ 0},
      vs.length ≤ finrank k V ∧ g = anisotropicReflectionsProduct Q vs := by
  let gi : Q.IsometryEquiv Q := ⟨g, hg⟩
  by_cases hAlt : (wallForm Q gi).IsAlt
  · by_cases hzero : finrank k (wallMovedSpace Q gi) = 0
    · have hrefl := eq_refl_of_finrank_wallMovedSpace_eq_zero Q gi hzero
      refine ⟨[], by simp, ?_⟩
      rw [anisotropicReflectionsProduct_nil]
      rw [← show gi.toLinearEquiv = g by rfl, hrefl]
      rfl
    · have hpos : 0 < finrank k (wallMovedSpace Q gi) := Nat.pos_of_ne_zero hzero
      obtain hrefl | hdrop | ⟨_, _, hbound, v, hv, h, hh, hrank, hnotAlt⟩ :=
        wallResidualReduction Q hQ gi
      · have hz : finrank k (wallMovedSpace Q gi) = 0 := by
          rw [hrefl]
          exact finrank_wallMovedSpace_refl_eq_zero Q
        omega
      · obtain ⟨u, hu, h, hh, hrank⟩ := hdrop
        exact (hu (wallMoved_isotropic_of_isAlt Q gi hAlt u)).elim
      obtain ⟨vs, hlen, heq⟩ := factorNonalternating Q hQ h hnotAlt
      refine ⟨⟨v, hv⟩ :: vs, ?_, ?_⟩
      · simp [hlen, hrank]
        omega
      · rw [anisotropicReflectionsProduct_cons, ← heq]
        simpa [gi] using reflection_mul_of_eq_reflection_apply Q gi h v hv hh
  · obtain ⟨vs, hlen, heq⟩ := factorNonalternating Q hQ gi hAlt
    refine ⟨vs, ?_, ?_⟩
    · rw [hlen]
      exact Submodule.finrank_le (wallMovedSpace Q gi)
    · simpa [gi] using heq

end QuadraticForm
