module
public import Theory.GroupTheory.NoncentralChiefRefinement.CubicComparison.SmallQuotients
public import Theory.GroupTheory.NoncentralChiefRefinement.ResidualRestriction.Comparison

/-!
# Bounding local cubic movement by the actual two-residual chief count

Above an S₃ two-core quotient, cubic movement on the full two-core counts a
complete chief series. Restricting and refining that series to O²(G) cannot
decrease its noncentral binary count. Jordan–Hölder invariance compares it
with any given complete chief series of the literal residual.

This retains the distinction between the two-residual and the two-core in
Aschbacher–Smith 13.4.7(4), printed p.903.
-/

public noncomputable section
open Subgroup
namespace NoncentralChiefRefinement.CubicComparison
variable {G : Type*} [Group G] [Finite G]

/-- The original residual chief count bounds cubic movement on the full local core. -/
theorem symmetricThree_core_length_le_residual_count
    (e : (G ⧸ pCore 2 G) ≃* Equiv.Perm (Fin 3))
    (E : Subgroup G) (hE : Nat.card E = 3)
    (t : ChiefSeries (pResidual 2 G)) (ht0 : t.head = ⊥) (ht1 : t.last = ⊤) :
    conjugationCubicLength E (pCore 2 G) ≤ t.noncentralTwoCount := by
  obtain ⟨s⟩ := SeriesOn.exists_series (⊤ : Subgroup G)
  obtain ⟨r,_,_,_,_,hr0,hr1,hr⟩ :=
    s.series.exists_complete_pResidual_refinement s.head_eq s.last_eq
  rw [r.noncentralTwoCount_eq t (hr0.trans ht0.symm) (hr1.trans ht1.symm)] at hr
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 G))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : f.ker = pCore 2 G := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  have hc := symmetricThree_count f hf (hk ▸ pCore_isPGroup) E hE
    s.series s.head_eq s.last_eq
  rw [hk] at hc
  exact hc ▸ hr
end NoncentralChiefRefinement.CubicComparison
