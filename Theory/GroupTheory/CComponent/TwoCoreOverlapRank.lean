module
public import Theory.GroupTheory.CComponent.TwoCorePrimeActors
public import Theory.GroupTheory.GeneralizedFitting.ComponentOverlapRank
public import Theory.GroupTheory.PrimeRankResidualCentralizer

/-!
# Normalizing a C-component from the rank of its overlap

Let C have quasisimple, centerless quotient by its own two-core.
For an odd prime p, a subgroup M of rank less than twice the rank of
M ∩ C normalizes C. Pass to the ambient two-core quotient, where C
becomes an ordinary centerless component. Odd prime ranks survive the
quotient, and the ordinary commuting-component rank argument applies.
Normalization then lifts through the solvable kernel.

Source: the commuting-component theorem, GLS vol.2, Theorem 3.5;
the exchanged-component argument in Aschbacher–Smith 5.2.2, pp.648–649.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace Subgroup

variable {G : Type*} [Group G] [Finite G]

/-- Insufficient odd prime rank for two conjugate overlaps forces
normalization of the original C-component, before quotienting its two-core. -/
theorem IsCComponent.normalizes_of_overlap_primeRank
    {C M : Subgroup G} (hC : C.IsCComponent)
    [IsQuasisimple (C ⧸ pCore 2 C)]
    (hz : center (C ⧸ pCore 2 C) = ⊥)
    (p : ℕ) [Fact p.Prime] (ho : Odd p)
    (hr : primeRank p M < 2 * primeRank p (M ⊓ C : Subgroup G)) :
    M ≤ normalizer (C : Set G) := by
  let q := QuotientGroup.mk' (pCore 2 G)
  have hk : IsPGroup 2 q.ker := by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup
  let e := cComponentTwoCoreQuotientEquiv hC
  have hz' : center (C.map q) = ⊥ := by
    apply eq_bot_iff.mpr
    intro x hx
    have hh := ((centerCongr e.symm) ⟨x,hx⟩).property
    change e.symm x ∈ center (C ⧸ pCore 2 C) at hh
    rw [hz] at hh
    exact e.symm.map_eq_one_iff.mp (mem_bot.mp hh)
  have hl := primeRank_mono p (map_inf_le (f := q) (H := M) (K := C))
  rw [ResidualCentralizerRank.primeRank_map_of_twoGroup_kernel ho q hk] at hl
  have hr' : primeRank p (M.map q) < 2 * primeRank p (M.map q ⊓ C.map q : Subgroup _) := by
    rw [ResidualCentralizerRank.primeRank_map_of_twoGroup_kernel ho q hk]
    omega
  have hn := (CComponentPrimeRank.twoCore_image_isComponent hC).normalizes_of_overlap_primeRank hz' p hr'
  let := (pCore_isPGroup (p := 2) (G := G)).isNilpotent
  rw [←normalizer_cComponent_quotient hC (pCore 2 G)]
  exact map_le_iff_le_comap.mp hn

end Subgroup
