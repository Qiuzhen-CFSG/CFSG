module
public import Theory.GroupTheory.GeneralizedFitting.SylowNormalizedComponent
public import Theory.GroupTheory.ConjugateSpanSylow
public import Theory.Quasithin.Rank

/-!
# Sylow orbits of C-components in odd rank at most two

When the solvable radical is the two-core, odd-prime ranks decrease in the
radical quotient. An ordinary component there has at most two conjugates.
Component normalizers lift through the radical, so the original component
also has at most two conjugates and its Sylow two-orbit is normal.

Source: Aschbacher--Smith A.3.8(3), used in 14.6.20, printed pp.46 and1037.
-/

public section
open Subgroup Theory.GroupTheory
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

theorem IsCComponent.normal_or_index_two_of_radical_eq_core
    {K : Subgroup G} (hK : K.IsCComponent)
    (hR : solvableRadical G = pCore 2 G)
    (hr : ∀ p : ℕ, p.Prime → Odd p → primeRank p G ≤ 2) :
    K.Normal ∨ (normalizer (K : Set G)).index = 2 := by
  let R := solvableRadical G
  let q := QuotientGroup.mk' R
  have hc : IsComponent (G ⧸ R) (K.map q) := map_cComponent_isComponent_of_solvableRadical hK
  apply cComponent_normal_or_index_two_of_quotient hK R
  apply hc.normal_or_index_two_of_odd_rank_le_two
  intro p hp ho
  let : Fact p.Prime := ⟨hp⟩
  exact (primeRank_quotient_le_of_isTwoGroup p ho R (pCore_isPGroup.to_le hR.le)).trans (hr p hp ho)

theorem IsCComponent.sylow_orbit_normal_of_radical_eq_core
    {K : Subgroup G} (hK : K.IsCComponent)
    (hR : solvableRadical G = pCore 2 G)
    (hr : ∀ p : ℕ, p.Prime → Odd p → primeRank p G ≤ 2) (T : Sylow 2 G) :
    (conjugateSpanBy K (T : Subgroup G)).Normal :=
  conjugateSpanBy_sylow_normal K T (hK.normal_or_index_two_of_radical_eq_core hR hr)
end Subgroup
