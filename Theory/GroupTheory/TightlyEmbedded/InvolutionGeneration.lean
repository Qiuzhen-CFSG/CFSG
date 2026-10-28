module

public import Theory.GroupTheory.TightlyEmbedded

/-!
# Centralizer generation and tightly embedded subgroups

The centralizer of an involution in a tightly embedded subgroup K lies
in N_G(K). Consequently, if the centralizers in L of the involutions of
D generate L, then D cannot lie in K unless L normalizes K. The same
argument excludes a nontrivial two-subgroup when each of its involutions,
together with a fixed involution, has centralizers generating L.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
the opening of 16.4.6 and the rank-one branch of 16.4.8, pp.1184, 1188.
The model-specific centralizer-generation equalities are separate inputs.
-/

public section

namespace Theory.GroupTheory

open Subgroup

variable {G : Type*} [Group G] [Finite G] {K L D : Subgroup G}

/-- Tight embedding controls the full ambient centralizer of an involution. -/
theorem IsTightlyEmbedded.involution_centralizer_le_normalizer
    (hK : IsTightlyEmbedded K) {r : G} (hrK : r ∈ K) (hr : orderOf r = 2) :
    centralizer ({r} : Set G) ≤ normalizer (K : Set G) := by
  have hp : IsPGroup 2 (zpowers r) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hr, pow_one])
  have hne : zpowers r ≠ ⊥ := by
    intro he
    have h1 : r = 1 := by
      have hm := mem_zpowers r
      rwa [he, mem_bot] at hm
    simp [h1] at hr
  have hc : centralizer ({r} : Set G) ≤ centralizer (zpowers r : Set G) := by
    rw [le_centralizer_iff, zpowers_le]
    intro x hx
    exact mem_centralizer_singleton_iff.mp hx
  exact hc.trans ((centralizer_le_normalizer _).trans
    (hK.normalizer_le hp hne (zpowers_le.mpr hrK)))

/-- The final centralizer-generation contradiction of the field-involution
case in 16.4.8, independent of its particular rank-one model. -/
theorem IsTightlyEmbedded.not_le_of_involution_centralizers_generate
    (hK : IsTightlyEmbedded K) (hnot : ¬ L ≤ normalizer (K : Set G))
    (hgen : (⨆ (r : G) (_ : r ∈ D) (_ : orderOf r = 2),
      L ⊓ centralizer ({r} : Set G)) = L) : ¬ D ≤ K := by
  intro hDK
  apply hnot
  rw [← hgen]
  refine iSup_le fun r => iSup_le fun hr => iSup_le fun hr2 => ?_
  exact inf_le_right.trans (hK.involution_centralizer_le_normalizer (hDK hr) hr2)

/-- If each involution of D pairs with r to generate L by centralizers,
then the two-subgroup D of K is trivial. This is the R₀ argument of 16.4.6. -/
theorem IsTightlyEmbedded.two_subgroup_eq_bot_of_pair_generation
    (hK : IsTightlyEmbedded K) (hnot : ¬ L ≤ normalizer (K : Set G))
    {r : G} (hrK : r ∈ K) (hr : orderOf r = 2)
    (hD : IsPGroup 2 D) (hDK : D ≤ K)
    (hgen : ∀ i : G, i ∈ D → orderOf i = 2 →
      (L ⊓ centralizer ({r} : Set G)) ⊔ (L ⊓ centralizer ({i} : Set G)) = L) :
    D = ⊥ := by
  rcases hD.card_eq_or_dvd with hcard | hdiv
  · exact D.eq_bot_iff_card.mpr hcard
  · obtain ⟨i, hi⟩ := exists_prime_orderOf_dvd_card' (G := D) 2 hdiv
    have hi2 : orderOf (i : G) = 2 := (orderOf_coe i).trans hi
    exfalso
    apply hnot
    rw [← hgen i i.property hi2]
    exact sup_le
      (inf_le_right.trans (hK.involution_centralizer_le_normalizer hrK hr))
      (inf_le_right.trans (hK.involution_centralizer_le_normalizer (hDK i.property) hi2))

end Theory.GroupTheory
