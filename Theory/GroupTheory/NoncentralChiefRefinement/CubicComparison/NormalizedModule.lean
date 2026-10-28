module
public import Theory.GroupTheory.NoncentralChiefRefinement.CubicComparison.SmallQuotients
public import Theory.GroupTheory.NoncentralChiefRefinement.CubicComparison.FixedIndex
public import Theory.GroupTheory.NoncentralChiefRefinement.CubicComparison.Bounds
public import Theory.GroupTheory.PCoreLocalSetup
/-!
# Chief counts from a mutually normalized binary module

For an actor whose quotient over its two-core has order three, every
complete noncentral binary chief count equals its cubic fixed length.
A mutually normalized two-group contributes that same length on its
intersection with the actor. This intersection is normal in the actor
and hence lies in its two-core, giving a lower bound for the chief count.

Source application: Aschbacher–Smith 13.4.12, printed pp.910–911.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace NoncentralChiefRefinement.CubicComparison
variable {G : Type*} [Group G] [Finite G]

theorem count_ge_of_normalized_module (R U A : Subgroup G)
    (hR : Nat.card (R ⧸ pCore 2 R) = 3)
    (hU : IsPGroup 2 U) (hA : Nat.card A = 3) (hAR : A ≤ R)
    (hUR : U ≤ normalizer (R : Set G)) (hRU : R ≤ normalizer (U : Set G))
    {n : ℕ} (hn : n ≤ conjugationCubicLength A U)
    (s : ChiefSeries R) (h0 : s.head = ⊥) (h1 : s.last = ⊤) :
    n ≤ s.noncentralTwoCount := by
  have hi := intersection_length_eq A U R
    (IsPGroup.of_card (n := 1) (by simpa using hA)) hU hAR hUR hRU
  have hnR : R ≤ normalizer ((U ⊓ R : Subgroup G) : Set G) :=
    (le_inf hRU R.le_normalizer).trans inf_normalizer_le_normalizer_inf
  have hcore : U ⊓ R ≤ R.pCoreIn 2 := le_pCoreIn_of_normalizes
    (hU.to_le inf_le_left) inf_le_right hnR
  have hb := conjugationCubicLength_mono A hcore
  have hAi : Nat.card (A.subgroupOf R) = 3 :=
    (Nat.card_congr (subgroupOfEquivOfLe hAR).toEquiv).trans hA
  have hc := count_of_core_quotient_card_three hR (A.subgroupOf R) hAi s h0 h1
  have he := length_map_injective R.subtype R.subtype_injective
    (A.subgroupOf R) (pCore 2 R)
  rw [map_subgroupOf_eq_of_le hAR] at he
  change conjugationCubicLength A (R.pCoreIn 2) = _ at he
  omega
end NoncentralChiefRefinement.CubicComparison
