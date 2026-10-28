module

public import BenderSuzuki.ZD.Recognition.MinimalReduction.Radical.Quotient
public import Theory.GroupTheory.CentralTwoQuotientOddCore

/-!
# The structural branch in a central two-quotient

A nontrivial central two-quotient of a minimal ZD counterexample satisfies
ZD by the proved product-disconnection descent. Its rank-one alternative
would make a distinguished involution central modulo the quotient odd core.
Sylow centrality lifts this through the central two-kernel, making the
original involution central modulo the original odd core. When that core is
trivial, this contradicts product disconnection. Thus the quotient satisfies
every clause of the structural alternative.

Source: GLS, Volume 4, Chapter 2, Lemma 4.5, printed p. 35 (PDF p. 52).
Reconstructing the full conclusion upstairs still requires the source's
central-extension argument for Bender groups.
-/

namespace BenderSuzuki.ZD
open Theory.GroupTheory PFAppendixIII PFchapter1section1
universe u
variable {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

/-- A nontrivial central two-quotient lies in the structural induction branch
once the ambient odd core has been eliminated. -/
public theorem MinimalCounterexample.central_quotient_structure
    (h : MinimalCounterexample Z M) (hgen : Subgroup.closure Z = ⊤)
    (hcentral : ∀ z ∈ Z, ∃ S : Sylow 2 G, z ∈ S ∧ ∀ s : S, Commute z (s : G))
    (hfusion : ∃ S : Sylow 2 G, (S : Subgroup G) ≤ M ∧ ControlsFusionIn M (S : Subgroup G))
    (hodd : pPrimeCore 2 G = ⊥)
    (A : Subgroup G) [A.Normal] (hAc : A ≤ Subgroup.center G)
    (hAp : IsPGroup 2 A) (hne : A ≠ ⊥) :
    StructureConclusion ((QuotientGroup.mk' A) '' Z) (M.map (QuotientGroup.mk' A)) := by
  obtain ⟨S, hSM, hf⟩ := hfusion
  have hquot := productDisconnected_quotient_of_central h.disconnected S hSM hf A hAc
  rcases h.conclusion_quotient A hne hquot with hr | hs
  · exfalso
    let q := QuotientGroup.mk' A
    have hgenq : Subgroup.closure (q '' Z) = ⊤ := by
      rw [← MonoidHom.map_closure, hgen, Subgroup.map_top_of_surjective q (QuotientGroup.mk'_surjective A)]
    let e : (G ⧸ A) ≃* Subgroup.closure (q '' Z) :=
      by rw [hgenq]; exact Subgroup.topEquiv.symm
    have hrq : ¬ TwoRankAtLeastTwo (G ⧸ A) := fun hh =>
      hr (hh.map_of_injective e.toMonoidHom e.injective)
    obtain ⟨z, hz, _⟩ := h.disconnected.nonempty
    obtain ⟨T, _, hT⟩ := hcentral z hz
    have hzq : IsInvolution (q z) := hquot.involutions (q z) ⟨z, hz, rfl⟩
    have hzbar := involution_image_mem_center_of_not_twoRank hrq hzq
    have hzodd := Subgroup.mem_center_mod_oddCore_of_central_two_quotient A hAc hAp T
      (show z ∈ Subgroup.centralizer (T : Set G) from fun t ht => (hT ⟨t, ht⟩).eq.symm) hzbar
    have hzinj : Function.Injective (QuotientGroup.mk' (pPrimeCore 2 G)) := by
      apply (MonoidHom.ker_eq_bot_iff _).mp
      rw [QuotientGroup.ker_mk', hodd]
    have hzc : z ∈ Subgroup.center G := by
      apply Subgroup.mem_center_iff.mpr
      intro g
      apply hzinj
      simpa only [map_mul] using Subgroup.mem_center_iff.mp hzodd
        (QuotientGroup.mk' (pPrimeCore 2 G) g)
    exact not_mem_of_mem_center h.disconnected hzc hz
  · exact hs

end BenderSuzuki.ZD
