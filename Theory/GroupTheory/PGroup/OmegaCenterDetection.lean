module

public import Theory.GroupTheory.PGroup.NormalSubgroups
public import Theory.GroupTheory.PGroup.OmegaAmbient

/-!
# Detecting normalized two-subgroups in the first omega center

A nontrivial subgroup normalized by a finite two-group contains a central
subgroup of order two. Consequently, a normalized subgroup inside that
two-group is trivial if it misses the first omega of the center.

The ambient formulation is used for the center of the marked parabolic
in Aschbacher–Smith, *The Classification of Quasithin Groups*,
Lemma 12.8.13(3), combined manuscript of 1 March 2004, printed p.855.
-/

open Subgroup

namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

public theorem eq_bot_of_normalized_of_omega_center_disjoint
    (S D : Subgroup G) (hS : IsPGroup 2 S) (hDS : D ≤ S)
    (hN : S ≤ normalizer (D : Set G))
    (hdis : omegaOneAmbient ((center S).map S.subtype) ⊓ D = ⊥) : D = ⊥ := by
  by_contra hD
  let N := D.subgroupOf S
  let : N.Normal := (normal_subgroupOf_iff_le_normalizer hDS).mpr hN
  have hn : Nontrivial N := by
    have hne : N ≠ ⊥ := by
      intro he
      apply hD
      rw [← map_subgroupOf_eq_of_le hDS]
      change N.map S.subtype = ⊥
      rw [he, map_bot]
    exact (nontrivial_iff_ne_bot N).mpr hne
  let : Fact (IsPGroup 2 S) := ⟨hS⟩
  obtain ⟨C, _, hCN, hcard, hCZ⟩ :=
    exists_central_subgroup_card_eq_prime_in_normal (p := 2) N hn
  have hCbot : C.map S.subtype = ⊥ := by
    apply le_bot_iff.mp
    rw [← hdis]
    refine le_inf ?_ ?_
    · rintro x ⟨c, hc, rfl⟩
      apply (omegaOneAmbient_le_iff _ _).mp le_rfl (c : G)
      · exact mem_map_of_mem S.subtype (hCZ hc)
      · have hp : (⟨c, hc⟩ : C) ^ 2 = 1 := by
          rw [← hcard]
          exact pow_card_eq_one'
        exact congrArg (S.subtype.comp C.subtype) hp
    · rintro x ⟨c, hc, rfl⟩
      exact hCN hc
  have hcb : C = ⊥ := (C.map_eq_bot_iff_of_injective S.subtype_injective).mp hCbot
  simp [hcb] at hcard
end Subgroup
