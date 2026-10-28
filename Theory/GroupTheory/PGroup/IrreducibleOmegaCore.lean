module

public import Theory.GroupTheory.PGroup.OmegaCenterIn
public import Theory.GroupTheory.PGroup.NormalSubgroups
public import Theory.GroupTheory.PCoreLocalSetup

/-!
# Irreducible central omega subgroups and the two-core

A nontrivial subgroup normalized by a finite two-group meets its central
omega subgroup. Consequently, if the central omega of a Sylow two-group
lies in an irreducible subgroup U, then U lies in the nontrivial two-core.
For a group with self-centralizing two-core, a fixed-free actor on U also
forces the center to be trivial.

The source application is Aschbacher–Smith, combined manuscript of
1 March 2004, Lemma 9.3.6, printed pp.733–734.
-/

public section
open Subgroup
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- A nontrivial normal subgroup of a two-group meets its central omega. -/
theorem inf_omegaCenterIn_ne_bot_of_normalized_twoGroup
    (Q R : Subgroup G) (hQR : Q ≤ R) (hR : IsPGroup 2 R)
    (hn : R ≤ normalizer (Q : Set G)) (hQ : Q ≠ ⊥) :
    Q ⊓ omegaCenterIn R ≠ ⊥ := by
  let N := Q.subgroupOf R
  let : N.Normal := normal_subgroupOf_of_le_normalizer hn
  have hN : N ≠ ⊥ := by
    intro he
    apply hQ
    have hm := map_subgroupOf_eq_of_le hQR
    change N.map R.subtype = Q at hm
    rw [he, map_bot] at hm
    exact hm.symm
  let : Fact (IsPGroup 2 R) := ⟨hR⟩
  obtain ⟨A, _, hAN, hcard, hAZ⟩ := exists_central_subgroup_card_eq_prime_in_normal
    (p := 2) N ((nontrivial_iff_ne_bot _).mpr hN)
  have hAne : A ≠ ⊥ := by
    intro he
    have hh := card_eq_one.mpr he
    omega
  obtain ⟨a, ha, ha1⟩ := A.bot_or_exists_ne_one.resolve_left hAne
  intro he
  have ham : (a : G) ∈ Q ⊓ omegaCenterIn R := by
    refine ⟨hAN ha, (mem_omegaCenterIn_iff R _).mpr ⟨a.property, ?_, ?_⟩⟩
    · intro r hr
      exact congrArg R.subtype ((mem_center_iff.mp (hAZ ha)) ⟨r,hr⟩)
    · have hh : a ^ 2 = 1 := by
        have hp := pow_card_eq_one' (x := (⟨a,ha⟩ : A))
        rw [hcard] at hp
        exact congrArg A.subtype hp
      exact congrArg R.subtype hh
  exact ha1 (Subtype.ext (mem_bot.mp (he ▸ ham)))

/-- Irreducibility promotes the central-omega intersection to core containment. -/
theorem pCoreIn_contains_irreducible_of_omegaCenter_le
    (H R U A : Subgroup G) (hQR : H.pCoreIn 2 ≤ R)
    (hRH : R ≤ H) (hR : IsPGroup 2 R) (hcore : H.pCoreIn 2 ≠ ⊥)
    (hOmega : omegaCenterIn R ≤ U) (hAH : A ≤ H)
    (hAU : A ≤ normalizer (U : Set G))
    (hirr : ∀ N : Subgroup G, N ≤ U → A ≤ normalizer (N : Set G) →
      N = ⊥ ∨ N = U) : U ≤ H.pCoreIn 2 := by
  have hHQ : H ≤ normalizer (H.pCoreIn 2 : Set G) := H.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image H (pCore 2 H))
  have hne : H.pCoreIn 2 ⊓ U ≠ ⊥ := by
    intro hb
    exact inf_omegaCenterIn_ne_bot_of_normalized_twoGroup _ R hQR hR
      (hRH.trans hHQ) hcore (bot_unique ((inf_le_inf_left _ hOmega).trans_eq hb))
  have he := (hirr (H.pCoreIn 2 ⊓ U) inf_le_right
    ((le_inf (hAH.trans hHQ) hAU).trans inf_normalizer_le_normalizer_inf)).resolve_left hne
  exact he ▸ inf_le_left

/-- A fixed-free actor on the central-omega container forces a trivial center. -/
theorem center_eq_bot_of_omegaCenter_le_fixedFree
    (H R U A : Subgroup G) (hcore : H ⊓ centralizer (H.pCoreIn 2 : Set G) ≤ H.pCoreIn 2)
    (hQR : H.pCoreIn 2 ≤ R) (hRH : R ≤ H) (hR : IsPGroup 2 R)
    (hOmega : omegaCenterIn R ≤ U) (hAH : A ≤ H)
    (hfixed : U ⊓ centralizer (A : Set G) = ⊥) : center H = ⊥ := by
  have hZH : centerIn H ≤ H := inf_le_left
  have hZQ : centerIn H ≤ H.pCoreIn 2 :=
    (inf_le_inf_left H (centralizer_le (pCoreIn_le 2 H))).trans hcore
  have hZN : H ≤ normalizer (centerIn H : Set G) := by
    rw [centerIn_eq_map_center]
    exact H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image H (center H))
  have hZ : centerIn H = ⊥ := by
    by_contra hne
    apply inf_omegaCenterIn_ne_bot_of_normalized_twoGroup (centerIn H) R
      (hZQ.trans hQR) hR (hRH.trans hZN) hne
    apply bot_unique
    exact (le_inf (inf_le_right.trans hOmega)
      (inf_le_left.trans (inf_le_right.trans (centralizer_le hAH)))).trans_eq hfixed
  rw [centerIn_eq_map_center] at hZ
  exact ((center H).map_eq_bot_iff_of_injective H.subtype_injective).mp hZ

end Subgroup
