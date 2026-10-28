module

public import CFSG.Quasithin.Chapter2.Section01To03.LocalStructure.CoreGeometry
public import Theory.GroupTheory.PerfectSylowTwo
public import Mathlib.GroupTheory.IndexNormal

/-!
# An index-two Sylow subgroup with an escaping local overgroup

Source: Aschbacher–Smith, Lemma 2.3.10, printed pp.526–527, including
the continuation on p.527. Index two makes S normal in T. Uniqueness then
controls N_G(S), and every larger two-subgroup in M is Sylow in M, giving
β₁. Enlarge the escaping local group to its core normalizer N. The same
index comparison makes S Sylow in N, and the relative core-centralizer
bound gives β₂. Perfectness rules out the degenerate |T| = 2 case.
-/

public section
namespace CFSG.Quasithin.Chapter2
open Subgroup
variable {G : Type*} [Group G] [Finite G] {M A H : Subgroup G}

private theorem double_card_le {A B : Subgroup G} (h : A < B) :
    2 * Nat.card A ≤ Nat.card B := by
  have hc := (A.subgroupOf B).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe h.le).toEquiv] at hc
  change Nat.card A * A.relIndex B = Nat.card B at hc
  have hi : 2 ≤ A.relIndex B := by
    have hn : A.relIndex B ≠ 0 := by
      intro he
      rw [he, mul_zero] at hc
      exact (Nat.card_pos (α := B)).ne hc
    have hne : A.relIndex B ≠ 1 := fun he => h.not_ge (relIndex_eq_one.mp he)
    omega
  calc
    2 * Nat.card A ≤ A.relIndex B * Nat.card A := Nat.mul_le_mul_right _ hi
    _ = Nat.card B := by rw [Nat.mul_comm, hc]

private theorem half_sylow_overgroup_eq (T : Sylow 2 G)
    (hTM : (T : Subgroup G) ≤ M) {A V : Subgroup G}
    (hcard : Nat.card (T : Subgroup G) = 2 * Nat.card A)
    (hAV : A < V) (hVp : IsPGroup 2 V) (hVM : V ≤ M) :
    ∃ P : Sylow 2 M, (P : Subgroup M).map M.subtype = V := by
  obtain ⟨P, hP⟩ := (hVp.comap_of_injective M.subtype M.subtype_injective).exists_le_sylow
  have hVP : V ≤ (P : Subgroup M).map M.subtype := by
    have hh := map_mono hP (f := M.subtype)
    change (V.subgroupOf M).map M.subtype ≤ _ at hh
    rwa [map_subgroupOf_eq_of_le hVM] at hh
  have hc : Nat.card ((P : Subgroup M).map M.subtype) = Nat.card (T : Subgroup G) := by
    rw [sylow_image_card, twoPart_eq_sylow_card T hTM]
  exact ⟨P, (eq_of_le_of_card_ge hVP (hc ▸ (hcard ▸ double_card_le hAV))).symm⟩

/-- Lemma 2.3.10 under the actual finite nonabelian simple QTKE hypotheses. -/
theorem lemma_2_3_10 {C : GroupClass} (hG : IsSimpleQTKE C G)
    (T : Sylow 2 G) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (hAT : A ≤ (T : Subgroup G)) (hi : A.relIndex (T : Subgroup G) = 2)
    (hout : ∃ H : Subgroup G, H ∈ Chapter1.HOver G (A : Set G) ∧ ¬ H ≤ M) :
    A ∈ beta M := by
  have hcard : Nat.card (T : Subgroup G) = 2 * Nat.card A := by
    have hh := (A.subgroupOf (T : Subgroup G)).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe hAT).toEquiv] at hh
    change Nat.card A * A.relIndex (T : Subgroup G) = _ at hh
    rw [hi] at hh
    omega
  let : IsSimpleGroup G := hG.simple
  let : Group.IsPerfect G := ⟨(inferInstance : (commutator G).Normal).eq_bot_or_eq_top.resolve_left
    (fun he => hG.nonabelian ((_root_.commutator_eq_bot_iff G).mp he))⟩
  have hAne : A ≠ ⊥ := by
    intro hb
    have ht : Nat.card (T : Subgroup G) = 2 := by simpa [hb] using hcard
    have heven : Even (Nat.card G) := even_iff_two_dvd.mpr
      (ht ▸ (T : Subgroup G).card_subgroup_dvd_card)
    have hgt := Theory.GroupTheory.perfect_sylow_two_card_gt_two T heven
    omega
  have hAp : IsPGroup 2 A := T.isPGroup'.to_le hAT
  have hAM : A ≤ M := hAT.trans hTM
  have hcore (V : Subgroup G) (hAV : A ≤ V) (hVp : IsPGroup 2 V) :
      twoCore (normalizer (V : Set G)) ≠ ⊥ := by
    intro he
    exact hAne (bot_unique (he ▸ hAV.trans
      (le_pCoreIn_of_normalizes hVp V.le_normalizer le_rfl)))
  have hTN : (T : Subgroup G) ≤ normalizer (A : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hAT).mp
      ((A.subgroupOf (T : Subgroup G)).normal_of_index_eq_two hi)
  have hNA : normalizer (A : Set G) ≤ M := by
    apply core_overgroup_le_of_sylow T hTM hunique (hcore A le_rfl hAp) (T.subtype hTM)
    simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le hTM] using hTN
  have hnorm : ∀ V : Subgroup G, IsPGroup 2 V → A ≤ V → V ≤ M →
      normalizer (V : Set G) ≤ M := by
    intro V hVp hAV hVM
    by_cases he : A = V
    · exact he ▸ hNA
    · obtain ⟨P, hP⟩ := half_sylow_overgroup_eq T hTM hcard (lt_of_le_of_ne hAV he) hVp hVM
      exact core_overgroup_le_of_sylow T hTM hunique (hcore V hAV hVp) P
        (hP.symm ▸ V.le_normalizer)
  refine ⟨⟨hAne, hAp⟩, hAM, fun V hV => hnorm V hV.2, ?_⟩
  obtain ⟨H, hH, hHM⟩ := hout
  let N := normalizer (twoCore H : Set G)
  have hHN : H ≤ N := le_normalizer_twoCore H
  have hAN : A ≤ N := hH.2.trans hHN
  have hNne : twoCore N ≠ ⊥ := by
    intro he
    exact hH.1 (bot_unique (he ▸ le_pCoreIn_of_normalizes
      (isPGroup_pCoreIn 2 H) (twoCore H).le_normalizer le_rfl))
  have hNM : ¬ N ≤ M := fun hn => hHM (hHN.trans hn)
  obtain ⟨P, hP⟩ := (hAp.comap_of_injective N.subtype N.subtype_injective).exists_le_sylow
  let B := (P : Subgroup N).map N.subtype
  have hAB : A ≤ B := by
    have hh := map_mono hP (f := N.subtype)
    change (A.subgroupOf N).map N.subtype ≤ _ at hh
    rwa [map_subgroupOf_eq_of_le hAN] at hh
  have hBM : B ≤ M := p_overgroup_le_of_normalizers_le
    (P.isPGroup'.map N.subtype) hAB hAM hnorm
  have he : B = A := by
    apply le_antisymm _ hAB
    by_contra hn
    obtain ⟨R, hR⟩ := half_sylow_overgroup_eq T hTM hcard
      (lt_of_le_of_ne hAB (fun he => hn he.ge)) (P.isPGroup'.map N.subtype) hBM
    exact hNM (core_overgroup_le_of_sylow T hTM hunique hNne R
      (hR.symm ▸ map_subtype_le (P : Subgroup N)))
  have hQA : twoCore H ≤ A := (le_pCoreIn_of_normalizes
    (isPGroup_pCoreIn 2 H) (twoCore H).le_normalizer le_rfl).trans
      ((pCoreIn_le_sylow N P).trans he.le)
  obtain ⟨R, hR⟩ := sylow_image_in_inf P hBM
  have hex : ∃ R : Sylow 2 ↥(M ⊓ N), (R : Subgroup ↥(M ⊓ N)).map (M ⊓ N).subtype = A := by
    have hh : ∃ R : Sylow 2 ↥(N ⊓ M), (R : Subgroup ↥(N ⊓ M)).map (N ⊓ M).subtype = A :=
      ⟨R, hR.trans he⟩
    rwa [inf_comm N M] at hh
  obtain ⟨R, hR⟩ := hex
  exact (inf_le_inf_left _ (centralizer_le hQA)).trans
    (hR ▸ pCoreIn_inf_centralizer_le_sylow M (twoCore H) R)

end CFSG.Quasithin.Chapter2
