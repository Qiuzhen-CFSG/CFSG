module

public import Theory.Mathieu.M22.Properties.SolvableSylowOvergroups.Coverage.Intransitive
public import Theory.Mathieu.M22.Properties.HexadExtension
public import Theory.GroupAction.SimpleCosets
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

/-!
# Recognition of the actual pair stabilizers in M₂₂

A subgroup of order 1920 contains a full Sylow two-subgroup and is
intransitive in degree 22. Native Sylow geometry therefore gives a preserved
pair or hexad. The hexad alternative would give a subgroup of index three
in A₆, which its faithful coset action excludes. Equality with the pair
stabilizer then follows from the order.

This supplies arbitrary-subgroup incidence in Aschbacher–Smith I.2.2(6a),
printed pp.410 and 412 (combined manuscript of 1 March 2004). It uses the
actual degree-22 action, without a maximal-subgroup table.
-/

public section
namespace Sporadic.Mathieu
open Subgroup MulAction
open scoped Pointwise

theorem m22_card1920_contains_sylow (H : Subgroup M22) (hc : Nat.card H = 1920) :
    ∃ U : Sylow 2 M22, (U : Subgroup M22) ≤ H := by
  let P : Sylow 2 H := Classical.choice inferInstance
  let A := P.toSubgroup.map H.subtype
  have hA : Nat.card A = 128 := by
    rw [card_map_of_injective H.subtype_injective, P.card_eq_multiplicity, hc]
    decide +kernel
  refine ⟨Sylow.ofCard A ?_, map_subtype_le _⟩
  rw [hA, m22_order]
  decide +kernel

theorem m22_card1920_not_le_hexad (H : Subgroup M22) (hc : Nat.card H = 1920)
    {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) :
    ¬ H ≤ stabilizer M22 B := by
  intro hle
  let L := H.subgroupOf (stabilizer M22 B)
  have hL : Nat.card L = 1920 :=
    (Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv).trans hc
  have hi : L.index = 3 := by
    have h := L.card_mul_index
    rw [hL, m22Hexad_stabilizer_card hB] at h
    omega
  let f : stabilizer M22 B →* alternatingGroup (Fin 6) :=
    (m22HexadQuotientAlternatingEquiv hB).toMonoidHom.comp
      (QuotientGroup.mk' (m22SetAction B).ker)
  have hf : Function.Surjective f :=
    (m22HexadQuotientAlternatingEquiv hB).surjective.comp (QuotientGroup.mk'_surjective _)
  let R := L.map f
  have hR : R.index ∣ 3 := hi ▸ L.index_map_dvd hf
  have hA : Nat.card (alternatingGroup (Fin 6)) = 360 := by
    rw [nat_card_alternatingGroup, Nat.card_fin]
    decide
  have hproper : R ≠ ⊤ := by
    intro he
    have hd := L.card_map_dvd f
    rw [show L.map f = ⊤ from he, card_top, hA, hL] at hd
    norm_num at hd
  have hiR : R.index = 3 := by
    exact ((Nat.dvd_prime Nat.prime_three).mp hR).resolve_left
      (fun h => hproper (index_eq_one.mp h))
  let : IsSimpleGroup (alternatingGroup (Fin 6)) :=
    alternatingGroup.isSimpleGroup (by simp)
  have hd := R.card_dvd_factorial_index_of_simple hproper
  rw [hA, hiR] at hd
  norm_num [Nat.factorial] at hd

/-- Every order-1920 subgroup is the stabilizer of a genuine unordered pair. -/
theorem m22_card1920_eq_pair_stabilizer (H : Subgroup M22) (hc : Nat.card H = 1920) :
    ∃ S : Finset (Fin 22), S.card = 2 ∧ H = stabilizer M22 S := by
  have hnt : ¬ IsPretransitive H (Fin 22) := by
    intro ht
    let := ht
    have hd : 22 ∣ Nat.card H := by
      have hi := (stabilizer H (0 : Fin 22)).index_dvd_card
      rw [index_stabilizer_of_transitive, Nat.card_fin] at hi
      exact hi
    rw [hc] at hd
    norm_num at hd
  rcases M22SolvableSylow.coverage_of_not_pretransitive H
      (m22_card1920_contains_sylow H hc) hnt with ⟨B, hB, hHB⟩ | ⟨S, hS, hHS⟩
  · exact (m22_card1920_not_le_hexad H hc hB hHB).elim
  refine ⟨S, hS, eq_of_le_of_card_ge hHS ?_⟩
  rcases Finset.card_eq_two.mp hS with ⟨x, y, hxy, rfl⟩
  obtain ⟨g, hg1, hg2⟩ := (is_two_pretransitive_iff.mp m22_isTwoPretransitive)
    (by decide : (1 : Fin 22) ≠ 2) hxy
  have hg : g • m22Pair12 = ({x, y} : Finset (Fin 22)) := by
    rw [m22Pair12, Finset.smul_finset_insert, Finset.smul_finset_singleton, ← hg1, ← hg2]
  have he := (Nat.card_congr (stabilizerEquivStabilizer hg.symm).toEquiv).symm.trans
    m22PairStabilizer_card
  exact le_of_eq (he.trans hc.symm)

/-- A source pair and a Sylow-fixed hexad are incident in the native design. -/
theorem m22_card1920_incident_hexad (H : Subgroup M22) (hc : Nat.card H = 1920) :
    ∃ S B : Finset (Fin 22), S.card = 2 ∧ B ∈ m22Blocks ∧ S ⊆ B ∧
      H = stabilizer M22 S ∧ m22HexadPointwiseKernel B ≤ H := by
  obtain ⟨S, hS, hH⟩ := m22_card1920_eq_pair_stabilizer H hc
  obtain ⟨U, hUH⟩ := m22_card1920_contains_sylow H hc
  obtain ⟨B, hB, hUB⟩ := M22SolvableSylow.sylow_preserves_hexad U
  have hk := (M22SolvableSylow.kernel_le_of_sylow hB U hUB).trans hUH
  exact ⟨S, B, hS, hB,
    M22SolvableSylow.small_invariant_subset_hexad hB S (by omega) (hH ▸ hk), hH, hk⟩

end Sporadic.Mathieu
