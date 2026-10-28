module

public import Theory.Mathieu.M23.QuasithinGeometry.HeptadStructure.SplitExtension
public import Theory.GroupAction.SimpleCosets
public import Mathlib.GroupTheory.Perm.MaximalSubgroups

/-!
# Ordinary maximality of the concrete M23 heptad stabilizer

The stabilizer is transitive on both the heptad and its complement, using the
actual alternating section and regular binary kernel. Every strict overgroup
is therefore transitive on all 23 points. Its index divides 253; index 23 is
incompatible with transitivity, and index 11 is excluded by the faithful coset
action of the simple group M23. This proves ordinary subgroup maximality.

This is the maximality used in Aschbacher–Smith 2.3.9(7)(f), printed pp.525–526
of the combined manuscript of 1 March 2004.
-/

@[expose] public section

open Subgroup Sporadic.Mathieu Sporadic.Mathieu.M23Geometry
open scoped Pointwise

namespace Sporadic.Mathieu.M23Geometry

private theorem heptad_moves {a b : Fin 23} (ha : a ∈ omega) (hb : b ∈ omega) :
    ∃ g : heptadStabilizer, (g : M23) • a = b := by
  obtain ⟨i, hi⟩ := labelEquiv.surjective ⟨a, ha⟩
  obtain ⟨j, hj⟩ := labelEquiv.surjective ⟨b, hb⟩
  have hi' : label i = a := congrArg Subtype.val hi
  have hj' : label j = b := congrArg Subtype.val hj
  let := alternatingGroup.isPretransitive_of_three_le_card (Fin 7) (by norm_num)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (alternatingGroup (Fin 7)) i j
  refine ⟨AlternatingSection.s g, ?_⟩
  rw [← hi', ← hj', AlternatingSection.s_label]
  exact congrArg label hg

private theorem complement_moves {a b : Fin 23} (ha : a ∉ omega) (hb : b ∉ omega) :
    ∃ g : heptadStabilizer, (g : M23) • a = b := by
  have ha' : a ∈ pairComplement omega := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ha⟩
  have hb' : b ∈ pairComplement omega := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hb⟩
  obtain ⟨g, hg, _⟩ := heptadKernelComplementAction_regular ⟨a, ha'⟩ ⟨b, hb'⟩
  refine ⟨g.val, ?_⟩
  simpa only [heptadKernelComplementAction_apply] using congrArg Subtype.val hg

private theorem overgroup_transitive (K : Subgroup M23) (hK : heptadStabilizer < K) :
    MulAction.IsPretransitive K (Fin 23) := by
  apply MulAction.IsPretransitive.of_partition (s := (omega : Set (Fin 23)))
  · intro a ha b hb
    obtain ⟨g, hg⟩ := heptad_moves ha hb
    exact ⟨⟨g, hK.le g.property⟩, hg⟩
  · intro a ha b hb
    obtain ⟨g, hg⟩ := complement_moves ha hb
    exact ⟨⟨g, hK.le g.property⟩, hg⟩
  · intro he
    apply hK.not_ge
    intro k hk
    have hm : (⟨k, hk⟩ : K) ∈ MulAction.stabilizer K (omega : Set (Fin 23)) := by
      rw [he]; trivial
    apply MulAction.mem_stabilizer_finset'.mpr
    intro a ha
    have hm' := MulAction.mem_stabilizer_iff.mp hm
    have hin : (⟨k, hk⟩ : K) • a ∈ (⟨k, hk⟩ : K) • (omega : Set (Fin 23)) :=
      Set.smul_mem_smul_set ha
    rwa [hm'] at hin

/-- The concrete heptad stabilizer is an ordinary maximal subgroup of M23. -/
theorem heptadStabilizer_isCoatom : IsCoatom heptadStabilizer := by
  refine ⟨?_, ?_⟩
  · intro he
    have hi := heptadStabilizer_index
    rw [he, Subgroup.index_top] at hi
    contradiction
  · intro K hK
    have hi := Subgroup.index_dvd_of_le hK.le
    rw [heptadStabilizer_index] at hi
    have hd : K.index ∈ (253 : ℕ).divisors := Nat.mem_divisors.mpr ⟨hi, by decide⟩
    have hd' : (253 : ℕ).divisors = {1, 11, 23, 253} := by decide +kernel
    rw [hd'] at hd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with h1 | h11 | h23 | h253
    · exact Subgroup.index_eq_one.mp h1
    · let := m23_isSimpleGroup
      by_contra hn
      have hc := K.card_dvd_factorial_index_of_simple hn
      rw [m23_order, h11] at hc
      norm_num [Nat.factorial] at hc
    · let := overgroup_transitive K hK
      have hi' : (MulAction.stabilizer K (0 : Fin 23)).index = 23 := by
        rw [MulAction.index_stabilizer, MulAction.orbit_eq_univ, Set.ncard_univ, Nat.card_fin]
      have hd23 : 23 ∣ Nat.card K := by
        simpa only [hi'] using (MulAction.stabilizer K (0 : Fin 23)).index_dvd_card
      have hc := K.card_mul_index
      rw [h23, m23_order] at hc
      have hc' : Nat.card K = 443520 := by omega
      rw [hc'] at hd23
      norm_num at hd23
    · have hi' := Subgroup.index_strictAnti hK
      rw [heptadStabilizer_index, h253] at hi'
      exact (lt_irrefl _ hi').elim

/-- Ordinary maximality transports to every heptad of the actual Witt design. -/
theorem heptad_stabilizer_isCoatom {B : Finset (Fin 23)} (hB : B ∈ m23Blocks) :
    IsCoatom (MulAction.stabilizer M23 B) := by
  obtain ⟨g, rfl⟩ := exists_smul_omega_eq hB
  rw [MulAction.stabilizer_smul_eq_stabilizer_map_conj]
  exact (OrderIso.isCoatom_iff (MulAut.conj g).mapSubgroup heptadStabilizer).mpr
    heptadStabilizer_isCoatom

end Sporadic.Mathieu.M23Geometry

end
