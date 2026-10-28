module

public import Theory.Mathieu.M22.Properties.HexadExtension
public import Theory.GroupAction.SimpleCosets
public import Mathlib.GroupTheory.Perm.MaximalSubgroups

/-!
# Ordinary maximality of the concrete M22 hexad stabilizers

The standard hexad stabilizer is transitive on its six points through its
actual alternating restriction image. Its three-point stabilizer has a
16-point orbit on the complement, by the checked stabilizer-chain orders
48 and 3. Thus every strict overgroup is transitive on all 22 points.

The hexad stabilizer has index 77. An intermediate subgroup of index 11
would have order 40320, incompatible with transitivity on 22 points; index
7 is excluded by the faithful coset action of the simple group M22.
Conjugacy of the actual hexads transports maximality to every hexad.

This is the ordinary subgroup maximality used in Aschbacher–Smith,
Lemma 2.3.9(7)(f), printed pp.525–526 of the combined manuscript of
1 March 2004. The proof uses the concrete degree-22 action throughout.
-/

public section

open scoped Pointwise
namespace Sporadic.Mathieu

private theorem hexad_moves {a b : Fin 22}
    (ha : a ∈ m22Hexad123) (hb : b ∈ m22Hexad123) :
    ∃ g : m22HexadStabilizer, (g : M22) • a = b := by
  let e := m22HexadLabels m22Hexad123_mem
  let := alternatingGroup.isPretransitive_of_three_le_card (Fin 6) (by norm_num)
  obtain ⟨p, hp⟩ := MulAction.exists_smul_eq (alternatingGroup (Fin 6))
    (e ⟨a, ha⟩) (e ⟨b, hb⟩)
  have hr : (p : Equiv.Perm (Fin 6)) ∈ (m22HexadAction m22Hexad123_mem).range := by
    rw [m22HexadAction_range]
    exact p.property
  obtain ⟨g, hg⟩ := hr
  refine ⟨g, ?_⟩
  have h := m22HexadAction_apply m22Hexad123_mem g ⟨a, ha⟩
  rw [hg] at h
  exact congrArg Subtype.val (e.injective (h.symm.trans hp))

private theorem stab3_orbit_four_card :
    Nat.card (MulAction.orbit m22Stab3 (4 : Fin 22)) = 16 := by
  let : Fintype (MulAction.orbit m22Stab3 (4 : Fin 22)) := Fintype.ofFinite _
  let : Fintype m22Stab4 := Fintype.ofFinite _
  have h := MulAction.card_orbit_mul_card_stabilizer_eq_card_group m22Stab3 (4 : Fin 22)
  have hNat : Nat.card (MulAction.orbit m22Stab3 (4 : Fin 22)) *
      Nat.card m22Stab4 = Nat.card m22Stab3 := by
    simpa only [Nat.card_eq_fintype_card] using h
  rw [m22Stab4_card, m22Stab3_card] at hNat
  omega

private theorem stab3_orbit_four :
    MulAction.orbit m22Stab3 (4 : Fin 22) = (m22Hexad123 : Set (Fin 22))ᶜ := by
  apply Set.eq_of_subset_of_ncard_le (ht := Set.toFinite _)
  · intro x hx
    obtain ⟨g, rfl⟩ := MulAction.mem_orbit_iff.mp hx
    change m22Stab3Perm g 4 ∉ m22Hexad123
    have hg : m22Stab3M22 g ∈ MulAction.stabilizer M22 m22Hexad123 :=
      m22Stab3_smul_hexad123 g
    have h := MulAction.mem_stabilizer_finset.mp hg (4 : Fin 22)
    exact h.not.mpr (by decide +kernel)
  · have hc : (m22Hexad123 : Set (Fin 22))ᶜ.ncard = 16 := by
      rw [Set.ncard_compl, Set.ncard_coe_finset, m22Block_card _ m22Hexad123_mem,
        Nat.card_fin]
    rw [hc, ← Nat.card_coe_set_eq, stab3_orbit_four_card]

private theorem complement_moves {a b : Fin 22}
    (ha : a ∉ m22Hexad123) (hb : b ∉ m22Hexad123) :
    ∃ g : m22HexadStabilizer, (g : M22) • a = b := by
  have ha' : a ∈ MulAction.orbit m22Stab3 (4 : Fin 22) := by
    rw [stab3_orbit_four]; exact ha
  have hb' : b ∈ MulAction.orbit m22Stab3 (4 : Fin 22) := by
    rw [stab3_orbit_four]; exact hb
  obtain ⟨ga, hga⟩ := MulAction.mem_orbit_iff.mp ha'
  obtain ⟨gb, hgb⟩ := MulAction.mem_orbit_iff.mp hb'
  refine ⟨⟨m22Stab3M22 (gb * ga⁻¹), m22Stab3_smul_hexad123 _⟩, ?_⟩
  change (gb * ga⁻¹ : m22Stab3) • a = b
  rw [mul_smul, ← hga, inv_smul_smul, hgb]

private theorem overgroup_transitive (K : Subgroup M22) (hK : m22HexadStabilizer < K) :
    MulAction.IsPretransitive K (Fin 22) := by
  apply MulAction.IsPretransitive.of_partition (s := (m22Hexad123 : Set (Fin 22)))
  · intro a ha b hb
    obtain ⟨g, hg⟩ := hexad_moves ha hb
    exact ⟨⟨g, hK.le g.property⟩, hg⟩
  · intro a ha b hb
    obtain ⟨g, hg⟩ := complement_moves ha hb
    exact ⟨⟨g, hK.le g.property⟩, hg⟩
  · intro he
    apply hK.not_ge
    intro k hk
    have hm : (⟨k, hk⟩ : K) ∈ MulAction.stabilizer K
        (m22Hexad123 : Set (Fin 22)) := by rw [he]; trivial
    apply MulAction.mem_stabilizer_finset'.mpr
    intro a ha
    have hm' := MulAction.mem_stabilizer_iff.mp hm
    have hin : (⟨k, hk⟩ : K) • a ∈ (⟨k, hk⟩ : K) •
        (m22Hexad123 : Set (Fin 22)) := Set.smul_mem_smul_set ha
    rwa [hm'] at hin

/-- The standard hexad stabilizer has index 77 in the concrete M22. -/
theorem m22HexadStabilizer_index : m22HexadStabilizer.index = 77 := by
  have h := m22HexadStabilizer.card_mul_index
  rw [m22HexadStabilizer_card, m22_order] at h
  omega

/-- The standard hexad stabilizer is an ordinary maximal subgroup of M22. -/
theorem m22HexadStabilizer_isCoatom : IsCoatom m22HexadStabilizer := by
  refine ⟨?_, ?_⟩
  · intro he
    have hi := m22HexadStabilizer_index
    rw [he, Subgroup.index_top] at hi
    contradiction
  · intro K hK
    have hi := Subgroup.index_dvd_of_le hK.le
    rw [m22HexadStabilizer_index] at hi
    have hd : K.index ∈ (77 : ℕ).divisors := Nat.mem_divisors.mpr ⟨hi, by decide⟩
    have hd' : (77 : ℕ).divisors = {1, 7, 11, 77} := by decide +kernel
    rw [hd'] at hd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with h1 | h7 | h11 | h77
    · exact Subgroup.index_eq_one.mp h1
    · let := m22_isSimpleGroup
      by_contra hn
      have hc := K.card_dvd_factorial_index_of_simple hn
      rw [m22_order, h7] at hc
      norm_num [Nat.factorial] at hc
    · let := overgroup_transitive K hK
      have hi' : (MulAction.stabilizer K (0 : Fin 22)).index = 22 := by
        rw [MulAction.index_stabilizer, MulAction.orbit_eq_univ, Set.ncard_univ, Nat.card_fin]
      have hd22 : 22 ∣ Nat.card K := by
        simpa only [hi'] using (MulAction.stabilizer K (0 : Fin 22)).index_dvd_card
      have hc := K.card_mul_index
      rw [h11, m22_order] at hc
      have hc' : Nat.card K = 40320 := by omega
      rw [hc'] at hd22
      norm_num at hd22
    · have hi' := Subgroup.index_strictAnti hK
      rw [m22HexadStabilizer_index, h77] at hi'
      exact (lt_irrefl _ hi').elim

/-- Every hexad stabilizer is an ordinary maximal subgroup of the concrete M22. -/
theorem m22_hexad_stabilizer_isCoatom (B : Finset (Fin 22)) (hB : B ∈ m22Blocks) :
    IsCoatom (MulAction.stabilizer M22 B) := by
  obtain ⟨g, rfl⟩ := exists_smul_m22Hexad123_eq hB
  rw [MulAction.stabilizer_smul_eq_stabilizer_map_conj]
  exact (OrderIso.isCoatom_iff (MulAut.conj g).mapSubgroup m22HexadStabilizer).mpr
    m22HexadStabilizer_isCoatom

end Sporadic.Mathieu

end
