module

public import Theory.Mathieu.M22.Properties.Transitivity
public import Mathlib.Data.Fintype.CardEmbedding
public import Mathlib.GroupTheory.GroupAction.SubMulAction

/-!
# Intrinsic recognition of the degree-22 point stabilizers

For an index-22 subgroup H, triple transitivity gives divisibility constraints
on every H-invariant subset of the natural action. Its size is 0, 1, 21 or 22.
Since |H| = 20160 is not divisible by 22, H has a proper orbit; that orbit or
its complement is a singleton. Equality of indices then identifies H with the
corresponding point stabilizer. Thus every abstract automorphism preserves
this stabilizer class.

This supplies the permutation-realization step for the design description of
Aut(M₂₂) in GLS3, Table 5.3c, Note 1, without assuming that description.
-/

open MulAction
open scoped Pointwise

private theorem card_dvd_index_mul_of_equivariant
    {G Y : Type*} [Group G] [MulAction G Y] [Finite Y]
    [IsPretransitive G Y] (H : Subgroup G)
    {A : Type*} [MulAction H A] [Finite A]
    (f : A → Y) (hf : ∀ (h : H) (a : A), f (h • a) = (h : G) • f a) :
    Nat.card Y ∣ H.index * Nat.card A := by
  classical
  let := Fintype.ofFinite A
  let := Fintype.ofFinite (orbitRel.Quotient H A)
  let (q : orbitRel.Quotient H A) := Fintype.ofFinite (orbit H q.out)
  have horbit (a : A) : Nat.card Y ∣ H.index * Nat.card (orbit H a) := by
    have hle : (stabilizer H a).map H.subtype ≤ stabilizer G (f a) := by
      rintro _ ⟨h, hh, rfl⟩
      apply mem_stabilizer_iff.mpr
      change (h : G) • f a = f a
      rw [← hf, mem_stabilizer_iff.mp hh]
    have hd := Subgroup.index_dvd_of_le hle
    rw [index_stabilizer_of_transitive, Subgroup.index_map_of_injective _ H.subtype_injective,
      Subgroup.range_subtype, index_stabilizer] at hd
    simpa only [← Nat.card_coe_set_eq, mul_comm] using hd
  have hcard : Nat.card A = ∑ q : orbitRel.Quotient H A, Nat.card (orbit H q.out) := by
    rw [Nat.card_congr (selfEquivSigmaOrbits H A)]
    simp only [Nat.card_eq_fintype_card, Fintype.card_sigma]
  rw [hcard, Finset.mul_sum]
  exact Finset.dvd_sum fun q _ => horbit q.out

private theorem descFactorial_dvd_index_mul
    {G X : Type*} [Group G] [MulAction G X] [Fintype X] [DecidableEq X]
    (H : Subgroup G) (S : Finset X) (hS : H ≤ stabilizer G S)
    (t : ℕ) [IsMultiplyPretransitive G X t] :
    (Fintype.card X).descFactorial t ∣ H.index * S.card.descFactorial t := by
  classical
  let A : SubMulAction H X := {
    carrier := S
    smul_mem' := by
      intro h x hx
      exact mem_stabilizer_finset'.mp (hS h.property) hx }
  let f : (Fin t ↪ A) → (Fin t ↪ X) :=
    fun e => e.trans (Function.Embedding.subtype _)
  have hf : ∀ (h : H) (a : Fin t ↪ A), f (h • a) = (h : G) • f a := by
    intro h a
    ext i
    rfl
  have hd := card_dvd_index_mul_of_equivariant H f hf
  have hA : Fintype.card A = S.card := by
    have he : A ≃ S := {
      toFun := fun x => ⟨x.val, x.property⟩
      invFun := fun x => ⟨x.val, x.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
    exact (Fintype.card_congr he).trans (Fintype.card_coe S)
  simpa only [Nat.card_eq_fintype_card, Fintype.card_embedding_eq, Fintype.card_fin,
    hA] using hd

namespace Sporadic.Mathieu

private theorem invariant_card (H : Subgroup M22) (hH : H.index = 22)
    (S : Finset (Fin 22)) (hS : H ≤ stabilizer M22 S) :
    S.card = 0 ∨ S.card = 1 ∨ S.card = 21 ∨ S.card = 22 := by
  let := m22_isTwoPretransitive
  let := m22_isThreePretransitive
  have h2 := descFactorial_dvd_index_mul H S hS 2
  have h3 := descFactorial_dvd_index_mul H S hS 3
  rw [Fintype.card_fin, hH] at h2 h3
  have hb : S.card ≤ 22 := by simpa using Finset.card_le_univ S
  interval_cases h : S.card <;> norm_num [h, Nat.descFactorial] at *

private theorem invariant_singleton (H : Subgroup M22)
    (S : Finset (Fin 22)) (hS : H ≤ stabilizer M22 S) (hc : S.card = 1) :
    ∃ y : Fin 22, H ≤ stabilizer M22 y := by
  obtain ⟨y, rfl⟩ := Finset.card_eq_one.mp hc
  refine ⟨y, ?_⟩
  intro g hg
  apply mem_stabilizer_iff.mpr
  exact Finset.mem_singleton.mp
    (mem_stabilizer_finset'.mp (hS hg) (Finset.mem_singleton_self y))

private theorem index_twenty_two_fixes (H : Subgroup M22) (hH : H.index = 22) :
    ∃ y : Fin 22, H ≤ stabilizer M22 y := by
  classical
  let S := (orbit H (0 : Fin 22)).toFinset
  have hS : H ≤ stabilizer M22 S := by
    intro g hg
    apply mem_stabilizer_finset'.mpr
    intro x hx
    exact Set.mem_toFinset.mpr
      (mapsTo_smul_orbit (⟨g, hg⟩ : H) 0 (Set.mem_toFinset.mp hx))
  have hpos : 0 < S.card := Finset.card_pos.mpr
    ⟨0, Set.mem_toFinset.mpr (mem_orbit_self 0)⟩
  have hd : S.card ∣ Nat.card H := by
    have hi := (stabilizer H (0 : Fin 22)).index_dvd_card
    rw [index_stabilizer] at hi
    simpa only [S, ← Set.ncard_eq_toFinset_card'] using hi
  have hc : Nat.card H = 20160 := by
    have h := H.card_mul_index
    rw [hH, m22_order] at h
    omega
  rcases invariant_card H hH S hS with h0 | h1 | h21 | h22
  · omega
  · exact invariant_singleton H S hS h1
  · apply invariant_singleton H Sᶜ
    · intro g hg
      apply mem_stabilizer_finset'.mpr
      intro x hx
      apply Finset.mem_compl.mpr
      exact (mem_stabilizer_finset.mp (hS hg) x).not.mpr (Finset.mem_compl.mp hx)
    · rw [Finset.card_compl, Fintype.card_fin, h21]
  · rw [h22, hc] at hd
    norm_num at hd

/-- Every subgroup of index 22 is a point stabilizer in the natural action. -/
public theorem m22_index_twenty_two_eq_stabilizer (H : Subgroup M22) (hH : H.index = 22) :
    ∃ y : Fin 22, H = stabilizer M22 y := by
  let := m22_isPretransitive
  obtain ⟨y, hy⟩ := index_twenty_two_fixes H hH
  refine ⟨y, ?_⟩
  by_contra hn
  have hi := Subgroup.index_strictAnti (lt_of_le_of_ne hy hn)
  rw [index_stabilizer_of_transitive, Nat.card_fin, hH] at hi
  omega

/-- Abstract automorphisms preserve the natural point-stabilizer class. -/
public theorem m22_stabilizer_map_eq (f : MulAut M22) (x : Fin 22) :
    ∃ y : Fin 22, (stabilizer M22 x).map f.toMonoidHom = stabilizer M22 y := by
  let := m22_isPretransitive
  apply m22_index_twenty_two_eq_stabilizer
  rw [Subgroup.index_map_of_bijective f.bijective, index_stabilizer_of_transitive, Nat.card_fin]

end Sporadic.Mathieu
