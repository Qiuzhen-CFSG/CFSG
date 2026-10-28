module

public import Theory.Mathieu.M23.Properties.Order
public import Theory.Mathieu.M23.Properties.Transitivity
public import Theory.Mathieu.M23.QuasithinGeometry.Involutions.FixedHeptad
public import Theory.GroupAction.AutomorphismNormalizer

/-!
# Automorphisms of the concrete M₂₃

The natural degree-23 action reconstructs every point stabilizer intrinsically:
four-transitivity restricts the orbit of an index-23 subgroup to a singleton or
its complement, and the order of M₂₃ rules out the full orbit.  Thus every
abstract automorphism preserves the natural point-stabilizer class.

The same concrete action proves self-normalization.  Every heptad is the fixed
set of an involution, and a permutation normalizing M₂₃ transports these fixed
sets to fixed sets of involutions.  Hence it preserves the Witt design and
belongs to M₂₃.  The permutation-normalizer reconstruction then makes every
abstract automorphism inner.

This supplies the M₂₃ cases of Aschbacher--Smith 16.1.5(6) and 16.1.6,
printed pp.1171--1172, for the actual design automorphism carrier.
-/

open MulAction
open Subgroup
open scoped Pointwise
namespace Sporadic.Mathieu

private theorem card_dvd_index_mul_of_equivariant
    {G Y : Type*} [Group G] [MulAction G Y] [Finite Y]
    [MulAction.IsPretransitive G Y] (H : Subgroup G)
    {A : Type*} [MulAction H A] [Finite A]
    (f : A → Y) (hf : ∀ (h : H) (a : A), f (h • a) = (h : G) • f a) :
    Nat.card Y ∣ H.index * Nat.card A := by
  classical
  let := Fintype.ofFinite A
  let := Fintype.ofFinite (orbitRel.Quotient H A)
  have horbit (a : A) : Nat.card Y ∣ H.index * Nat.card (orbit H a) := by
    have hle : (stabilizer H a).map H.subtype ≤ stabilizer G (f a) := by
      rintro _ ⟨h, hh, rfl⟩
      apply mem_stabilizer_iff.mpr
      change (h : G) • f a = f a
      rw [← hf, mem_stabilizer_iff.mp hh]
    have hd := Subgroup.index_dvd_of_le hle
    rw [index_stabilizer_of_transitive,
      Subgroup.index_map_of_injective _ H.subtype_injective,
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
    (t : ℕ) [MulAction.IsMultiplyPretransitive G X t] :
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
  simpa only [Nat.card_eq_fintype_card, Fintype.card_embedding_eq, Fintype.card_fin, hA] using hd

private theorem m23_invariant_card (H : Subgroup M23) (hH : H.index = 23)
    (S : Finset (Fin 23)) (hS : H ≤ stabilizer M23 S) :
    S.card = 0 ∨ S.card = 1 ∨ S.card = 22 ∨ S.card = 23 := by
  let := m23_isFourPretransitive
  let _ : MulAction.IsMultiplyPretransitive M23 (Fin 23) 2 :=
    MulAction.isMultiplyPretransitive_of_le (G := M23) (α := Fin 23)
      (m := 2) (n := 4) (by decide) (by simp)
  let _ : MulAction.IsMultiplyPretransitive M23 (Fin 23) 3 :=
    MulAction.isMultiplyPretransitive_of_le (G := M23) (α := Fin 23)
      (m := 3) (n := 4) (by decide) (by simp)
  have h2 := descFactorial_dvd_index_mul H S hS 2
  have h3 := descFactorial_dvd_index_mul H S hS 3
  rw [Fintype.card_fin, hH] at h2 h3
  have hb : S.card ≤ 23 := by simpa using Finset.card_le_univ S
  interval_cases h : S.card <;> norm_num [h, Nat.descFactorial] at *

private theorem invariant_singleton (H : Subgroup M23)
    (S : Finset (Fin 23)) (hS : H ≤ stabilizer M23 S) (hc : S.card = 1) :
    ∃ y : Fin 23, H ≤ stabilizer M23 y := by
  obtain ⟨y, rfl⟩ := Finset.card_eq_one.mp hc
  refine ⟨y, ?_⟩
  intro g hg
  apply mem_stabilizer_iff.mpr
  exact Finset.mem_singleton.mp
    (mem_stabilizer_finset'.mp (hS hg) (Finset.mem_singleton_self y))

private theorem m23_index_twenty_three_fixes (H : Subgroup M23) (hH : H.index = 23) :
    ∃ y : Fin 23, H ≤ stabilizer M23 y := by
  classical
  let := m23_isFourPretransitive
  let S := (orbit H (0 : Fin 23)).toFinset
  have hS : H ≤ stabilizer M23 S := by
    intro g hg
    apply mem_stabilizer_finset'.mpr
    intro x hx
    exact Set.mem_toFinset.mpr (mapsTo_smul_orbit (⟨g, hg⟩ : H) 0
      (Set.mem_toFinset.mp hx))
  have hpos : 0 < S.card := Finset.card_pos.mpr
    ⟨0, Set.mem_toFinset.mpr (mem_orbit_self 0)⟩
  have hd : S.card ∣ Nat.card H := by
    have hi := (stabilizer H (0 : Fin 23)).index_dvd_card
    rw [index_stabilizer] at hi
    simpa only [S, ← Set.ncard_eq_toFinset_card'] using hi
  have hc : Nat.card H = 443520 := by
    have h := H.card_mul_index
    rw [hH, m23_order] at h
    omega
  rcases m23_invariant_card H hH S hS with h0 | h1 | h22 | h23
  · omega
  · exact invariant_singleton H S hS h1
  · apply invariant_singleton H Sᶜ
    · intro g hg
      apply mem_stabilizer_finset'.mpr
      intro x hx
      apply Finset.mem_compl.mpr
      exact (mem_stabilizer_finset.mp (hS hg) x).not.mpr (Finset.mem_compl.mp hx)
    · rw [Finset.card_compl, Fintype.card_fin, h22]
  · rw [h23, hc] at hd
    norm_num at hd

/-- Every subgroup of index 23 is a point stabilizer in the natural action. -/
public theorem m23_index_twenty_three_eq_stabilizer (H : Subgroup M23)
    (hH : H.index = 23) : ∃ y : Fin 23, H = stabilizer M23 y := by
  let := m23_isPretransitive
  obtain ⟨y, hy⟩ := m23_index_twenty_three_fixes H hH
  refine ⟨y, ?_⟩
  by_contra hn
  have hi := Subgroup.index_strictAnti (lt_of_le_of_ne hy hn)
  rw [index_stabilizer_of_transitive, Nat.card_fin, hH] at hi
  omega

/-- Abstract automorphisms preserve the natural point-stabilizer class. -/
public theorem m23_stabilizer_map_eq (f : MulAut M23) (x : Fin 23) :
    ∃ y : Fin 23, (stabilizer M23 x).map f.toMonoidHom = stabilizer M23 y := by
  let := m23_isPretransitive
  apply m23_index_twenty_three_eq_stabilizer
  rw [Subgroup.index_map_of_bijective f.bijective,
    index_stabilizer_of_transitive, Nat.card_fin]

private theorem normalizer_fixedHeptad
    (σ : Subgroup.normalizer (M23 : Set (Equiv.Perm (Fin 23))))
    (t : M23) (_ht : orderOf t = 2) :
    M23Geometry.fixedHeptad (M23.normalizerMonoidHom σ t) =
      (σ : Equiv.Perm (Fin 23)) • M23Geometry.fixedHeptad t := by
  ext x
  rw [M23Geometry.mem_fixedHeptad, Finset.mem_smul_finset]
  change σ.val (t.val (σ.val⁻¹ x)) = x ↔ _
  constructor
  · intro hx
    refine ⟨σ.val⁻¹ x, (M23Geometry.mem_fixedHeptad _ _).mpr ?_, ?_⟩
    · change t.val (σ.val⁻¹ x) = σ.val⁻¹ x
      exact σ.val.injective (hx.trans (Equiv.apply_symm_apply σ.val x).symm)
    · exact Equiv.apply_symm_apply σ.val x
  · rintro ⟨y, hy, rfl⟩
    have hty := (M23Geometry.mem_fixedHeptad t y).mp hy
    change t.val y = y at hty
    simp only [Equiv.Perm.smul_def,
      show σ.val⁻¹ (σ.val y) = y from σ.val.symm_apply_apply y, hty]

private theorem m23_heptad_eq_fixedHeptad (B : Finset (Fin 23)) (hB : B ∈ m23Blocks) :
    ∃ t : M23, orderOf t = 2 ∧ M23Geometry.fixedHeptad t = B := by
  obtain ⟨g, hg⟩ := M23Geometry.exists_smul_omega_eq hB
  refine ⟨MulAut.conj g M23Geometry.involutionRepresentative,
    ((MulAut.conj g).orderOf_eq M23Geometry.involutionRepresentative).trans
      M23Geometry.involutionRepresentative_order, ?_⟩
  rw [M23Geometry.fixedHeptad_conj,
    M23Geometry.fixedHeptad_involutionRepresentative]
  exact hg

private theorem normalizer_mem_M23
    (σ : Subgroup.normalizer (M23 : Set (Equiv.Perm (Fin 23)))) :
    (σ : Equiv.Perm (Fin 23)) ∈ M23 := by
  rw [mem_M23_iff]
  apply Set.Subset.antisymm
  · rintro B ⟨C, hC, rfl⟩
    obtain ⟨t, ht, rfl⟩ := m23_heptad_eq_fixedHeptad C hC
    change (σ : Equiv.Perm (Fin 23)) • M23Geometry.fixedHeptad t ∈ m23Blocks
    rw [← normalizer_fixedHeptad σ t ht]
    exact M23Geometry.fixedHeptad_mem
      ((M23.normalizerMonoidHom σ).orderOf_eq t |>.trans ht)
  · intro B hB
    refine ⟨(σ : Equiv.Perm (Fin 23))⁻¹ • B, ?_, ?_⟩
    · obtain ⟨t, ht, rfl⟩ := m23_heptad_eq_fixedHeptad B hB
      change ((σ : Equiv.Perm (Fin 23))⁻¹ • M23Geometry.fixedHeptad t) ∈ m23Blocks
      have hn := normalizer_fixedHeptad σ⁻¹ t ht
      change M23Geometry.fixedHeptad (M23.normalizerMonoidHom σ⁻¹ t) =
        ((σ : Equiv.Perm (Fin 23))⁻¹ • M23Geometry.fixedHeptad t) at hn
      rw [← hn]
      exact M23Geometry.fixedHeptad_mem
        ((M23.normalizerMonoidHom σ⁻¹).orderOf_eq t |>.trans ht)
    · simp only [smul_inv_smul]

/-- The concrete M₂₃ is self-normalizing in its natural symmetric group. -/
public theorem m23_normalizer_eq :
    Subgroup.normalizer (M23 : Set (Equiv.Perm (Fin 23))) = M23 := by
  apply le_antisymm
  · intro σ hσ
    exact normalizer_mem_M23 ⟨σ, hσ⟩
  · exact Subgroup.le_normalizer

/-- Every abstract automorphism of the concrete M₂₃ is inner. -/
public theorem m23_conj_surjective :
    Function.Surjective (MulAut.conj : M23 →* MulAut M23) :=
  Subgroup.conj_surjective_of_stabilizers_of_normalizer M23 (0 : Fin 23)
    (fun f => m23_stabilizer_map_eq f 0) m23_normalizer_eq

/-- Every involutory automorphism of M₂₃ is inner. -/
public theorem m23_involution_automorphism_inner (r : MulAut M23)
    (_hr : orderOf r = 2) : ∃ g : M23, r = MulAut.conj g :=
  by
    obtain ⟨g, hg⟩ := m23_conj_surjective r
    exact ⟨g, hg.symm⟩

/-- Every two-power-order automorphism centralizing a Sylow 2-subgroup pointwise is inner. -/
public theorem m23_sylow_centralizing_two_automorphism_inner (r : MulAut M23)
    (n : ℕ) (S : Sylow 2 M23) (_hr : r ^ (2 ^ n) = 1)
    (_hS : ∀ x ∈ S, r x = x) : ∃ g : M23, r = MulAut.conj g :=
  by
    obtain ⟨g, hg⟩ := m23_conj_surjective r
    exact ⟨g, hg.symm⟩

end Sporadic.Mathieu
