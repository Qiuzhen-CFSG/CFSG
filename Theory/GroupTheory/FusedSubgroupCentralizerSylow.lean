module

public import Theory.GroupTheory.CharacteristicCentralizerSylow
public import Theory.GroupTheory.PGroup.CharacteristicCenterReduction

/-!
# Promoting the elementary subgroup to a Sylow subgroup

Suppose A is a two-subgroup of K and E is a nontrivial subgroup of A.
If E# is exactly the intersection of A# with an ambient conjugacy class,
then N_K(A) normalizes E. If C_K(e) = A for every e in E#, the normalizer
condition in a finite two-group forces A to be Sylow in K: a larger
two-normalizer would have a nontrivial central element in its normal E,
and would therefore lie in A.

This proves the Sylow assertion used at the start of Aschbacher 47.1,
printed p.260, without assuming the order of C_G(t).
-/

@[expose] public section
open Subgroup

namespace Subgroup

variable {G : Type*} [Group G] [Finite G]

theorem exists_sylow_of_fused_subgroup (K A E : Subgroup G) (z : G)
    (hA : IsPGroup 2 A) (hAK : A ≤ K) (hEA : E ≤ A) (hE : E ≠ ⊥)
    (hfusion : ∀ e ∈ A, e ≠ 1 → (IsConj z e ↔ e ∈ E))
    (hcentral : ∀ e ∈ E, e ≠ 1 → K ⊓ centralizer ({e} : Set G) ≤ A) :
    ∃ S : Sylow 2 K, (S : Subgroup K).map K.subtype = A := by
  have hnorm : normalizer (A : Set G) ≤ normalizer (E : Set G) := by
    apply le_normalizer_iff.mpr
    intro g hg e he
    by_cases he1 : e = 1
    · simpa only [he1, mul_one, mul_inv_cancel] using E.one_mem
    have hgeA := (mem_normalizer_iff.mp hg e).mp (hEA he)
    have hge1 : g * e * g⁻¹ ≠ 1 := by
      intro hh
      exact he1 ((MulAut.conj g).injective (hh.trans (map_one _).symm))
    exact (hfusion _ hgeA hge1).mp
      (((hfusion e (hEA he) he1).mpr he).trans (isConj_iff.mpr ⟨g, rfl⟩))
  have hmax (B : Subgroup G) (hB : IsPGroup 2 B) (hAB : A ≤ B)
      (hBK : B ≤ K) (hBN : B ≤ normalizer (A : Set G)) : B = A := by
    have hEB : E ≤ B := hEA.trans hAB
    let : (E.subgroupOf B).Normal :=
      (normal_subgroupOf_iff_le_normalizer hEB).mpr (hBN.trans hnorm)
    have hne : E.subgroupOf B ≠ ⊥ := by
      intro hh
      apply hE
      rw [← map_subgroupOf_eq_of_le hEB, hh, Subgroup.map_bot]
    obtain ⟨e, he, he1⟩ := (center B ⊓ E.subgroupOf B).bot_or_exists_ne_one.resolve_left
      (center_inf_ne_bot_of_normal hB _ hne)
    have he1G : (e : G) ≠ 1 := fun hh => he1 (Subtype.ext hh)
    apply le_antisymm _ hAB
    intro b hb
    apply hcentral e he.2 he1G
    exact ⟨hBK hb, mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (mem_center_iff.mp he.1 ⟨b, hb⟩))⟩
  have hAKp : IsPGroup 2 (A.subgroupOf K) := hA.comap_subtype
  obtain ⟨S, hAS⟩ := hAKp.exists_le_sylow
  let B := (S : Subgroup K).map K.subtype
  have hAB : A ≤ B := by
    rw [← map_subgroupOf_eq_of_le hAK]
    exact map_mono hAS
  exact ⟨S, prime_overgroup_eq_of_normalizer_control A K (normalizer (A : Set G))
    le_rfl hmax B (S.isPGroup'.map K.subtype) hAB (map_subtype_le _)⟩

end Subgroup
