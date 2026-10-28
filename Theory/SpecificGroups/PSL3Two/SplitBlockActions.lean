module

public import Theory.SpecificGroups.BinaryFour.SplitBlockPair
public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic

/-!+# Aligning the common four-group in the split binary block

The row and column involutions act on the four-dimensional binary space as
the regular module of their four-group. Consequently an automorphism
normalizing this four-group is determined by the images of its two generators
and one cyclic vector. The finite calculation below checks these 4 · 4 · 16
possibilities. Every nonidentity cubic normalizer is conjugate, by the
four-group itself, to the specified cubic or its inverse.

This conjugation preserves both the marked central vector and the parabolic
image. Thus a cubic extending the *actual common four-group* gives the
published compatible pair, without an independent choice of coordinates for
the second local group.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, proof of
14.4.4, printed p.1007. This proves the coordinate alignment; the split block
and the quaternion residual must still supply their actual local actions.
-/

namespace BinaryFourSplitPair.SplitBlockActions

open Subgroup

private def overlapWord (i : Fin 4) : MulAut E := ![1, row, column, row * column] i

private theorem overlapWord_mul : ∀ i j : Fin 4, ∃ k : Fin 4,
    ∀ v, (overlapWord i * overlapWord j) v = overlapWord k v := by decide +kernel

private theorem overlapWord_inv : ∀ i : Fin 4,
    ∀ v, (overlapWord i)⁻¹ v = overlapWord i v := by decide +kernel

private theorem overlapWord_mem (i : Fin 4) : overlapWord i ∈ overlap := by
  have hr : row ∈ overlap := subset_closure (by simp)
  have hc : column ∈ overlap := subset_closure (by simp)
  have h : ∀ j : Fin 4, j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by decide
  rcases h i with rfl | rfl | rfl | rfl
  · exact one_mem _
  · exact hr
  · exact hc
  · exact mul_mem hr hc

private theorem mem_overlap_iff (f : MulAut E) :
    f ∈ overlap ↔ ∃ i : Fin 4, overlapWord i = f := by
  let D : Subgroup (MulAut E) := {
    carrier := Set.range overlapWord
    one_mem' := ⟨0, rfl⟩
    mul_mem' := by
      rintro _ _ ⟨i, rfl⟩ ⟨j, rfl⟩
      obtain ⟨k, hk⟩ := overlapWord_mul i j
      exact ⟨k, (MulEquiv.ext hk).symm⟩
    inv_mem' := by
      rintro _ ⟨i, rfl⟩
      exact ⟨i, (MulEquiv.ext (overlapWord_inv i)).symm⟩ }
  constructor
  · apply (show overlap ≤ D from ?_)
    apply (closure_le _).2
    intro x hx
    rcases (show x = row ∨ x = column from by simpa using hx) with rfl | rfl
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
  · rintro ⟨i, rfl⟩
    exact overlapWord_mem i

private def seed : E := Multiplicative.ofAdd ![0,0,1,0]

private def orbitWord (r q : MulAut E) (t : E) (v : E) : E :=
  t ^ (v.toAdd 0 + v.toAdd 1 + v.toAdd 2 + v.toAdd 3).val *
  r t ^ (v.toAdd 0 + v.toAdd 1).val *
  q t ^ (v.toAdd 1 + v.toAdd 3).val *
  r (q t) ^ (v.toAdd 1).val

private theorem orbitWord_seed : ∀ v, orbitWord row column seed v = v := by
  decide +kernel

private theorem aut_orbitWord (f : MulAut E) (v : E) :
    f v = orbitWord (f * row * f⁻¹) (f * column * f⁻¹) (f seed) v := by
  conv_lhs => rw [← orbitWord_seed v]
  simp only [orbitWord, map_mul, map_pow, MulAut.mul_apply, MulAut.inv_apply,
    MulEquiv.symm_apply_apply]

-- Only the two four-group images and the cyclic vector are enumerated.
set_option synthInstance.maxSize 512 in
set_option maxRecDepth 2000 in
private theorem cubic_census : ∀ i j : Fin 4, ∀ t : E,
    let u := orbitWord (overlapWord i) (overlapWord j) t
    (∀ v, u (u (u v)) = v) →
      (∀ v, u v = v) ∨ ∃ k : Fin 4,
        (∀ v, u v = (overlapWord k * normalizingCubic * (overlapWord k)⁻¹) v) ∨
        (∀ v, u v = (overlapWord k * normalizingCubic⁻¹ * (overlapWord k)⁻¹) v) := by
  dsimp only
  decide +kernel

/-- Every cubic normalizing the displayed four-group has the same relative
position, up to conjugation by that four-group and inversion. -/
public theorem cubic_normal_form (f : MulAut E)
    (hn : f ∈ normalizer (overlap : Set (MulAut E)))
    (h3 : f ^ 3 = 1) (hne : f ≠ 1) :
    ∃ d ∈ overlap, f = d * normalizingCubic * d⁻¹ ∨
      f = d * normalizingCubic⁻¹ * d⁻¹ := by
  have hr : f * row * f⁻¹ ∈ overlap :=
    (mem_normalizer_iff.mp hn row).mp (subset_closure (by simp))
  have hc : f * column * f⁻¹ ∈ overlap :=
    (mem_normalizer_iff.mp hn column).mp (subset_closure (by simp))
  obtain ⟨i, hi⟩ := (mem_overlap_iff _).mp hr
  obtain ⟨j, hj⟩ := (mem_overlap_iff _).mp hc
  have hf (v : E) : f v = orbitWord (overlapWord i) (overlapWord j) (f seed) v := by
    rw [aut_orbitWord f, hi, hj]
  have hcube : ∀ v, f (f (f v)) = v := by
    intro v
    have h := DFunLike.congr_fun h3 v
    simpa only [pow_succ, pow_zero, one_mul, MulAut.mul_apply, MulAut.one_apply] using h
  have htest : ∀ v, orbitWord (overlapWord i) (overlapWord j) (f seed)
      (orbitWord (overlapWord i) (overlapWord j) (f seed)
        (orbitWord (overlapWord i) (overlapWord j) (f seed) v)) = v := by
    intro v
    simpa only [← hf] using hcube v
  rcases cubic_census i j (f seed) htest with hid | ⟨k, hk | hk⟩
  · exact (hne (MulEquiv.ext fun v => (hf v).trans (hid v))).elim
  · exact ⟨overlapWord k, overlapWord_mem k,
      Or.inl (MulEquiv.ext fun v => (hf v).trans (hk v))⟩
  · exact ⟨overlapWord k, overlapWord_mem k,
      Or.inr (MulEquiv.ext fun v => (hf v).trans (hk v))⟩

public theorem overlap_le_parabolic : overlap ≤ parabolic := by
  apply closure_mono
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
  exact hx.elim Or.inl (fun h => Or.inr (Or.inl h))

/-- Changing coordinates by the common four-group preserves the source z. -/
public theorem overlap_fixes_point {d : MulAut E} (hd : d ∈ overlap) : d point = point := by
  obtain ⟨i, rfl⟩ := (mem_overlap_iff d).mp hd
  exact (by decide +kernel : ∀ i, overlapWord i point = point) i

/-- The displayed quaternion image is the cubic extension of the common
four-group, with its actual embedding retained. -/
public theorem quaternion_eq_sup_zpowers :
    quaternion = overlap ⊔ zpowers normalizingCubic := by
  apply le_antisymm
  · apply (closure_le _).2
    intro x hx
    rcases (show x = row ∨ x = column ∨ x = normalizingCubic from by simpa using hx)
      with rfl | rfl | rfl
    · exact (show overlap ≤ overlap ⊔ zpowers normalizingCubic from le_sup_left)
        (subset_closure (by simp))
    · exact (show overlap ≤ overlap ⊔ zpowers normalizingCubic from le_sup_left)
        (subset_closure (by simp))
    · exact (show zpowers normalizingCubic ≤ overlap ⊔ zpowers normalizingCubic from le_sup_right)
        (mem_zpowers _)
  · apply sup_le
    · apply closure_mono
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
      exact hx.elim Or.inl (fun h => Or.inr (Or.inl h))
    · exact zpowers_le.mpr (subset_closure (by simp))

/-- One simultaneous change of coordinates aligns the cubic extension,
preserves the parabolic image, and fixes the marked central point. -/
public theorem align_cubic_extension (f : MulAut E)
    (hn : f ∈ normalizer (overlap : Set (MulAut E)))
    (h3 : f ^ 3 = 1) (hne : f ≠ 1) :
    ∃ d ∈ overlap, d point = point ∧
      parabolic.map (MulAut.conj d).toMonoidHom = parabolic ∧
      (overlap ⊔ zpowers f).map (MulAut.conj d).toMonoidHom = quaternion := by
  obtain ⟨k, hk, hf⟩ := cubic_normal_form f hn h3 hne
  have hki : k⁻¹ ∈ overlap := inv_mem hk
  refine ⟨k⁻¹, hki, overlap_fixes_point hki, ?_, ?_⟩
  · exact mem_normalizer_iff_map_conj_eq.mp
      (parabolic.le_normalizer (overlap_le_parabolic hki))
  · have hD : overlap.map (MulAut.conj k⁻¹).toMonoidHom = overlap :=
      mem_normalizer_iff_map_conj_eq.mp (overlap.le_normalizer hki)
    rw [Subgroup.map_sup, hD, MonoidHom.map_zpowers, quaternion_eq_sup_zpowers]
    change overlap ⊔ zpowers (k⁻¹ * f * k) = overlap ⊔ zpowers normalizingCubic
    rcases hf with hf | hf
    · rw [hf]
      simp [mul_assoc]
    · rw [hf]
      simp [mul_assoc]

end BinaryFourSplitPair.SplitBlockActions
