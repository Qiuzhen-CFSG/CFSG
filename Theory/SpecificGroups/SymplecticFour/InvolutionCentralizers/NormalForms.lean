module

public import Theory.SpecificGroups.SymplecticFour.InvolutionCentralizers.Basic
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.TwoLocalCover.Geometry
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Plane.Extension
public import Theory.SpecificGroups.SymplecticFour.RootNormalizerResidual.Weyl

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Normal forms for involutions in symplectic four-space

The moved space of an involution is isotropic. An actual symplectic change
of basis moves it to the standard point or plane, forcing an upper shear
with symmetric two-by-two block. A moved line gives a long root; a zero
diagonal block gives a short root. In the remaining rank-two case, finite
characteristic-two fields have square roots, and elimination factors the
block as `A * Aᵀ`. The block-diagonal symplectic lift of `A` conjugates the
published c₂ representative to the shear.

Source: Aschbacher–Smith, Definition E.2.6 (printed p.218), and the symplectic
involution types used in Lemma 16.1.4(1),(2) (printed p.1171).
-/

public noncomputable section
set_option linter.unusedSimpArgs false
open Matrix
open Theory.SpecificGroups.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.InvolutionTypes
open Theory.SpecificGroups.SymplecticFour.InvolutionCentralizers

namespace Theory.SpecificGroups.SymplecticFour.InvolutionCentralizers
open TwoLocalCover
variable {F : Type*} [Field F]
theorem movedSpace_conj (h g : Sp F) :
    movedSpace (h * g * h⁻¹) = (movedSpace g).map (toLinear h).toLinearMap := by
  ext x
  constructor
  · rintro ⟨v, rfl⟩
    refine ⟨g • (h⁻¹ • v) - h⁻¹ • v, ⟨h⁻¹ • v, rfl⟩, ?_⟩
    change toLinear h (_ - _) = (h * g * h⁻¹) • v - v
    simp only [map_sub, toLinear_apply, mul_smul, smul_inv_smul]
  · rintro ⟨y, ⟨v, rfl⟩, rfl⟩
    refine ⟨h • v, ?_⟩
    change (h * g * h⁻¹) • (h • v) - h • v = toLinear h (g • v - v)
    simp only [map_sub, toLinear_apply, mul_smul, inv_smul_smul]

theorem matrix_of_movedSpace_le_plane (g : Sp F) (hg : movedSpace g ≤ plane F) :
    g.val = fromBlocks 1 g.val.toBlocks₁₂ 0 1 ∧ g.val.toBlocks₁₂.IsSymm := by
  have hrows (i : Fin 2) (j : Fin 2 ⊕ Fin 2) :
      g.val (.inr i) j = (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) (.inr i) j := by
    have hx := hg (show g • (Pi.single j (1 : F) : Vector F) - Pi.single j 1 ∈ movedSpace g from
      ⟨Pi.single j 1, rfl⟩)
    have hi := hx i
    simpa [smul_eq_mulVec, Matrix.mulVec_single, Pi.single_apply,
      Matrix.one_apply, eq_comm] using (sub_eq_zero.mp hi)
  have hC : g.val.toBlocks₂₁ = 0 := by
    ext i j
    simpa [Matrix.toBlocks₂₁] using hrows i (.inl j)
  have hD : g.val.toBlocks₂₂ = 1 := by
    ext i j
    simpa [Matrix.toBlocks₂₂, Matrix.one_apply] using hrows i (.inr j)
  have hs := g.property
  rw [← g.val.fromBlocks_toBlocks] at hs
  have hb := SymplecticGroup.fromBlocks_mem_iff.mp hs
  simp only [hC, hD, mul_zero, transpose_zero, zero_mul, transpose_one, mul_one,
    one_mul, sub_zero, true_and] at hb
  have hA : g.val.toBlocks₁₁ = 1 := by
    have := congrArg Matrix.transpose hb.2
    simpa using this
  exact ⟨by nth_rw 1 [← g.val.fromBlocks_toBlocks]; rw [hA, hC, hD], hb.1⟩
end Theory.SpecificGroups.SymplecticFour.InvolutionCentralizers

namespace Theory.SpecificGroups.SymplecticFour.InvolutionCentralizers
open TwoLocalCover
open InvolutionTypes
open Representation.OneCohomology.SymplecticFour
variable {F : Type*} [Field F]

private theorem root0_move (t : F) (v : Vector F) :
    rootElement 0 t • v - v = (t * v (.inr 0)) • e 0 := by
  funext i
  rcases i with i | i <;> fin_cases i <;>
    simp [rootElement, rootMatrix, Matrix.mulVec, dotProduct,
      Fintype.sum_sum_type, Fin.sum_univ_two, Matrix.single, e]

theorem movedSpace_root0 {t : F} (ht : t ≠ 0) : movedSpace (rootElement 0 t) = point F := by
  ext x
  constructor
  · rintro ⟨v, rfl⟩
    change rootElement 0 t • v - v ∈ point F
    rw [root0_move]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  · intro hx
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
    refine ⟨Pi.single (.inr 0) (a / t), ?_⟩
    change rootElement 0 t • (Pi.single (.inr 0) (a / t) : Vector F) - _ = _
    change rootElement 0 t • (Pi.single (.inr 0) (a / t) : Vector F) - (Pi.single (.inr 0) (a / t) : Vector F) = _
    rw [root0_move]
    simp only [Pi.single_apply, if_true]
    field_simp [ht]

private theorem root4_move (t : F) (v : Vector F) :
    rootElement 4 t • v - v =
      Sum.elim ![t * v (.inr 1), t * v (.inr 0)] 0 := by
  funext i
  rcases i with i | i <;> fin_cases i <;>
    simp [rootElement, rootMatrix, Matrix.mulVec, dotProduct,
      Fintype.sum_sum_type, Fin.sum_univ_two, Matrix.single]

theorem movedSpace_root4 {t : F} (ht : t ≠ 0) : movedSpace (rootElement 4 t) = plane F := by
  ext x
  constructor
  · rintro ⟨v, rfl⟩
    change rootElement 4 t • v - v ∈ plane F
    rw [root4_move]
    intro i
    rfl
  · intro hx
    refine ⟨Sum.elim 0 ![x (.inl 1) / t, x (.inl 0) / t], ?_⟩
    change rootElement 4 t • (Sum.elim 0 ![x (.inl 1) / t, x (.inl 0) / t] : Vector F) - (Sum.elim 0 ![x (.inl 1) / t, x (.inl 0) / t] : Vector F) = _
    rw [root4_move]
    funext i
    rcases i with i | i <;> fin_cases i
    · simp [Fin.sum_univ_two]
      field_simp [ht]
    · simp [Fin.sum_univ_two]
      field_simp [ht]
    · exact (mem_plane _).mp hx 0 |>.symm
    · exact (mem_plane _).mp hx 1 |>.symm

theorem root4_orthogonal [CharP F 2] (t : F) : ∀ v : Vector F, form F v (rootElement 4 t • v) = 0 := by
  intro v
  have h : rootElement 4 t • v = v + Sum.elim ![t * v (.inr 1), t * v (.inr 0)] 0 :=
    (sub_eq_iff_eq_add.mp (root4_move t v)).trans (add_comm _ _)
  rw [h, map_add, form_alternating.self_eq_zero, zero_add]
  simp only [form_apply, Fin.sum_univ_two, Sum.elim_inl, Sum.elim_inr,
    Pi.zero_apply, mul_zero, zero_sub, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  ring_nf
  simp [CharTwo.two_eq_zero]
end Theory.SpecificGroups.SymplecticFour.InvolutionCentralizers
namespace Theory.SpecificGroups.SymplecticFour.InvolutionCentralizers
open InvolutionTypes
variable {F : Type*} [Field F]

private theorem form_conj (h g : Sp F) (v : Vector F) :
    form F v ((h * g * h⁻¹) • v) =
      form F (h⁻¹ • v) (g • (h⁻¹ • v)) := by
  simpa only [mul_smul, smul_inv_smul] using preserves_form h (h⁻¹ • v) (g • (h⁻¹ • v))

private theorem orthogonal_conj_iff (h g : Sp F) :
    (∀ v : Vector F, form F v ((h * g * h⁻¹) • v) = 0) ↔
      ∀ v : Vector F, form F v (g • v) = 0 := by
  constructor
  · intro hv v
    simpa only [form_conj, inv_smul_smul] using hv (h • v)
  · intro hv v
    rw [form_conj]
    exact hv _

theorem isB1_conj_iff (h g : Sp F) : IsB1 (h * g * h⁻¹) ↔ IsB1 g := by
  unfold IsB1
  rw [movedSpace_conj, (toLinear h).finrank_map_eq]
  exact and_congr_left fun _ => congrArg (· = 2) ((MulAut.conj h).orderOf_eq g) |>.to_iff

theorem isA2_conj_iff (h g : Sp F) : IsA2 (h * g * h⁻¹) ↔ IsA2 g := by
  unfold IsA2
  rw [movedSpace_conj, (toLinear h).finrank_map_eq, orthogonal_conj_iff]
  exact and_congr_left fun _ => congrArg (· = 2) ((MulAut.conj h).orderOf_eq g) |>.to_iff

theorem isC2_conj_iff (h g : Sp F) : IsC2 (h * g * h⁻¹) ↔ IsC2 g := by
  have he : (∃ v : Vector F, form F v ((h * g * h⁻¹) • v) ≠ 0) ↔
      ∃ v : Vector F, form F v (g • v) ≠ 0 := by
    simpa only [not_forall] using not_congr (orthogonal_conj_iff h g)
  unfold IsC2
  rw [movedSpace_conj, (toLinear h).finrank_map_eq, he]
  exact and_congr_left fun _ => congrArg (· = 2) ((MulAut.conj h).orderOf_eq g) |>.to_iff
end Theory.SpecificGroups.SymplecticFour.InvolutionCentralizers

namespace Theory.SpecificGroups.SymplecticFour.InvolutionCentralizers
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

private theorem pivot_factor (a b c : F) (ha : a ≠ 0) :
    ∃ A : Matrix (Fin 2) (Fin 2) F, A * Aᵀ = !![a,b;b,c] := by
  obtain ⟨u, hu⟩ := Finite.surjective_of_injective (CharTwo.sq_injective (R := F)) a
  have hu0 : u ≠ 0 := by intro h; simp [h] at hu; exact ha hu.symm
  obtain ⟨v, hv⟩ := Finite.surjective_of_injective (CharTwo.sq_injective (R := F))
    (c - (b/u)^2)
  refine ⟨!![u,0;b/u,v], ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, ← pow_two, hu, hv, hu0]
  all_goals field_simp

theorem symmetric_factorization (B : Matrix (Fin 2) (Fin 2) F) (hs : B.IsSymm) (hd : B.det ≠ 0)
    (ha : B 0 0 ≠ 0 ∨ B 1 1 ≠ 0) :
    ∃ A : Matrix (Fin 2) (Fin 2) F, IsUnit A ∧ B = A * Aᵀ := by
  have he : B 1 0 = B 0 1 := congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M 0 1) hs
  have hB : B = !![B 0 0,B 0 1;B 0 1,B 1 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [he]
  have hf : ∃ A : Matrix (Fin 2) (Fin 2) F, B = A * Aᵀ := by
    rcases ha with ha | ha
    · obtain ⟨A,hA⟩ := pivot_factor (B 0 0) (B 0 1) (B 1 1) ha
      exact ⟨A, hB.trans hA.symm⟩
    · obtain ⟨A,hA⟩ := pivot_factor (B 1 1) (B 0 1) (B 0 0) ha
      let S : Matrix (Fin 2) (Fin 2) F := !![0,1;1,0]
      refine ⟨S * A, ?_⟩
      rw [Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc A, hA, ← Matrix.mul_assoc]
      rw [hB]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [S, Matrix.mul_apply, Fin.sum_univ_two]
  obtain ⟨A, hA⟩ := hf
  refine ⟨A, (Matrix.isUnit_iff_isUnit_det A).mpr (isUnit_iff_ne_zero.mpr ?_), hA⟩
  intro h
  apply hd
  rw [hA, Matrix.det_mul, Matrix.det_transpose, h, zero_mul]
end Theory.SpecificGroups.SymplecticFour.InvolutionCentralizers

namespace Theory.SpecificGroups.SymplecticFour.InvolutionCentralizers
open InvolutionTypes TwoLocalCover
open Representation.OneCohomology.SymplecticFour
variable {F : Type*} [Field F]

private theorem shear_move (g : Sp F) (B : Matrix (Fin 2) (Fin 2) F)
    (hg : g.val = fromBlocks 1 B 0 1) (v : Vector F) :
    g • v - v = Sum.elim (B *ᵥ (fun i => v (.inr i))) 0 := by
  funext i
  rcases i with i | i <;>
    simp [smul_eq_mulVec, hg, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.one_apply]

private theorem shear_eq_root4 (g : Sp F)
    (hg : g.val = fromBlocks 1 g.val.toBlocks₁₂ 0 1)
    (hs : g.val.toBlocks₁₂.IsSymm)
    (h0 : g.val.toBlocks₁₂ 0 0 = 0) (h1 : g.val.toBlocks₁₂ 1 1 = 0) :
    g = rootElement 4 (g.val.toBlocks₁₂ 0 1) := by
  have he := hs.apply 0 1
  apply Subtype.ext
  rw [hg]
  change fromBlocks 1 g.val.toBlocks₁₂ 0 1 = rootMatrix 4 (g.val.toBlocks₁₂ 0 1)
  have hB : g.val.toBlocks₁₂ = single 0 1 (g.val.toBlocks₁₂ 0 1) +
      single 1 0 (g.val.toBlocks₁₂ 0 1) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.single, h0, h1, he]
  exact congrArg (fun B : Matrix (Fin 2) (Fin 2) F => fromBlocks 1 B 0 1) hB

private theorem eq_root0_of_movedSpace_le_point (g : Sp F)
    (hg : movedSpace g ≤ point F) :
    g = rootElement 0 (g.val.toBlocks₁₂ 0 0) := by
  obtain ⟨hM, hs⟩ := matrix_of_movedSpace_le_plane g (hg.trans point_le_plane)
  have hb (j : Fin 2) : g.val.toBlocks₁₂ 1 j = 0 := by
    have hx := hg (show g • (Pi.single (.inr j) (1 : F) : Vector F) - Pi.single (.inr j) 1 ∈
      movedSpace g from ⟨Pi.single (.inr j) 1, rfl⟩)
    have he := (mem_point_iff _).mp hx |>.1
    simpa [smul_eq_mulVec, Matrix.mulVec_single, Matrix.toBlocks₁₂] using he
  have he := hs.apply 0 1
  apply Subtype.ext
  rw [hM]
  change fromBlocks 1 g.val.toBlocks₁₂ 0 1 = rootMatrix 0 (g.val.toBlocks₁₂ 0 0)
  have hB : g.val.toBlocks₁₂ = single 0 0 (g.val.toBlocks₁₂ 0 0) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.single, hb, ← he]
  exact congrArg (fun B : Matrix (Fin 2) (Fin 2) F => fromBlocks 1 B 0 1) hB

private theorem diagonal_zero_of_orthogonal (g : Sp F)
    (hg : g.val = fromBlocks 1 g.val.toBlocks₁₂ 0 1)
    (ho : ∀ v : Vector F, form F v (g • v) = 0) (i : Fin 2) :
    g.val.toBlocks₁₂ i i = 0 := by
  have h := ho (Pi.single (.inr i) 1)
  change form F (Pi.single (.inr i) 1) (g.val *ᵥ (Pi.single (.inr i) 1)) = 0 at h
  rw [hg] at h
  fin_cases i <;>
    simpa [form_apply, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
      Matrix.single, Pi.single_apply, Fin.sum_univ_two] using h

private theorem block_det_ne_zero (g : Sp F) (hg : movedSpace g = plane F) :
    g.val.toBlocks₁₂.det ≠ 0 := by
  have hM := (matrix_of_movedSpace_le_plane g (le_of_eq hg)).1
  have hsurj : Function.Surjective g.val.toBlocks₁₂.mulVec := by
    intro x
    have hx : Sum.elim x (0 : Fin 2 → F) ∈ movedSpace g := by rw [hg]; intro i; rfl
    obtain ⟨v, hv⟩ := hx
    change g • v - v = Sum.elim x 0 at hv
    rw [shear_move g _ hM] at hv
    exact ⟨fun i => v (.inr i), funext fun i => congrFun hv (.inl i)⟩
  exact isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp
    (Matrix.mulVec_surjective_iff_isUnit.mp hsurj))

variable [CharP F 2]

theorem exists_conjugate_movedSpace_standard (g : Sp F) (hg : orderOf g = 2) :
    ∃ h : Sp F, movedSpace (h * g * h⁻¹) = point F ∨
      movedSpace (h * g * h⁻¹) = plane F := by
  simpa only [movedSpace_conj] using isotropic_subspace_conjugate_standard (movedSpace g)
    (movedSpace_ne_bot g (orderOf_eq_prime_iff.mp hg).2)
    (movedSpace_isotropic g (orderOf_eq_prime_iff.mp hg).1)

theorem isB1_conjugate_root0 (g : Sp F) (hg : IsB1 g) :
    ∃ (h : Sp F) (t : F), t ≠ 0 ∧ g = h * rootElement 0 t * h⁻¹ := by
  obtain ⟨h, hh⟩ := exists_conjugate_movedSpace_standard g hg.1
  have htype := (isB1_conj_iff h g).mpr hg
  have hp : movedSpace (h * g * h⁻¹) = point F := by
    rcases hh with hh | hh
    · exact hh
    · have hd := htype.2
      rw [hh, finrank_plane] at hd
      omega
  have he := eq_root0_of_movedSpace_le_point (h * g * h⁻¹) (le_of_eq hp)
  let t := (h * g * h⁻¹).val.toBlocks₁₂ 0 0
  refine ⟨h⁻¹, t, ?_, ?_⟩
  · intro ht
    have ht' : (h * g * h⁻¹).val.toBlocks₁₂ 0 0 = 0 := by simpa [t] using ht
    rw [ht'] at he
    rw [RootSubgroup.element_zero] at he
    have hn := (orderOf_eq_prime_iff.mp htype.1).2
    exact hn he
  · have he' : h * g * h⁻¹ = rootElement 0 t := by simpa [t] using he
    rw [← he']
    simp [mul_assoc]

theorem isA2_conjugate_root4 (g : Sp F) (hg : IsA2 g) :
    ∃ (h : Sp F) (t : F), t ≠ 0 ∧ g = h * rootElement 4 t * h⁻¹ := by
  obtain ⟨h, hh⟩ := exists_conjugate_movedSpace_standard g hg.1
  have htype := (isA2_conj_iff h g).mpr hg
  have hp : movedSpace (h * g * h⁻¹) ≤ plane F := by
    rcases hh with hh | hh
    · exact hh.le.trans point_le_plane
    · exact hh.le
  obtain ⟨hM, hs⟩ := matrix_of_movedSpace_le_plane _ hp
  have he := shear_eq_root4 _ hM hs
    (diagonal_zero_of_orthogonal _ hM htype.2.2 0)
    (diagonal_zero_of_orthogonal _ hM htype.2.2 1)
  let t := (h * g * h⁻¹).val.toBlocks₁₂ 0 1
  refine ⟨h⁻¹, t, ?_, ?_⟩
  · intro ht
    have ht' : (h * g * h⁻¹).val.toBlocks₁₂ 0 1 = 0 := by simpa [t] using ht
    rw [ht'] at he
    rw [RootSubgroup.element_zero] at he
    exact (orderOf_eq_prime_iff.mp htype.1).2 he
  · have he' : h * g * h⁻¹ = rootElement 4 t := by simpa [t] using he
    rw [← he']
    simp [mul_assoc]

end Theory.SpecificGroups.SymplecticFour.InvolutionCentralizers

namespace Theory.SpecificGroups.SymplecticFour.InvolutionCentralizers
open InvolutionTypes TwoLocalCover
open Representation.OneCohomology.SymplecticFour
variable {F : Type*} [Field F] [Finite F] [CharP F 2]
noncomputable section

private def glLevi (A : Matrix (Fin 2) (Fin 2) F) (hA : IsUnit A) : Sp F :=
  ⟨fromBlocks A 0 0 (A⁻¹)ᵀ, by
    apply SymplecticGroup.fromBlocks_mem_iff.mpr
    simp only [mul_zero, transpose_zero, zero_mul, transpose_transpose, sub_zero,
      true_and]
    have hdet : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hA
    have hh := congrArg Matrix.transpose (Matrix.nonsing_inv_mul A hdet)
    simpa only [transpose_mul, transpose_one] using hh⟩

omit [Finite F] [CharP F 2] in
private theorem glLevi_conj_shear (A : Matrix (Fin 2) (Fin 2) F) (hA : IsUnit A)
    (B : Matrix (Fin 2) (Fin 2) F) (hB : B.IsSymm) :
    glLevi A hA *
      ⟨fromBlocks 1 B 0 1, by
        apply SymplecticGroup.fromBlocks_mem_iff.mpr
        simp only [mul_zero, transpose_zero, zero_mul, transpose_one, one_mul,
          mul_one, sub_zero, and_true, true_and]
        exact hB⟩ * (glLevi A hA)⁻¹ =
      ⟨fromBlocks 1 (A * B * Aᵀ) 0 1, by
        apply SymplecticGroup.fromBlocks_mem_iff.mpr
        simp only [mul_zero, transpose_zero, zero_mul, transpose_one, one_mul,
          mul_one, sub_zero, and_true, true_and]
        change (A * B * Aᵀ)ᵀ = A * B * Aᵀ
        rw [transpose_mul, transpose_mul, transpose_transpose, hB]
        simp [Matrix.mul_assoc]⟩ := by
  let X : Sp F := ⟨fromBlocks A⁻¹ 0 0 Aᵀ, by
    apply SymplecticGroup.fromBlocks_mem_iff.mpr
    simp only [mul_zero, transpose_zero, zero_mul, transpose_transpose, sub_zero,
      true_and]
    have hdet : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hA
    have hh := congrArg Matrix.transpose (Matrix.mul_nonsing_inv A hdet)
    simpa only [transpose_mul, transpose_one] using hh⟩
  have hiSp : (glLevi A hA)⁻¹ = X := by
    apply inv_eq_of_mul_eq_one_right
    apply Subtype.ext
    change fromBlocks A 0 0 (A⁻¹)ᵀ * fromBlocks A⁻¹ 0 0 Aᵀ = _
    simp only [Matrix.fromBlocks_multiply, mul_zero, zero_mul, add_zero, zero_add,
      mul_one, one_mul, transpose_transpose]
    rw [Matrix.mul_nonsing_inv A ((Matrix.isUnit_iff_isUnit_det A).mp hA)]
    have hh := congrArg Matrix.transpose
      (Matrix.mul_nonsing_inv A ((Matrix.isUnit_iff_isUnit_det A).mp hA))
    have hh' : A⁻¹ᵀ * Aᵀ = 1 := by
      simpa only [transpose_mul, transpose_one] using hh
    simp [hh']
  rw [hiSp]
  apply Subtype.ext
  change fromBlocks A 0 0 (A⁻¹)ᵀ * fromBlocks 1 B 0 1 *
      fromBlocks A⁻¹ 0 0 Aᵀ = fromBlocks 1 (A * B * Aᵀ) 0 1
  simp only [Matrix.fromBlocks_multiply, mul_zero, zero_mul, add_zero, zero_add,
    mul_one, one_mul]
  rw [Matrix.mul_nonsing_inv A ((Matrix.isUnit_iff_isUnit_det A).mp hA)]
  have hh := congrArg Matrix.transpose
    (Matrix.mul_nonsing_inv A ((Matrix.isUnit_iff_isUnit_det A).mp hA))
  have hh' : A⁻¹ᵀ * Aᵀ = 1 := by
    simpa only [transpose_mul, transpose_one] using hh
  rw [hh']
end

open InvolutionTypes TwoLocalCover
open Representation.OneCohomology.SymplecticFour
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

omit [Finite F] in
private theorem shear_orthogonal_of_diagonal_zero (g : Sp F)
    (hg : g.val = fromBlocks 1 g.val.toBlocks₁₂ 0 1)
    (hs : g.val.toBlocks₁₂.IsSymm)
    (h0 : g.val.toBlocks₁₂ 0 0 = 0) (h1 : g.val.toBlocks₁₂ 1 1 = 0) :
    ∀ v : Vector F, form F v (g • v) = 0 := by
  rw [shear_eq_root4 g hg hs h0 h1]
  exact root4_orthogonal _

omit [Finite F] [CharP F 2] in
private theorem c2_rep_matrix :
    (rootElement 0 (1 : F) * rootElement 2 1).val =
      fromBlocks 1 (1 : Matrix (Fin 2) (Fin 2) F) 0 1 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [rootElement, rootMatrix, Matrix.fromBlocks_multiply, Matrix.mul_apply,
      Fintype.sum_sum_type, Fin.sum_univ_two, Matrix.single, Matrix.one_apply]

private theorem c2_conjugate_of_factor (g : Sp F)
    (hM : g.val = fromBlocks 1 g.val.toBlocks₁₂ 0 1)
    (hs : g.val.toBlocks₁₂.IsSymm) (hd : g.val.toBlocks₁₂.det ≠ 0)
    (hdiag : g.val.toBlocks₁₂ 0 0 ≠ 0 ∨ g.val.toBlocks₁₂ 1 1 ≠ 0) :
    ∃ h : Sp F, g = h * c2Representative F * h⁻¹ := by
  obtain ⟨A, hA, hAB⟩ := symmetric_factorization g.val.toBlocks₁₂ hs hd hdiag
  have he := glLevi_conj_shear A hA 1 Matrix.isSymm_one
  have hq : (⟨fromBlocks 1 (1 : Matrix (Fin 2) (Fin 2) F) 0 1, by
      apply SymplecticGroup.fromBlocks_mem_iff.mpr
      simp⟩ : Sp F) = c2Representative F := by
    apply Subtype.ext
    exact c2_rep_matrix.symm
  refine ⟨glLevi A hA, ?_⟩
  rw [hq] at he
  apply Subtype.ext
  have hval := congrArg Subtype.val he
  change _ = fromBlocks 1 (A * 1 * Aᵀ) 0 1 at hval
  rw [mul_one] at hval
  exact hM.trans ((congrArg (fun B : Matrix (Fin 2) (Fin 2) F => fromBlocks 1 B 0 1) hAB).trans hval.symm)

theorem isC2_conjugate_c2 (g : Sp F) (hg : IsC2 g) :
    ∃ h : Sp F, g = h * c2Representative F * h⁻¹ := by
  obtain ⟨h, hh⟩ := exists_conjugate_movedSpace_standard g hg.1
  have htype := (isC2_conj_iff h g).mpr hg
  have hp : movedSpace (h * g * h⁻¹) = plane F := by
    rcases hh with hh | hh
    · have hd := htype.2.1
      rw [hh, finrank_point] at hd
      omega
    · exact hh
  let k := h * g * h⁻¹
  obtain ⟨hM, hs⟩ := matrix_of_movedSpace_le_plane k (le_of_eq hp)
  have hd := block_det_ne_zero k hp
  have hdiag : k.val.toBlocks₁₂ 0 0 ≠ 0 ∨ k.val.toBlocks₁₂ 1 1 ≠ 0 := by
    by_contra hn
    push Not at hn
    obtain ⟨v, hv⟩ := htype.2.2
    exact hv (shear_orthogonal_of_diagonal_zero k hM hs hn.1 hn.2 v)
  obtain ⟨a, ha⟩ := c2_conjugate_of_factor k hM hs hd hdiag
  refine ⟨h⁻¹ * a, ?_⟩
  calc
    g = h⁻¹ * k * h := by simp [k, mul_assoc]
    _ = h⁻¹ * (a * c2Representative F * a⁻¹) * h := by rw [ha]
    _ = (h⁻¹ * a) * c2Representative F * (h⁻¹ * a)⁻¹ := by simp [mul_assoc]

end Theory.SpecificGroups.SymplecticFour.InvolutionCentralizers

namespace Theory.SpecificGroups.SymplecticFour.InvolutionCentralizers
open InvolutionTypes
open Representation.OneCohomology.SymplecticFour
variable {F : Type*} [Field F] [CharP F 2]

/-- Nonzero elements of the standard long root have Suzuki type b₁. -/
theorem root0_isB1 {t : F} (ht : t ≠ 0) : IsB1 (rootElement 0 t) :=
  ⟨rootElement_orderOf 0 ht, by rw [movedSpace_root0 ht, finrank_point]⟩

/-- Nonzero elements of the standard short root have Suzuki type a₂. -/
theorem root4_isA2 {t : F} (ht : t ≠ 0) : IsA2 (rootElement 4 t) :=
  ⟨rootElement_orderOf 4 ht, by rw [movedSpace_root4 ht, finrank_plane], root4_orthogonal t⟩

/-- The actual eight matrix root groups have precisely the two root types. -/
theorem rootElement_types (r : Fin 8) {t : F} (ht : t ≠ 0) :
    IsB1 (rootElement r t) ∨ IsA2 (rootElement r t) := by
  obtain ⟨w, hw⟩ := RootNormalizerResidual.exists_root_conjugation (F := F) r
  have hm : rootElement r t ∈ RootSubgroup.group r :=
    (RootSubgroup.mem_group_iff _ _).mpr ⟨t, rfl⟩
  rw [← hw] at hm
  obtain ⟨x, hx, he⟩ := hm
  obtain ⟨s, rfl⟩ := (RootSubgroup.mem_group_iff _ _).mp hx
  change w * rootElement (if r.val < 4 then 0 else 4) s * w⁻¹ = rootElement r t at he
  have hs : s ≠ 0 := by
    intro hs
    rw [hs, RootSubgroup.element_zero, mul_one, mul_inv_cancel] at he
    exact (orderOf_eq_prime_iff.mp (rootElement_orderOf r ht)).2 he.symm
  rw [← he]
  by_cases hr : r.val < 4
  · simp only [hr, if_true]
    exact Or.inl ((isB1_conj_iff w _).mpr (root0_isB1 hs))
  · simp only [hr, if_false]
    exact Or.inr ((isA2_conj_iff w _).mpr (root4_isA2 hs))

/-- Definition E.2.6: root elements are exactly types b₁ and a₂. This direction
of the classification holds over every field of characteristic two. -/
theorem isRootElement_iff (g : Sp F) : IsRootElement g ↔ IsB1 g ∨ IsA2 g := by
  constructor
  · rintro ⟨h, r, t, ht, rfl⟩
    rcases rootElement_types r ht with hb | ha
    · exact Or.inl ((isB1_conj_iff h _).mpr hb)
    · exact Or.inr ((isA2_conj_iff h _).mpr ha)
  · rintro (hb | ha)
    · obtain ⟨h,t,ht,he⟩ := isB1_conjugate_root0 g hb
      exact ⟨h,0,t,ht,he⟩
    · obtain ⟨h,t,ht,he⟩ := isA2_conjugate_root4 g ha
      exact ⟨h,4,t,ht,he⟩
end Theory.SpecificGroups.SymplecticFour.InvolutionCentralizers
