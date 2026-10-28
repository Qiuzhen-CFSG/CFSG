module

public import Theory.Representation.HigherFieldBorelFixedSpaces.Extension
public import Theory.Representation.HigherFieldBorelFixedSpaces.Natural
public import Theory.SpecificGroups.PSL3.HigherFieldBorelResidual

/-!
# Higher-field Borel residuals on natural binary modules

These are the concrete fixed-space calculations for the natural-module
branches of Aschbacher–Smith 13.8.20, combined manuscript (1 March 2004),
printed pp.954–955 (PDF pp.971–972). The groups are actual SL₂(F), SL₃(F),
and (in odd extension degree) PSL₃(F); all module actions and the projective
comparison retain their matrix meaning.

The upper triangular Borel equals its two-residual and has odd index. A
nonidentity diagonal element has no eigenvalue one on each natural module;
the same holds on both the binary dual and the F-linear dual restricted to
the prime field. Tensoring with the actual natural binary S₃-module preserves
vanishing for the Borel in the first factor.

`Extension` passes these calculations through genuine equivariant section
coordinates and handles one or two noncentral layers with central layers by
coset averaging. The FF-module classification and identification of the source
sections remain inputs to the source-theorem owner, as required in 13.8.20.
-/

@[expose] public section

open Matrix Matrix.SpecialLinearGroup Matrix.PSL3.LinearThree
open Representation.BinaryOffender
open scoped MatrixGroups
namespace Representation.HigherFieldBorelFixedSpaces

private lemma four_le_field_card {F : Type*} {n : ℕ}
    (hn : 1 < n) (hF : Nat.card F = 2^n) : 4 ≤ Nat.card F := by
  rw [hF]
  exact Nat.pow_le_pow_right (by decide : 0 < 2) hn

/-- Embed the intrinsic residual of a subgroup back into its ambient group. -/
abbrev twoResidualImage {K : Type*} [Group K] (B : Subgroup K) : Subgroup K :=
  (pResidual 2 B).map B.subtype

private lemma twoResidualImage_eq {K : Type*} [Group K] (B : Subgroup K)
    (h : pResidual 2 B = ⊤) : twoResidualImage B = B := by
  simp only [twoResidualImage, h, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- The actual rank-one Borel is its own embedded two-residual. -/
theorem sl2_twoResidualImage {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2^n) :
    twoResidualImage (rankOneBorel F) = rankOneBorel F :=
  twoResidualImage_eq _ (sl2_borel_residual (four_le_field_card hn hF))

/-- The actual upper triangular SL₃ Borel is its own embedded two-residual. -/
theorem sl3_twoResidualImage {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2^n) :
    twoResidualImage (borelSL F) = borelSL F :=
  twoResidualImage_eq _ (Matrix.PSL3.HigherFieldBorelResidual.borelSL_residual
    (by have := four_le_field_card hn hF; omega))

/-- The actual projective Borel is its own embedded two-residual. -/
theorem psl3_twoResidualImage {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2^n) :
    twoResidualImage (borel F) = borel F :=
  twoResidualImage_eq _ (Matrix.PSL3.HigherFieldBorelResidual.borel_residual
    (by have := four_le_field_card hn hF; omega))

theorem sl2_twoResidual_odd_index {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2^n) :
    Odd (twoResidualImage (rankOneBorel F)).index := by
  rw [sl2_twoResidualImage hn hF]
  exact sl2_borel_odd_index

theorem sl3_twoResidual_odd_index {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2^n) :
    Odd (twoResidualImage (borelSL F)).index := by
  rw [sl3_twoResidualImage hn hF]
  exact sl3_borel_odd_index (by omega) hF

theorem psl3_twoResidual_odd_index {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2^n) :
    Odd (twoResidualImage (borel F)).index := by
  rw [psl3_twoResidualImage hn hF]
  have h := sl3_borel_odd_index (by omega : 0 < n) hF
  rwa [← borel_comap F, (borel F).index_comap_of_surjective
    (Matrix.PSL3.projection_surjective F)] at h

variable [Algebra (ZMod 2) F]

/-- Vanishing on the SL2 natural module and its actual natural S₃ tensor. -/
theorem sl2_twoResidual_natural_fixedSpaces {n : ℕ} (hn : 1 < n)
    (hF : Nat.card F = 2^n) :
    fixedSpace (binaryNatural (F := F) 2) (twoResidualImage (rankOneBorel F)) = ⊥ ∧
    fixedSpace (externalTensor (binaryNatural (F := F) 2)
      (BinaryPermutation.coreRepresentation (Fin 3)))
      ((twoResidualImage (rankOneBorel F)).prod ⊥) = ⊥ := by
  rw [sl2_twoResidualImage hn hF]
  have h := sl2_borel_fixedSpace (F := F) (by have := four_le_field_card hn hF; omega)
  exact ⟨h, naturalS3_tensor_fixedSpace _ _ h⟩

/-- Vanishing on the SL2 binaryDual module and its actual natural S₃ tensor. -/
theorem sl2_twoResidual_binaryDual_fixedSpaces {n : ℕ} (hn : 1 < n)
    (hF : Nat.card F = 2^n) :
    fixedSpace ((binaryNatural (F := F) 2).dual) (twoResidualImage (rankOneBorel F)) = ⊥ ∧
    fixedSpace (V := TensorProduct (ZMod 2) (Module.Dual (ZMod 2) (Fin 2 → F)) (BinaryPermutation.core (Fin 3)))
      (externalTensor ((binaryNatural (F := F) 2).dual)
      (BinaryPermutation.coreRepresentation (Fin 3)))
      ((twoResidualImage (rankOneBorel F)).prod ⊥) = ⊥ := by
  rw [sl2_twoResidualImage hn hF]
  have h := sl2_borel_dual_fixedSpace (F := F) (by have := four_le_field_card hn hF; omega)
  exact ⟨h, naturalS3_tensor_fixedSpace _ _ h⟩

/-- Vanishing on the SL2 fieldDual module and its actual natural S₃ tensor. -/
theorem sl2_twoResidual_fieldDual_fixedSpaces {n : ℕ} (hn : 1 < n)
    (hF : Nat.card F = 2^n) :
    fixedSpace (binaryFieldDual (F := F) 2) (twoResidualImage (rankOneBorel F)) = ⊥ ∧
    fixedSpace (V := TensorProduct (ZMod 2) (Module.Dual F (Fin 2 → F)) (BinaryPermutation.core (Fin 3)))
      (externalTensor (binaryFieldDual (F := F) 2)
      (BinaryPermutation.coreRepresentation (Fin 3)))
      ((twoResidualImage (rankOneBorel F)).prod ⊥) = ⊥ := by
  rw [sl2_twoResidualImage hn hF]
  have h := sl2_borel_fieldDual_fixedSpace (F := F) (by have := four_le_field_card hn hF; omega)
  exact ⟨h, naturalS3_tensor_fixedSpace _ _ h⟩

/-- Vanishing on the SL3 natural module and its actual natural S₃ tensor. -/
theorem sl3_twoResidual_natural_fixedSpaces {n : ℕ} (hn : 1 < n)
    (hF : Nat.card F = 2^n) :
    fixedSpace (binaryNatural (F := F) 3) (twoResidualImage (borelSL F)) = ⊥ ∧
    fixedSpace (externalTensor (binaryNatural (F := F) 3)
      (BinaryPermutation.coreRepresentation (Fin 3)))
      ((twoResidualImage (borelSL F)).prod ⊥) = ⊥ := by
  rw [sl3_twoResidualImage hn hF]
  have h := sl3_borel_fixedSpace (F := F) (by have := four_le_field_card hn hF; omega)
  exact ⟨h, naturalS3_tensor_fixedSpace _ _ h⟩

/-- Vanishing on the SL3 binaryDual module and its actual natural S₃ tensor. -/
theorem sl3_twoResidual_binaryDual_fixedSpaces {n : ℕ} (hn : 1 < n)
    (hF : Nat.card F = 2^n) :
    fixedSpace ((binaryNatural (F := F) 3).dual) (twoResidualImage (borelSL F)) = ⊥ ∧
    fixedSpace (V := TensorProduct (ZMod 2) (Module.Dual (ZMod 2) (Fin 3 → F)) (BinaryPermutation.core (Fin 3)))
      (externalTensor ((binaryNatural (F := F) 3).dual)
      (BinaryPermutation.coreRepresentation (Fin 3)))
      ((twoResidualImage (borelSL F)).prod ⊥) = ⊥ := by
  rw [sl3_twoResidualImage hn hF]
  have h := sl3_borel_dual_fixedSpace (F := F) (by have := four_le_field_card hn hF; omega)
  exact ⟨h, naturalS3_tensor_fixedSpace _ _ h⟩

/-- Vanishing on the SL3 fieldDual module and its actual natural S₃ tensor. -/
theorem sl3_twoResidual_fieldDual_fixedSpaces {n : ℕ} (hn : 1 < n)
    (hF : Nat.card F = 2^n) :
    fixedSpace (binaryFieldDual (F := F) 3) (twoResidualImage (borelSL F)) = ⊥ ∧
    fixedSpace (V := TensorProduct (ZMod 2) (Module.Dual F (Fin 3 → F)) (BinaryPermutation.core (Fin 3)))
      (externalTensor (binaryFieldDual (F := F) 3)
      (BinaryPermutation.coreRepresentation (Fin 3)))
      ((twoResidualImage (borelSL F)).prod ⊥) = ⊥ := by
  rw [sl3_twoResidualImage hn hF]
  have h := sl3_borel_fieldDual_fixedSpace (F := F) (by have := four_le_field_card hn hF; omega)
  exact ⟨h, naturalS3_tensor_fixedSpace _ _ h⟩

/-- Vanishing on the PSL3 natural module and its actual natural S₃ tensor. -/
theorem psl3_twoResidual_natural_fixedSpaces {n : ℕ} (hn : 1 < n) (hodd : Odd n)
    (hF : Nat.card F = 2^n) :
    fixedSpace (projectiveBinaryNatural hodd hF) (twoResidualImage (borel F)) = ⊥ ∧
    fixedSpace (externalTensor (projectiveBinaryNatural hodd hF)
      (BinaryPermutation.coreRepresentation (Fin 3)))
      ((twoResidualImage (borel F)).prod ⊥) = ⊥ := by
  rw [psl3_twoResidualImage hn hF]
  have h := psl3_borel_fixedSpace (F := F) hodd hF (by have := four_le_field_card hn hF; omega)
  exact ⟨h, naturalS3_tensor_fixedSpace _ _ h⟩

/-- Vanishing on the PSL3 binaryDual module and its actual natural S₃ tensor. -/
theorem psl3_twoResidual_binaryDual_fixedSpaces {n : ℕ} (hn : 1 < n) (hodd : Odd n)
    (hF : Nat.card F = 2^n) :
    fixedSpace ((projectiveBinaryNatural hodd hF).dual) (twoResidualImage (borel F)) = ⊥ ∧
    fixedSpace (V := TensorProduct (ZMod 2) (Module.Dual (ZMod 2) (Fin 3 → F)) (BinaryPermutation.core (Fin 3)))
      (externalTensor ((projectiveBinaryNatural hodd hF).dual)
      (BinaryPermutation.coreRepresentation (Fin 3)))
      ((twoResidualImage (borel F)).prod ⊥) = ⊥ := by
  rw [psl3_twoResidualImage hn hF]
  have h := psl3_borel_dual_fixedSpace (F := F) hodd hF (by have := four_le_field_card hn hF; omega)
  exact ⟨h, naturalS3_tensor_fixedSpace _ _ h⟩

/-- Vanishing on the PSL3 fieldDual module and its actual natural S₃ tensor. -/
theorem psl3_twoResidual_fieldDual_fixedSpaces {n : ℕ} (hn : 1 < n) (hodd : Odd n)
    (hF : Nat.card F = 2^n) :
    fixedSpace (projectiveBinaryFieldDual hodd hF) (twoResidualImage (borel F)) = ⊥ ∧
    fixedSpace (V := TensorProduct (ZMod 2) (Module.Dual F (Fin 3 → F)) (BinaryPermutation.core (Fin 3)))
      (externalTensor (projectiveBinaryFieldDual hodd hF)
      (BinaryPermutation.coreRepresentation (Fin 3)))
      ((twoResidualImage (borel F)).prod ⊥) = ⊥ := by
  rw [psl3_twoResidualImage hn hF]
  have h := psl3_borel_fieldDual_fixedSpace (F := F) hodd hF (by have := four_le_field_card hn hF; omega)
  exact ⟨h, naturalS3_tensor_fixedSpace _ _ h⟩

end Representation.HigherFieldBorelFixedSpaces
