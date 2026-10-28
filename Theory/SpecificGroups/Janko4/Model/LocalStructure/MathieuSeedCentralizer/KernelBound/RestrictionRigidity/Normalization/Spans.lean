module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.RestrictionRigidity.Normalization.Tables
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Tactic.Abel
/-!
# The exact algebra span and its nonconstant part

Both published 56-element lists are compared with the identity, the ten
actual kernel deviations and the 45 square generators by checked binary
linear combinations. The nonconstant span and the multiplication interface
are used only through these exact comparisons; no basis or algebra assertion
is inferred from the data declarations. Source: `KernelBound/source/README.md`.
-/

@[expose] public section
open scoped BigOperators Matrix
namespace Janko4.LocalStructure.MathieuSeedCentralizer.KernelBound.RestrictionRigidity.NormalizationCertificate
open Coordinates GeneratorCertificates

def radicalSpace : Submodule (ZMod 2) HalfMatrix :=
  Submodule.span (ZMod 2) (Set.range deviation) ⊔ squareSpan

def normalSpace : Submodule (ZMod 2) HalfMatrix :=
  Submodule.span (ZMod 2) {1} ⊔ radicalSpace

lemma deviation_mem (i : Fin 10) : deviation i ∈ radicalSpace :=
  Submodule.mem_sup_left (Submodule.subset_span ⟨i, rfl⟩)

lemma square_mem_radical {X : HalfMatrix} (hX : X ∈ squareSpan) : X ∈ radicalSpace :=
  Submodule.mem_sup_right hX

lemma normalBasis_mem (i : Fin 56) : normalBasis i ∈ normalSpace := by
  by_cases h0 : i.val = 0
  · have hi : i = 0 := Fin.ext h0
    rw [hi, normalBasis_zero]
    exact Submodule.mem_sup_left (Submodule.mem_span_singleton_self _)
  by_cases h10 : i.val < 11
  · have hi : i = ⟨(i.val - 1) + 1, by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hi]
    exact Submodule.mem_sup_right (deviation_mem ⟨i.val - 1, by omega⟩)
  · have hi : i = ⟨(i.val - 11) + 11, by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hi, normalBasis_square ⟨i.val - 11, by omega⟩]
    exact Submodule.mem_sup_right (square_mem_radical (Submodule.subset_span ⟨_, rfl⟩))

lemma concreteAlgebra_le_normalSpace : concreteAlgebra ≤ normalSpace := by
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  change decodeHalf (algebraBasisWords.get i) ∈ _
  rw [← original_coordinates i]
  exact combination_mem _ _ _ normalBasis_mem

lemma normal_span_eq_concrete :
    Submodule.span (ZMod 2) (Set.range normalBasis) = concreteAlgebra := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change decodeHalf (normalWords.get i) ∈ _
    rw [← normal_original_coordinates i]
    exact combination_mem _ _ _ (fun i => Submodule.subset_span ⟨i, rfl⟩)
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change decodeHalf (algebraBasisWords.get i) ∈ _
    rw [← original_coordinates i]
    exact combination_mem _ _ _ (fun i => Submodule.subset_span ⟨i, rfl⟩)

lemma alternative_span_eq_concrete :
    Submodule.span (ZMod 2) (Set.range alternativeBasis) = concreteAlgebra := by
  rw [← normal_span_eq_concrete]
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change decodeHalf (alternativeBasisWords.get i) ∈ _
    rw [← alternative_coordinates i]
    exact combination_mem _ _ _ (fun i => Submodule.subset_span ⟨i, rfl⟩)
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change decodeHalf (normalWords.get i) ∈ _
    rw [← normal_alternative_coordinates i]
    exact combination_mem _ _ _ (fun i => Submodule.subset_span ⟨i, rfl⟩)

lemma exists_normal_coefficients {G : HalfMatrix} (hG : G ∈ concreteAlgebra) :
    ∃ (a : ZMod 2) (v : Fin 10 → ZMod 2) (D : HalfMatrix),
      D ∈ squareSpan ∧ G = a • 1 + (∑ i, v i • deviation i) + D := by
  obtain ⟨A, hA, R, hR, rfl⟩ := Submodule.mem_sup.mp (concreteAlgebra_le_normalSpace hG)
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hA
  obtain ⟨B, hB, D, hD, rfl⟩ := Submodule.mem_sup.mp hR
  obtain ⟨v, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun (ZMod 2)).mp hB
  exact ⟨a, v, D, hD, (add_assoc _ _ _).symm⟩

lemma deviation_mul_radical_of_products
    (h : ∀ (i : Fin 10) (j : Fin 55),
      deviation i * normalBasis ⟨j.val + 1, by omega⟩ ∈ squareSpan)
    (i : Fin 10) {R : HalfMatrix} (hR : R ∈ radicalSpace) : deviation i * R ∈ squareSpan := by
  obtain ⟨B, hB, D, hD, rfl⟩ := Submodule.mem_sup.mp hR
  clear hR
  rw [mul_add]
  apply squareSpan.add_mem
  · induction hB using Submodule.span_induction with
    | mem B hB =>
      obtain ⟨j, rfl⟩ := hB
      exact h i ⟨j.val, by omega⟩
    | zero => simp only [mul_zero]; exact squareSpan.zero_mem
    | add B C _ _ ihB ihC => simpa only [mul_add] using squareSpan.add_mem ihB ihC
    | smul a B _ ih => simpa only [Matrix.mul_smul] using squareSpan.smul_mem a ih
  · induction hD using Submodule.span_induction with
    | mem D hD =>
      obtain ⟨j, rfl⟩ := hD
      have hh := h i ⟨j.val + 10, by omega⟩
      change deviation i * normalBasis ⟨j.val + 11, by omega⟩ ∈ squareSpan at hh
      rw [normalBasis_square] at hh
      exact hh
    | zero => simp only [mul_zero]; exact squareSpan.zero_mem
    | add B C _ _ ihB ihC => simpa only [mul_add] using squareSpan.add_mem ihB ihC
    | smul a B _ ih => simpa only [Matrix.mul_smul] using squareSpan.smul_mem a ih

end Janko4.LocalStructure.MathieuSeedCentralizer.KernelBound.RestrictionRigidity.NormalizationCertificate
