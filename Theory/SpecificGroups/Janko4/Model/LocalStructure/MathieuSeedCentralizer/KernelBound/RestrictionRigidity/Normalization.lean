module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.AmbientConditions
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.RestrictionRigidity.Data
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.RestrictionRigidity.LocalElements
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.RestrictionRigidity.Normalization.Spans
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.RestrictionRigidity.Normalization.Certificates
public import Mathlib.Algebra.CharP.Two
import Mathlib.Tactic.Abel

/-!
# Normalization by actual local-kernel elements

Write a restriction as a linear combination of the identity, the ten actual
kernel deviations `Nᵢ = restriction(eᵢ) - 1`, and the 45 square generators.
The checked coordinate comparisons identify this span with the exact published
`concreteAlgebra` and with the alternative list in `RestrictionRigidity.Data`.
All 550 products `Nᵢ Nⱼ` and `Nᵢ squareBasisⱼ` belong to `squareSpan`.
A common nonzero annihilated vector forces the constant coefficient of an
invertible restriction to be one. Thus no abstract radical or nilpotence
assumption is needed. Multiplying successively by the actual `eᵢ` removes
each binary first-degree coefficient, absorbing every cross term in
`squareSpan`. The inverse of this actual product is the required kernel
normalizer.

Source: `KernelBound/source/README.md` and the literal finite witnesses in
`kernel-restriction.json`; reproduction and conventions are documented in
`Normalization/source/README.md`. This proves normalization only; the separate
restriction-separation argument is assembled in the parent module.
-/

public section
open scoped BigOperators Matrix
namespace Janko4.LocalStructure.MathieuSeedCentralizer.KernelBound.RestrictionRigidity
namespace NormalizationCertificate
open Coordinates GeneratorCertificates

private lemma deviation_mul_radical (i : Fin 10) {R : HalfMatrix} (hR : R ∈ radicalSpace) :
    deviation i * R ∈ squareSpan :=
  deviation_mul_radical_of_products deviation_products i hR

private lemma radical_annihilator {R : HalfMatrix} (hR : R ∈ radicalSpace) : R * annihilator = 0 := by
  obtain ⟨B, hB, D, hD, rfl⟩ := Submodule.mem_sup.mp hR
  clear hR
  rw [add_mul]
  have hB0 : B * annihilator = 0 := by
    induction hB using Submodule.span_induction with
    | mem B hB =>
      obtain ⟨i, rfl⟩ := hB
      exact normalBasis_annihilator ⟨i.val, by omega⟩
    | zero => exact zero_mul _
    | add B C _ _ ihB ihC => rw [add_mul, ihB, ihC, add_zero]
    | smul a B _ ih => rw [Matrix.smul_mul, ih, smul_zero]
  have hD0 : D * annihilator = 0 := by
    induction hD using Submodule.span_induction with
    | mem D hD =>
      obtain ⟨i, rfl⟩ := hD
      have hh := normalBasis_annihilator ⟨i.val + 10, by omega⟩
      change normalBasis ⟨i.val + 11, by omega⟩ * annihilator = 0 at hh
      rw [normalBasis_square] at hh
      exact hh
    | zero => exact zero_mul _
    | add B C _ _ ihB ihC => rw [add_mul, ihB, ihC, add_zero]
    | smul a B _ ih => rw [Matrix.smul_mul, ih, smul_zero]
  rw [hB0, hD0, add_zero]

private lemma binary_scalar (a : ZMod 2) : a = 0 ∨ a = 1 :=
  (by decide +kernel : ∀ a : ZMod 2, a = 0 ∨ a = 1) a

private lemma constant_eq_one {G : HalfMatrix} (hG : IsUnit G)
    (a : ZMod 2) {R : HalfMatrix} (hR : R ∈ radicalSpace)
    (h : G = a • 1 + R) : a = 1 := by
  rcases binary_scalar a with rfl | ha
  · exfalso
    have hz : G * annihilator = 0 := by
      rw [h, zero_smul, zero_add, radical_annihilator hR]
    obtain ⟨u, rfl⟩ := hG
    apply annihilator_ne_zero
    have hh := congrArg (fun X : HalfMatrix => (↑u⁻¹ : HalfMatrix) * X) hz
    simpa only [← mul_assoc, Units.inv_mul, one_mul, mul_zero] using hh
  · exact ha

private lemma sum_deviations_mem {n : ℕ} (idx : Fin n → Fin 10) (v : Fin n → ZMod 2) :
    (∑ i, v i • deviation (idx i)) ∈ radicalSpace :=
  radicalSpace.sum_mem (fun i _ => radicalSpace.smul_mem (v i) (deviation_mem (idx i)))

private lemma normalization_step (N B D : HalfMatrix) :
    (1 + N) * (1 + (N + B) + D) = 1 + B + (D + N * (N + B + D)) := by
  calc
    _ = 1 + B + D + (N + N) + N * (N + B + D) := by
      simp only [mul_add, add_mul, one_mul, mul_one]
      abel
    _ = _ := by
      have hN : N + N = 0 := by ext i j; exact CharTwo.add_self_eq_zero (N i j)
      rw [hN, add_zero, add_assoc]

private lemma normalize_sum (n : ℕ) (idx : Fin n → Fin 10) (v : Fin n → ZMod 2)
    (D : HalfMatrix) (hD : D ∈ squareSpan) :
    ∃ (f : ambientKernel) (E : HalfMatrix), E ∈ squareSpan ∧
      restriction (kernelCentralizerInclusion f) *
        (1 + (∑ i, v i • deviation (idx i)) + D) = 1 + E := by
  induction n generalizing D with
  | zero =>
    refine ⟨1, D, hD, ?_⟩
    simp only [map_one, Fin.sum_univ_zero, add_zero, one_mul]
  | succ n ih =>
    rw [Fin.sum_univ_succ]
    rcases binary_scalar (v 0) with ha | ha
    · rw [ha, zero_smul, zero_add]
      exact ih (fun i => idx i.succ) (fun i => v i.succ) D hD
    · rw [ha, one_smul]
      let B : HalfMatrix := ∑ i : Fin n, v i.succ • deviation (idx i.succ)
      have hB : B ∈ radicalSpace := sum_deviations_mem _ _
      have hR : deviation (idx 0) + B + D ∈ radicalSpace :=
        radicalSpace.add_mem (radicalSpace.add_mem (deviation_mem _) hB) (square_mem_radical hD)
      have hD' : D + deviation (idx 0) * (deviation (idx 0) + B + D) ∈ squareSpan :=
        squareSpan.add_mem hD (deviation_mul_radical _ hR)
      obtain ⟨f, E, hE, hf⟩ := ih (fun i => idx i.succ) (fun i => v i.succ) _ hD'
      refine ⟨f * kernelBasis ⟨(idx 0).val + 1, by omega⟩, E, hE, ?_⟩
      rw [map_mul, map_mul, mul_assoc, restriction_deviation, normalization_step]
      exact hf

end NormalizationCertificate
open Coordinates NormalizationCertificate

/-- Every algebra-valued centralizer restriction can be normalized modulo the
literal square span by an actual element of the known ambient kernel. -/
theorem exists_kernel_normalization (c : SeedCentralizer)
    (hc : restriction c ∈ concreteAlgebra) :
    ∃ (e : ambientKernel) (D : HalfMatrix), D ∈ squareSpan ∧
      restriction ((kernelCentralizerInclusion e)⁻¹ * c) = 1 + D := by
  obtain ⟨a, v, D, hD, hG⟩ := exists_normal_coefficients hc
  have hR : (∑ i, v i • deviation i) + D ∈ radicalSpace :=
    radicalSpace.add_mem (sum_deviations_mem id v) (square_mem_radical hD)
  have ha := constant_eq_one (restriction_isUnit c) a hR (hG.trans (add_assoc _ _ _))
  rw [ha, one_smul] at hG
  obtain ⟨f, E, hE, hf⟩ := normalize_sum 10 id v D hD
  refine ⟨f⁻¹, E, hE, ?_⟩
  rw [map_inv, inv_inv, map_mul, hG]
  exact hf

end Janko4.LocalStructure.MathieuSeedCentralizer.KernelBound.RestrictionRigidity
