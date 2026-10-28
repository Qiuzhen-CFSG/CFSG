module

public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Threes.FusionCertificates.Evaluations
public import Mathlib.Tactic.FinCases

/-!
# Ambient fusion of the two local J4 order-three words

Both local words are conjugate to the designated representative in the actual
matrix-generated carrier. The conjugators are straight-line group expressions
in the original generators. An untrusted search found them by matching
involutions centralizing the order-three words, then matching conjugates inside
an involution centralizer. No assertion about these centralizers is needed here:
683 kernel-checked packed products verify the resulting words and the two
intertwining identities directly.

The local program `J4G1-max10W1` and the designated word are from the ATLAS,
by R. A. Wilson, S. J. Nickerson and J. N. Bray:
https://brauer.maths.qmul.ac.uk/Atlas/v3/spor/J4/ . Their literal definitions and
attribution are in `Threes.LocalModel` and `Simplicity.Words`; the source matrices
are documented in `Model.Data`. The search supplies witnesses, not assumptions
about simplicity, recognition, class counts, or the order of a local subgroup.
-/

public section
namespace Janko4.Simplicity
open Janko4.GeneratorCertificates ThreeFusion

private theorem localU_eq (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    threeLocalU hA hB = w27 (a hA) (b hB) := by
  have hx : w20 (a hA) (b hB) = (threeLocalProgram (a hA) (b hB)).1 := rfl
  have hy : w13 (a hA) (b hB) = (threeLocalProgram (a hA) (b hB)).2 := rfl
  simp only [w27, w26, w25, w24, w23, w22, w21, hx, hy]
  simp [threeLocalU, word, mul_assoc]

private theorem localV_eq (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    threeLocalV hA hB = w37 (a hA) (b hB) := by
  have hx : w20 (a hA) (b hB) = (threeLocalProgram (a hA) (b hB)).1 := rfl
  have hy : w13 (a hA) (b hB) = (threeLocalProgram (a hA) (b hB)).2 := rfl
  simp only [w37, w36, w35, w34, w33, w32, w31, w30, w29, w28, w21, hx, hy]
  simp [threeLocalV, word, mul_assoc]

private theorem localZ_eq (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    threeLocalZ hA hB = w42 (a hA) (b hB) := by
  simp only [threeLocalZ, w42, w41, w40, w38, w39, localU_eq, localV_eq]

private theorem representative_eq
    (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    primeRepresentative (a hA) (b hB) 2 = w51 (a hA) (b hB) := by
  simp [primeRepresentative, w51, w50, w49, w48, w47, w46, w45, w44, w43,
    w2, w0, w1, word, mul_assoc]

/-- The noncentral local word is conjugate to the designated representative. -/
theorem threeLocalU_fusion
    (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    ∃ g : Model, primeRepresentative (a hA) (b hB) 2 =
      g * threeLocalU hA hB * g⁻¹ := by
  let c := w556 (a hA) (b hB)
  have h : threeLocalU hA hB * c = c * primeRepresentative (a hA) (b hB) 2 := by
    apply toMatrix_injective
    simp only [c, map_mul, localU_eq, representative_eq, eval27, eval556, eval51]
    rw [← decode_packedMul, ← decode_packedMul, p679, p680]
  refine ⟨c⁻¹, ?_⟩
  simp only [inv_inv]
  calc
    primeRepresentative (a hA) (b hB) 2 =
        c⁻¹ * (c * primeRepresentative (a hA) (b hB) 2) := by simp
    _ = c⁻¹ * (threeLocalU hA hB * c) := congrArg (c⁻¹ * ·) h.symm
    _ = c⁻¹ * threeLocalU hA hB * c := (mul_assoc _ _ _).symm

/-- The central local word is conjugate to the designated representative. -/
theorem threeLocalZ_fusion
    (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    ∃ g : Model, primeRepresentative (a hA) (b hB) 2 =
      g * threeLocalZ hA hB * g⁻¹ := by
  let c := w584 (a hA) (b hB)
  have h : threeLocalZ hA hB * c = c * primeRepresentative (a hA) (b hB) 2 := by
    apply toMatrix_injective
    simp only [c, map_mul, localZ_eq, representative_eq, eval42, eval584, eval51]
    rw [← decode_packedMul, ← decode_packedMul, p681, p682]
  refine ⟨c⁻¹, ?_⟩
  simp only [inv_inv]
  calc
    primeRepresentative (a hA) (b hB) 2 =
        c⁻¹ * (c * primeRepresentative (a hA) (b hB) 2) := by simp
    _ = c⁻¹ * (threeLocalZ hA hB * c) := congrArg (c⁻¹ * ·) h.symm
    _ = c⁻¹ * threeLocalZ hA hB * c := (mul_assoc _ _ _).symm

/-- The two concrete fusion witnesses required for local order-three coverage. -/
theorem threeLocalRepresentative_fusion
    (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    ∀ i : Fin 2, ∃ (k : ℕ) (g : Model),
      primeRepresentative (a hA) (b hB) 2 =
        g * threeLocalRepresentative hA hB i ^ k * g⁻¹ := by
  intro i
  fin_cases i
  · obtain ⟨g, hg⟩ := threeLocalU_fusion hA hB
    exact ⟨1, g, by simpa [threeLocalRepresentative] using hg⟩
  · obtain ⟨g, hg⟩ := threeLocalZ_fusion hA hB
    exact ⟨1, g, by simpa [threeLocalRepresentative] using hg⟩

end Janko4.Simplicity
