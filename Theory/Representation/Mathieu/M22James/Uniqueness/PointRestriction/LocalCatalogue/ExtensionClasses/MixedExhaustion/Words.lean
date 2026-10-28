module

public import Theory.Representation.Mathieu.M22James.Uniqueness.PointRestriction.LocalCatalogue.ExtensionClasses.MixedExhaustion.Semilinear

/-!
# Three-generator word coordinates for mixed SL₃(4) extensions

The generators are x₀₁(1), x₀₁(ω), and the cyclic coordinate permutation.
The cross block of any word is a linear function of its 27 generator entries.
Section changes telescope along words. Two additional input vectors are the
published symmetric-square and dual-symmetric-square formulas on the generators.
No cocycle law for those formulas is needed here.

This is the finite linear-algebra route to the mixed-extension calculation
used in James (1973), Lemma 8.3; see Aschbacher–Smith H.12.1, pp.393–394.
-/

@[expose] public noncomputable section

open Matrix
namespace Representation.SL3FourLocalCatalogue.ExtensionExhaustion
open SL3FourNaturalDual ExtensionCoordinates
abbrev Mat := Matrix (Fin 3) (Fin 3) F
abbrev Coord := Fin 3 × Fin 3 × Fin 3
abbrev Input := Coord → F

def cycle : SL := ⟨!![0,0,1; 1,0,0; 0,1,0], by simp [Matrix.det_fin_three]⟩
def generator (s : Fin 3) : SL :=
  ![Matrix.SpecialLinearGroup.transvection (by decide : (0 : Fin 3) ≠ 1) 1,
    Matrix.SpecialLinearGroup.transvection (by decide : (0 : Fin 3) ≠ 1) omega,
    cycle] s

def word : List (Fin 3) → SL
  | [] => 1
  | s :: w => generator s * word w

def rightWord : List (Fin 3) → Mat
  | [] => 1
  | s :: w => right (generator s) * rightWord w

lemma right_word (w : List (Fin 3)) : right (word w) = rightWord w := by
  induction w with
  | nil => simp [word, rightWord, right]
  | cons s w ih => simp only [word, rightWord, right_mul, ih]

def slice (s : Fin 3) : Input →ₗ[F] Mat where
  toFun m i j := m (s, i, j)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def wordMap : List (Fin 3) → Input →ₗ[F] Mat
  | [] => 0
  | s :: w => (LinearMap.mulLeft F (generator s).val).comp (wordMap w) +
      (LinearMap.mulRight F (rightWord w)).comp (slice s)

def inputs (c : BlockCocycle .natural .dual) : Input :=
  fun u => coeff c (generator u.1) u.2.1 u.2.2

lemma wordMap_value (c : BlockCocycle .natural .dual) (hc : c.value z = 0)
    (w : List (Fin 3)) : wordMap w (inputs c) = coeff c (word w) := by
  induction w with
  | nil => exact (coeff_one c).symm
  | cons s w ih =>
    change (generator s).val * wordMap w (inputs c) + slice s (inputs c) * rightWord w = _
    rw [word, coeff_mul c hc, ih, right_word]
    rfl

def coboundaryInputs (f : Mat) : Input := fun u =>
  ((generator u.1).val * f + f * right (generator u.1)) u.2.1 u.2.2

def symmetricInputs : Input := fun u => symmetricMatrix (generator u.1) u.2.1 u.2.2
def dualInputs : Input := fun u => dualSymmetricMatrix (generator u.1) u.2.1 u.2.2

def sectionMatrix : (Fin 11 → F) →ₗ[F] Mat where
  toFun v i j := v ⟨2 + 3 * i.val + j.val, by omega⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def modelInputs : (Fin 11 → F) →ₗ[F] Input where
  toFun v := coboundaryInputs (sectionMatrix v) + v 0 • symmetricInputs + v 1 • dualInputs
  map_add' v w := by
    funext u
    simp only [coboundaryInputs, map_add, Matrix.mul_add, Matrix.add_apply,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul]
    abel
  map_smul' r v := by
    funext u
    simp only [coboundaryInputs, map_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.add_apply, mul_add, mul_assoc,
      RingHom.id_apply]

lemma wordMap_coboundary (w : List (Fin 3)) (f : Mat) :
    wordMap w (coboundaryInputs f) = (word w).val * f + f * rightWord w := by
  induction w with
  | nil =>
    change 0 = (1 : Mat) * f + f * 1
    simp only [one_mul, mul_one]
    funext i j
    exact (CharTwo.add_self_eq_zero (f i j)).symm
  | cons s w ih =>
    change (generator s).val * wordMap w (coboundaryInputs f) +
      slice s (coboundaryInputs f) * rightWord w = _
    have hs : slice s (coboundaryInputs f) = (generator s).val * f + f * right (generator s) := rfl
    rw [ih, hs, word, Matrix.SpecialLinearGroup.coe_mul, rightWord]
    simp only [mul_add, add_mul, mul_assoc]
    have hz : (generator s).val * (f * rightWord w) +
        (generator s).val * (f * rightWord w) = 0 := by
      funext i j
      exact CharTwo.add_self_eq_zero _
    linear_combination (norm := abel) hz

lemma wordMap_models (v : Fin 11 → F) (w : List (Fin 3)) :
    wordMap w (modelInputs v) = (word w).val * sectionMatrix v +
      sectionMatrix v * rightWord w +
      v 0 • wordMap w symmetricInputs + v 1 • wordMap w dualInputs := by
  change wordMap w (coboundaryInputs (sectionMatrix v) + v 0 • symmetricInputs +
    v 1 • dualInputs) = _
  rw [map_add, map_add, map_smul, map_smul, wordMap_coboundary]

end Representation.SL3FourLocalCatalogue.ExtensionExhaustion
