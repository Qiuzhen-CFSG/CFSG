module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.FiniteRootAction.RootCurves.Degrees
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.BasicMinimum.EndNode.Weights

/-!
# Integral degree of a full F4 coroot weight

The inverse Cartan matrix converts the root degree `(2,2,1,1)` into the
integral functional `(16,30,21,11)` on full coroot weight coordinates.
Its value on the actual weight of any native root equals the previously
proved Euclidean degree. No division or characteristic-dependent eigenvalue
argument enters this comparison.

Source: the F4 Cartan pairing and the grading in Steinberg (1963), Section 12.
-/

public section
noncomputable section
namespace ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.FiniteRootAction

open Theory.AlgebraicGroup StandardRootSystem
open EndNode

/-- Integral degree on all four coroot weight coordinates. -/
@[expose] def weightDegree (μ : Weight) : ℤ :=
  16 * μ 0 + 30 * μ 1 + 21 * μ 2 + 11 * μ 3

/-- The full simple-coroot weight of an actual native root. -/
@[expose] def rootWeight (r : F4Chevalley.Root) : Weight :=
  fun j => typeF4RootPairing.pairingIn ℤ r (typeF4SimpleRootIndex j)

theorem weightDegree_add (μ ν : Weight) :
    weightDegree (μ + ν) = weightDegree μ + weightDegree ν := by
  simp only [weightDegree, Pi.add_apply]
  ring

theorem weightDegree_sub (μ ν : Weight) :
    weightDegree (μ - ν) = weightDegree μ - weightDegree ν := by
  simp only [weightDegree, Pi.sub_apply]
  ring

theorem weightDegree_nsmul (n : ℕ) (μ : Weight) :
    weightDegree (n • μ) = (n : ℤ) * weightDegree μ := by
  simp only [weightDegree, Pi.smul_apply, nsmul_eq_mul]
  ring

/-- The integer degree agrees with the geometric degree on every native root. -/
theorem weightDegree_rootWeight (r : F4Chevalley.Root) :
    (weightDegree (rootWeight r) : ℝ) = RootCurves.rootDegree r := by
  have hc (j : Fin 4) : (rootWeight r j : ℝ) =
      (if j.val < 2 then 1 else 2) * dot r.val (typeF4SimpleRoot j) := by
    change algebraMap ℤ ℝ (rootWeight r j) = _
    rw [rootWeight, typeF4RootPairing.algebraMap_pairingIn]
    simp only [typeF4RootPairing_pairing,
      typeF4CorootScale_simpleRoot, typeF4SimpleRootIndex_val]
  simp only [weightDegree, Int.cast_add, Int.cast_mul, Int.cast_ofNat, hc,
    RootCurves.rootDegree, RootCurves.degree]
  norm_num [dot, Fin.sum_univ_four, typeF4SimpleRoot,
    Matrix.cons_val_two, Matrix.cons_val_three]
  ring

/-- Every native positive root has strictly positive integer degree. -/
theorem weightDegree_rootWeight_pos {r : F4Chevalley.Root}
    (hr : typeF4RootPairing_base.IsPos r) : 0 < weightDegree (rootWeight r) := by
  have h := RootCurves.rootDegree_pos hr
  rw [← weightDegree_rootWeight] at h
  exact_mod_cast h

end ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.FiniteRootAction
