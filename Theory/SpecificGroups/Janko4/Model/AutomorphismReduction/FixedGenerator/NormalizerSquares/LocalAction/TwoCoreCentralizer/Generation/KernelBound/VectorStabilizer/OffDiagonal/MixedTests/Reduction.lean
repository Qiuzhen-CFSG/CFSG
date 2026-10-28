module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.VectorStabilizer.OffDiagonal.MixedTests.Data

/-!
# Soundness of the simultaneous mixed-test certificate

The first check identifies each residue as a linear functional annihilating
the actual thirteen-generator span. The second identifies its coefficients
on D. The third supplies a left inverse on all 600 coordinates, proving
completeness of the common zero kernel without a dimension assumption.

The witnesses are full Gaussian remainders as described in
VectorStabilizer/source/README.md; source/generate.py selects coordinates.
-/

set_option maxRecDepth 10000

@[expose] public section
open scoped Matrix
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.VectorStabilizer.OffDiagonal.MixedTestCertificate
open OrbitCoverCoordinates OrbitCoverCoordinates.LinearMembership
open GeneratorCertificates FiniteAlgebra

/-- Inclusion of the two tested entries in the published family. -/
def testIndex (t : Fin 2) : Fin 40 := ⟨t.val, by omega⟩

def PivotChecks : Prop :=
  (∀ k : Fin 13, pivotRadicalWords.get k = radicalWord (pivots.get k)) ∧
  (∀ (t : Fin 2) (k : Fin 13),
    (pivotCoefficientWords t).get k = coefficientWord (testIndex t) (pivots.get k))

def RowChecks (i : Fin 600) : Prop :=
  radicalWord (positions.get i) = scan (corrections.get i) pivotRadicalWords.toList ∧
  equations.get i = coefficientWord (testIndex (testIndices.get i)) (positions.get i) ^^^
    scan (corrections.get i) (pivotCoefficientWords (testIndices.get i)).toList ∧
  scan (recovery.get i) equations.toList = 2 ^ i.val

/-- One coordinate of a full Gaussian remainder, as a linear functional. -/
def residue (p : Position) (c : ℕ) : RestrictionMatrix →ₗ[ZMod 2] ZMod 2 where
  toFun M := M p.1 p.2 + ev (fun k => M (pivots.get k).1 (pivots.get k).2) c
  map_add' M N := by
    simp only [Matrix.add_apply, ev, mul_add, Finset.sum_add_distrib]
    ring
  map_smul' a M := by
    simp only [Matrix.smul_apply, smul_eq_mul, RingHom.id_apply, ev,
      mul_add, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    ring

lemma residue_radical_zero (hp : PivotChecks) (p : Position) (c : ℕ)
    (hc : radicalWord p = scan c pivotRadicalWords.toList) (t : Fin 13) :
    residue p c (radicalKGenerator t) = 0 := by
  have he := congrArg (fun w => bit w t.val) hc
  rw [radicalWord_spec, bit_scan] at he
  simp only [hp.1, radicalWord_spec] at he
  change radicalKGenerator t p.1 p.2 +
    ev (fun k => radicalKGenerator t (pivots.get k).1 (pivots.get k).2) c = 0
  rw [← he, CharTwo.add_self_eq_zero]

lemma residue_span_zero (hp : PivotChecks) (p : Position) (c : ℕ)
    (hc : radicalWord p = scan c pivotRadicalWords.toList)
    (M : RestrictionMatrix) (hM : M ∈ radicalKUpperSpace) : residue p c M = 0 := by
  induction hM using Submodule.span_induction with
  | mem M hM =>
    obtain ⟨t, rfl⟩ := hM
    exact residue_radical_zero hp p c hc t
  | zero => exact map_zero _
  | add M N _ _ hM hN => rw [map_add, hM, hN, add_zero]
  | smul a M _ hM => rw [map_smul, hM, smul_zero]

lemma equation_spec (hp : PivotChecks) (i : Fin 600) (hi : RowChecks i)
    (D : MixedMatrix) :
    ev (flat D) (equations.get i) =
      residue (positions.get i) (corrections.get i)
        (Dᵀ * mixedGenerator (testIndex (testIndices.get i)) +
          (mixedGenerator (testIndex (testIndices.get i)))ᵀ * D) := by
  rw [hi.2.1, ev_xor, coefficientWord_spec, ev_scan]
  change _ = _ + ev _ _
  simp only [hp.2, coefficientWord_spec]
  rfl

/-- Every simultaneous solution vanishes, once the concrete rows are checked. -/
theorem eq_zero_of_checks (hp : PivotChecks) (hr : ∀ i, RowChecks i)
    (D : MixedMatrix)
    (h : ∀ t : Fin 2,
      Dᵀ * mixedGenerator (testIndex t) + (mixedGenerator (testIndex t))ᵀ * D ∈
        radicalKUpperSpace) : D = 0 := by
  have hz (i : Fin 600) : ev (flat D) (equations.get i) = 0 := by
    rw [equation_spec hp i (hr i)]
    exact residue_span_zero hp _ _ (hr i).1 _ (h _)
  have hx (i : Fin 600) : flat D i = 0 := by
    have he := congrArg (ev (flat D)) (hr i).2.2
    rw [ev_scan, ev_unit] at he
    simpa only [hz, mul_zero, Finset.sum_const_zero] using he.symm
  ext i j
  simpa only [flat, Equiv.symm_apply_apply, Matrix.zero_apply] using hx (finProdFinEquiv (i,j))

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.VectorStabilizer.OffDiagonal.MixedTestCertificate
