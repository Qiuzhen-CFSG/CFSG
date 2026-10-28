module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.VectorStabilizer.Displacement.Separation.Geometry

/-!
# Rigidity of the self-adjoint displacement space

All 45 directions have image in a certified nine-space. The original exterior
combination 1513 vanishes there, so its pullback has only a linear residue.
Forty-five existing exterior annihilators evaluate that residue; a checked
inverse of their coefficient matrix forces every coefficient to vanish.
The annihilators vanish on all 1221 actual restricted exterior generators.
No identification of an ambient stabilizer or dimension assertion is used.

Source and matrix provenance: source/README.md and ../source/README.md.
Witness regeneration and full-remainder convention: Separation/source/generate.py.
-/

public section
open scoped Matrix
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.VectorStabilizer.Displacement
open OrbitCoverCoordinates OrbitCoverCoordinates.LinearMembership
open GeneratorCertificates LinearMembership.FiniteAlgebra
open PolynomialCertificate
namespace Separation

attribute [local irreducible] selfAdjointWords productWords effectWords weightWords
  evaluationRows recoveryRows selectedWeights testFormRows
  ExteriorAnnihilators.weights

theorem product_decode (k : Fin 45) :
    packedMatrix (productWords.get k) = testForm * selfAdjointBasis k := by
  change packedMatrix (productWords.get k) =
    rectDecode 50 testFormRows * packedMatrix (selfAdjointWords.get k)
  simp only [packedMatrix, ← decode_slices]
  symm
  apply product_eq
  intro i
  simpa only [slices, get_ofFn] using product_checks k i

theorem effect_decode (k : Fin 45) :
    packedMatrix (effectWords.get k) = linearResidue (selfAdjointBasis k) := by
  have h : packedMatrix (effectWords.get k) =
      packedMatrix (productWords.get k) + (packedMatrix (productWords.get k))ᵀ := by
    ext i j
    change bit (effectWords.get k) (j.val+50*i.val) =
      bit (productWords.get k) (j.val+50*i.val) +
      bit (productWords.get k) (i.val+50*j.val)
    simp only [bit, effect_checks]
    cases (productWords.get k).testBit (j.val+50*i.val) <;>
      cases (productWords.get k).testBit (i.val+50*j.val) <;> decide
  rw [h, product_decode, Matrix.transpose_mul, form_symmetric]
  exact add_comm _ _

theorem weight_decode (k : Fin 45) :
    packedMatrix (weightWords.get k) =
      PullbackCoefficients.rowsMatrix (ExteriorAnnihilators.weightRows
        (ExteriorAnnihilators.weights.get (selectedWeights.get k))) := by
  rw [packedMatrix, ← decode_slices]
  ext i j
  simp only [rectDecode, slices, get_ofFn, weight_checks,
    PullbackCoefficients.rowsMatrix, ExteriorAnnihilators.weightRows,
    bit, Nat.testBit_mod_two_pow, j.isLt, decide_true, Bool.true_and]

/-- A previously certified functional on the actual restricted exterior span. -/
@[expose] def separator (i : Fin 45) : RestrictionMatrix →ₗ[ZMod 2] ZMod 2 where
  toFun R := upperValue (ExteriorAnnihilators.weights.get (selectedWeights.get i)) R
  map_add' := upperValue_add _
  map_smul' r R := by simpa only [smul_eq_mul, RingHom.id_apply] using upperValue_smul _ r R

theorem separator_zero (i : Fin 45) {R : RestrictionMatrix}
    (hR : R ∈ restrictionExteriorSpace) : separator i R = 0 :=
  upperValue_zero_of_mem _ (ExteriorAnnihilators.weights_annihilate _) hR

theorem residue_evaluation (i k : Fin 45) :
    separator i (linearResidue (selfAdjointBasis k)) = bit (evaluationRows.get i) k.val := by
  rw [← effect_decode]
  change upperValue _ (packedMatrix _) = _
  rw [← ExteriorAnnihilators.weightRows_spec]
  change pairing (PullbackCoefficients.rowsMatrix _) (packedMatrix _) = _
  rw [← weight_decode, ← packedDot_matrix]
  simp only [bit, evaluation_checks]

/-- The linear residue separates every coefficient in the displayed span. -/
theorem residue_rigidity {X : RestrictionMatrix} (hX : X ∈ selfAdjointSpace)
    (hres : linearResidue X ∈ restrictionExteriorSpace) : X = 0 := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (ZMod 2)).mp hX
  have hz : ∀ i : Fin 45, ev c (evaluationRows.get i) = 0 := by
    intro i
    have he : ev c (evaluationRows.get i) =
        separator i (linearResidue (combination selfAdjointBasis c)) := by
      simp only [combination, LinearMap.coe_mk, AddHom.coe_mk, map_sum, map_smul,
        residue_evaluation, ev, smul_eq_mul]
      apply Finset.sum_congr rfl
      intro k _
      exact mul_comm _ _
    rw [he]
    change separator i (linearResidue (∑ k, c k • selfAdjointBasis k)) = 0
    rw [hc]
    exact separator_zero i hres
  have hc0 : ∀ i, c i = 0 := by
    intro i
    rw [← ev_unit c i, ← recovery_checks i, ev_scan]
    simp only [hz, mul_zero, Finset.sum_const_zero]
  rw [← hc]
  simp only [hc0, zero_smul, Finset.sum_const_zero]

end Separation

/-- Exterior preservation forces zero displacement in the 45-generator space. -/
theorem selfAdjoint_rigidity (X : RestrictionMatrix) (hX : X ∈ selfAdjointSpace)
    (hpres : ∀ R : RestrictionMatrix, R ∈ restrictionExteriorSpace →
      (1 + X)ᵀ * R * (1 + X) ∈ restrictionExteriorSpace) : X = 0 :=
  Separation.residue_rigidity hX (Separation.residue_mem hX hpres)

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.VectorStabilizer.Displacement
