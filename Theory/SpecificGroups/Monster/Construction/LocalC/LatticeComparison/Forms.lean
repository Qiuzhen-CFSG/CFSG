module
public import Theory.SpecificGroups.Monster.Construction.LocalC.LatticeComparison.Representatives
public import Theory.SpecificGroups.Monster.Construction.TrialitySpin.Structure.QuadraticSpace.Coordinates

/-!
# The quadratic form of the source representatives

Direct integral dot products give the code half-norm `|v|/4`, the even cocode
half-norm `|J|(|J|+1)`, and the mixed pairing
`|v ∩ J| - |J||v|/4`. Reducing them modulo two proves that the explicit
representative map preserves the full source quadratic form, including the
cocode-parity correction.

Source: Aschbacher, *Sporadic Groups*, Lemma 23.10(2–3) and Exercise 8.10,
printed pp. 120–122, and Lemma 27.2, pp. 144–145. The imported Golay
and Leech constructions are the attributed ATLAS ports.
-/

@[expose] public section
noncomputable section
open Atlas.Codes Atlas.Fischer Atlas.Lattices
open scoped BigOperators
namespace Sporadic.Monster.Construction.LocalC
open TrialitySpin

private theorem lift_mul (a b : BinaryWord) :
    (∑ i, golayIntegerLift a i * golayIntegerLift b i) = (overlap a b : ℤ) := by
  rw [overlap_eq_sum, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases ha : a i = 0 <;> by_cases hb : b i = 0 <;> simp [golayIntegerLift, ha, hb]

private theorem code_weight (v : golay) :
    (hammingNorm v.val : ℤ) = 4 * (hammingNorm v.val / 4 : ℕ) := by
  have hd := golay_doublyEven v.val v.prop
  exact_mod_cast (show hammingNorm v.val = 4 * (hammingNorm v.val / 4) by omega)

/-- The source code vector has half-norm `|v|/4`. -/
theorem sourceCodeVector_halfNorm (v : golay) :
    leechHalfNorm (sourceCodeVector v) = (hammingNorm v.val / 4 : ℕ) := by
  have he : integerDot (sourceCodeVector v).val (sourceCodeVector v).val =
      4 * (hammingNorm v.val : ℤ) := by
    rw [← integerDot_lift_self]
    simp only [integerDot, sourceCodeVector_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hn := leechHalfNorm_mul (sourceCodeVector v)
  rw [he, code_weight] at hn
  omega

/-- The source cocode vector has even half-norm `|J|(|J|+1)`. -/
theorem sourceCocodeVector_halfNorm (J : BinaryWord) :
    leechHalfNorm (sourceCocodeVector J) = (hammingNorm J : ℤ) * (hammingNorm J + 1) := by
  have he : integerDot (sourceCocodeVector J).val (sourceCocodeVector J).val =
      16 * ((hammingNorm J : ℤ) * (hammingNorm J + 1)) := by
    simp only [integerDot, sourceCocodeVector_apply]
    calc
      _ = ∑ i, (16 * (golayIntegerLift J i * golayIntegerLift J i) -
          8 * (hammingNorm J : ℤ) * golayIntegerLift J i + (hammingNorm J : ℤ)^2) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
          ← Finset.mul_sum]
        change 16 * integerDot (golayIntegerLift J) (golayIntegerLift J) -
          8 * (hammingNorm J : ℤ) * (∑ i, golayIntegerLift J i) +
          ∑ _ : Omega, (hammingNorm J : ℤ)^2 = _
        rw [integerDot_lift_self, sum_golayIntegerLift]
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
          nsmul_eq_mul]
        ring
  have hn := leechHalfNorm_mul (sourceCocodeVector J)
  rw [he] at hn
  omega

/-- The mixed integral pairing is the overlap minus the weight correction. -/
theorem sourceCodeVector_pairing_cocode (v : golay) (J : BinaryWord) :
    leechIntegralPairing (sourceCodeVector v) (sourceCocodeVector J) =
      (overlap v.val J : ℤ) - (hammingNorm J : ℤ) * (hammingNorm v.val / 4 : ℕ) := by
  have he : integerDot (sourceCodeVector v).val (sourceCocodeVector J).val =
      8 * (overlap v.val J : ℤ) - 2 * (hammingNorm J : ℤ) * hammingNorm v.val := by
    simp only [integerDot, sourceCodeVector_apply, sourceCocodeVector_apply]
    calc
      _ = ∑ i, (8 * (golayIntegerLift v.val i * golayIntegerLift J i) -
          2 * (hammingNorm J : ℤ) * golayIntegerLift v.val i) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := by rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
        lift_mul, sum_golayIntegerLift]
  have hn := leechIntegralPairing_mul (sourceCodeVector v) (sourceCocodeVector J)
  rw [he, code_weight] at hn
  nlinarith

/-- The cocode parity is the parity of a representative's support. -/
theorem sourceCocodeParity_mk (J : BinaryWord) :
    cocodeParity (Submodule.Quotient.mk J) = (hammingNorm J : Bit) := by
  change cocodeDualEquiv (Submodule.Quotient.mk J) golayOne = _
  rw [cocodeDualEquiv_mk, binaryDot_overlap]
  congr 1
  simp [overlap, hammingNorm, golayOne, allOnes]

theorem sourceCocodePairing_mk (v : golay) (J : BinaryWord) :
    cocodePairing v (Submodule.Quotient.mk J) = (overlap v.val J : Bit) := by
  rw [cocodePairing, cocodeDualEquiv_mk, binaryDot_overlap]

/-- The cocode classes form a totally singular subspace of the actual Leech quotient. -/
theorem sourceCocodeClass_quadratic (c : Cocode) : leechQuadratic (sourceCocodeClass c) = 0 := by
  obtain ⟨J, rfl⟩ := Submodule.Quotient.mk_surjective golay c
  rw [sourceCocodeClass_mk, leechQuadratic_reduce, sourceCocodeVector_halfNorm]
  push_cast
  rcases bit_cases (hammingNorm J : Bit) with h | h <;> simp [h]

theorem sourceCodeClass_quadratic (v : golay) :
    leechQuadratic (leechReduction (sourceCodeVector v)) = golayQuarterWeight v := by
  rw [leechQuadratic_reduce, sourceCodeVector_halfNorm]
  rfl

theorem sourceCodeCocode_polar (v : golay) (c : Cocode) :
    leechPolar (leechReduction (sourceCodeVector v)) (sourceCocodeClass c) =
      cocodePairing v c + cocodeParity c * golayQuarterWeight v := by
  obtain ⟨J, rfl⟩ := Submodule.Quotient.mk_surjective golay c
  rw [sourceCocodeClass_mk, leechPolar_reduce, sourceCodeVector_pairing_cocode,
    sourceCocodePairing_mk, sourceCocodeParity_mk]
  unfold golayQuarterWeight
  push_cast
  rw [sub_eq_add_neg, CharTwo.neg_eq]
  norm_cast

/-- The prescribed map preserves the source square form, including odd cocode parity. -/
theorem sourceCoordinateMap_quadratic (x : QuadraticCoordinates) :
    leechQuadratic (sourceCoordinateMap x) = coordinateQuadratic x := by
  rw [sourceCoordinateMap, leechQuadratic_add, sourceCodeClass_quadratic,
    sourceCocodeClass_quadratic, sourceCodeCocode_polar]
  unfold coordinateQuadratic
  ring

end Sporadic.Monster.Construction.LocalC
