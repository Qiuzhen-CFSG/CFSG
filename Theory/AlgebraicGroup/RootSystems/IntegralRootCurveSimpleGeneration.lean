module

public import Theory.AlgebraicGroup.RootSystems.SimpleGeckGroup
public import Theory.AlgebraicGroup.Borel.IntegralChevalleyRootCurves

/-!
# Generation of all integral root curves by simple curves

Each canonical root curve is the conjugate of its signed simple curve by its
chosen integral Tits word. This gives equality of the all-root and simple-root
generated subgroups over every commutative ring, without comparing distinct
routes or discarding their operator signs. Source: GLS3 §§1.12 and 2.1–2.3.
-/

namespace RootPairing.IntegralGeckConstruction
@[expose] public section
noncomputable section

variable {ι R M N : Type*} [Field R] [CharZero R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [P.IsCrystallographic] [P.IsReduced]
  {b : P.Base} [Fintype ι] [DecidableEq ι]
  {S : Type*} [CommRing S]

open SimpleGeckGroup

/-- The chosen integral Tits word as units after scalar extension. -/
def rootCurveTitsWord (word : List b.support) :
    (Matrix (b.support ⊕ ι) (b.support ⊕ ι) S)ˣ where
  val := specializeMatrix (titsWord (P := P) word)
  inv := specializeMatrix (titsWordInv (P := P) word)
  val_inv := by rw [← specializeMatrix_mul, titsWord_mul_inv, specializeMatrix_one]
  inv_val := by rw [← specializeMatrix_mul, titsWord_inv_mul, specializeMatrix_one]

private theorem specialize_eUnipotent (i : b.support) (t : ℤ) :
    specializeMatrix (S := S) (eUnipotent i t) = positiveMatrix i (t : S) := by
  ext j k
  simp only [specializeMatrix, eUnipotent, positiveMatrix_formula, Matrix.map_apply,
    Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Int.coe_castRingHom,
    Int.cast_add, Int.cast_mul, Int.cast_pow]
  simp [Matrix.one_apply]

private theorem specialize_fUnipotent (i : b.support) (t : ℤ) :
    specializeMatrix (S := S) (fUnipotent i t) = negativeMatrix i (t : S) := by
  ext j k
  simp only [specializeMatrix, fUnipotent, negativeMatrix_formula, Matrix.map_apply,
    Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Int.coe_castRingHom,
    Int.cast_add, Int.cast_mul, Int.cast_pow]
  simp [Matrix.one_apply]

@[simp] theorem rootCurveTitsWord_nil :
    rootCurveTitsWord (P := P) (b := b) (S := S) [] = 1 := by
  apply Units.ext
  exact specializeMatrix_one

theorem rootCurveTitsWord_cons (i : b.support) (word : List b.support) :
    rootCurveTitsWord (S := S) (i :: word) =
      positiveUnit i 1 * negativeUnit i (-1) * positiveUnit i 1 *
        rootCurveTitsWord word := by
  apply Units.ext
  change specializeMatrix (titsLift i * titsWord word) = _
  simp [titsLift, specializeMatrix_mul, specialize_eUnipotent,
    specialize_fUnipotent, rootCurveTitsWord]

theorem rootCurveTitsWord_mem (word : List b.support) :
    rootCurveTitsWord (S := S) word ∈ SimpleGeckGroup.subgroup b S := by
  induction word with
  | nil => rw [rootCurveTitsWord_nil]; exact Subgroup.one_mem _
  | cons i word ih =>
    rw [rootCurveTitsWord_cons]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _
      (Subgroup.mul_mem _ (positiveUnit_mem i 1) (negativeUnit_mem i (-1)))
      (positiveUnit_mem i 1)) ih

/-- An exact chosen-route formula; its parameter has no omitted carrier-vector sign. -/
theorem rootCurveUnit_of_pos (r : ι) (hr : b.IsPos r) (t : S) :
    rootCurveUnit (integralChevalleyRootOperators (P := P) (b := b)) r t =
      rootCurveTitsWord (rootRoute (P := P) (b := b) r).word *
        positiveUnit (rootRoute (P := P) (b := b) r).simple t *
        (rootCurveTitsWord (rootRoute (P := P) (b := b) r).word)⁻¹ := by
  apply Units.ext
  change 1 + t • specializeMatrix (rootDividedPower (P := P) (b := b) r 1) +
      t ^ 2 • specializeMatrix (rootDividedPower (P := P) (b := b) r 2) +
      t ^ 3 • specializeMatrix (rootDividedPower (P := P) (b := b) r 3) = _
  rw [rootDividedPower_of_pos r hr, rootDividedPower_of_pos r hr,
    rootDividedPower_of_pos r hr]
  simp only [specializeMatrix_transportedMatrix]
  change _ = specializeMatrix (titsWord (P := P) (rootRoute (P := P) (b := b) r).word) *
    positiveMatrix (rootRoute (P := P) (b := b) r).simple t *
    specializeMatrix (titsWordInv (P := P) (rootRoute (P := P) (b := b) r).word)
  have hTU := (rootCurveTitsWord (S := S) (rootRoute (P := P) (b := b) r).word).val_inv
  simp only [rootCurveTitsWord] at hTU
  simp only [positiveMatrix_formula, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_smul, Matrix.smul_mul, specializeMatrix]
  simp only [specializeMatrix] at hTU
  noncomm_ring [hTU]

/-- The negative route uses the negative simple operator, with the same parameter. -/
theorem rootCurveUnit_of_neg (r : ι) (hr : ¬ b.IsPos r) (t : S) :
    let := P.indexNeg
    rootCurveUnit (integralChevalleyRootOperators (P := P) (b := b)) r t =
      rootCurveTitsWord (rootRoute (P := P) (b := b) (-r)).word *
        negativeUnit (rootRoute (P := P) (b := b) (-r)).simple t *
        (rootCurveTitsWord (rootRoute (P := P) (b := b) (-r)).word)⁻¹ := by
  let := P.indexNeg
  apply Units.ext
  change 1 + t • specializeMatrix (rootDividedPower (P := P) (b := b) r 1) +
      t ^ 2 • specializeMatrix (rootDividedPower (P := P) (b := b) r 2) +
      t ^ 3 • specializeMatrix (rootDividedPower (P := P) (b := b) r 3) = _
  simp only [rootDividedPower, dif_neg hr, specializeMatrix_transportedMatrix]
  change _ = specializeMatrix (titsWord (P := P) (rootRoute (P := P) (b := b) (-r)).word) *
    negativeMatrix (rootRoute (P := P) (b := b) (-r)).simple t *
    specializeMatrix (titsWordInv (P := P) (rootRoute (P := P) (b := b) (-r)).word)
  have hTU := (rootCurveTitsWord (S := S) (rootRoute (P := P) (b := b) (-r)).word).val_inv
  simp only [rootCurveTitsWord] at hTU
  simp only [negativeMatrix_formula, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_smul, Matrix.smul_mul, specializeMatrix]
  simp only [specializeMatrix] at hTU
  noncomm_ring [hTU]

@[simp] theorem rootCurveUnit_simple (i : b.support) (t : S) :
    rootCurveUnit (integralChevalleyRootOperators (P := P) (b := b)) i t =
      positiveUnit i t := by
  rw [rootCurveUnit_of_pos (i : ι) (b.isPos_of_mem_support i.property)]
  simp

@[simp] theorem rootCurveUnit_neg_simple (i : b.support) (t : S) :
    let := P.indexNeg
    rootCurveUnit (integralChevalleyRootOperators (P := P) (b := b)) (-i : ι) t =
      negativeUnit i t := by
  let := P.indexNeg
  apply Units.ext
  change 1 + t • specializeMatrix (rootDividedPower (P := P) (b := b) (-i : ι) 1) +
      t ^ 2 • specializeMatrix (rootDividedPower (P := P) (b := b) (-i : ι) 2) +
      t ^ 3 • specializeMatrix (rootDividedPower (P := P) (b := b) (-i : ι) 3) = _
  simp only [rootDividedPower_neg_of_pos (i : ι) (b.isPos_of_mem_support i.property),
    rootRoute_word_simple, rootRoute_simple, transportedMatrix_nil]
  rfl

/-- The subgroup generated by all canonical integral root curves. -/
def allRootCurveSubgroup (b : P.Base) (S : Type*) [CommRing S] :
    Subgroup (Matrix (b.support ⊕ ι) (b.support ⊕ ι) S)ˣ :=
  Subgroup.closure (Set.range fun p : ι × S =>
    rootCurveUnit (integralChevalleyRootOperators (P := P) (b := b)) p.1 p.2)

theorem rootCurveUnit_mem_simpleSubgroup (r : ι) (t : S) :
    rootCurveUnit (integralChevalleyRootOperators (P := P) (b := b)) r t ∈
      SimpleGeckGroup.subgroup b S := by
  let := P.indexNeg
  by_cases hr : b.IsPos r
  · rw [rootCurveUnit_of_pos r hr]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (rootCurveTitsWord_mem _)
      (positiveUnit_mem _ _)) (Subgroup.inv_mem _ (rootCurveTitsWord_mem _))
  · rw [rootCurveUnit_of_neg r hr]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (rootCurveTitsWord_mem _)
      (negativeUnit_mem _ _)) (Subgroup.inv_mem _ (rootCurveTitsWord_mem _))

/-- All-root generation agrees with generation by the pinned simple curves. -/
theorem allRootCurveSubgroup_eq_simpleSubgroup :
    allRootCurveSubgroup b S = SimpleGeckGroup.subgroup b S := by
  let := P.indexNeg
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨⟨r, t⟩, rfl⟩
    exact rootCurveUnit_mem_simpleSubgroup r t
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨⟨s, i⟩, t, rfl⟩
    cases s
    · change negativeUnit i t ∈ allRootCurveSubgroup b S
      rw [← rootCurveUnit_neg_simple]
      exact Subgroup.subset_closure ⟨((-i : ι), t), rfl⟩
    · change positiveUnit i t ∈ allRootCurveSubgroup b S
      rw [← rootCurveUnit_simple]
      exact Subgroup.subset_closure ⟨((i : ι), t), rfl⟩

end
end
end RootPairing.IntegralGeckConstruction
