module

public import Theory.SpecificGroups.LieType.ExceptionalSplit.RootFaithfulness

/-!
# Proper normalizers of the actual exceptional root groups

The simple Weyl word conjugates the positive parameter-one root to the
negative parameter-minus-one root. The latter cannot belong to the positive
root group even after quotienting by the center: such membership would make
the two root elements commute before quotienting, and hence make the Weyl
word commute with the positive root. Its exact conjugation formula and the
Cartan/negative-root matrix entry rule this out.

Consequently the actual positive root group and the cyclic group generated
by its parameter-one element have proper normalizers. In characteristic two
these give proper two-local normalizers, including over the field of order
two. No simplicity or trivial-center assumption is used.

Source: Steinberg, Lectures on Chevalley Groups, Section 3, rank-one Weyl
relations; GLS3 §§2.1–2.3 and §2.6. These are properness inputs for the
exceptional Levi sections in Aschbacher–Smith A.2.18, printed p.40.
-/

public section
noncomputable section

namespace ExceptionalSplit

open RootPairing.IntegralGeckConstruction RootPairing.SimpleGeckGroup
open TheoremDRootNormalizer

variable {ι R M N : Type*} [Field R] [CharZero R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [P.IsCrystallographic] [P.IsReduced]
  {b : P.Base} [Fintype ι] [DecidableEq ι]
  {F : Type*} [Field F]

private theorem specialize_e (i : b.support) (t : ℤ) :
    specializeMatrix (S := F) (eUnipotent i t) = positiveMatrix i (t : F) := by
  ext j k
  simp only [specializeMatrix, eUnipotent, positiveMatrix_formula, Matrix.map_apply,
    Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Int.coe_castRingHom,
    Int.cast_add, Int.cast_mul, Int.cast_pow]
  simp [Matrix.one_apply]

private theorem specialize_f (i : b.support) (t : ℤ) :
    specializeMatrix (S := F) (fUnipotent i t) = negativeMatrix i (t : F) := by
  ext j k
  simp only [specializeMatrix, fUnipotent, negativeMatrix_formula, Matrix.map_apply,
    Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Int.coe_castRingHom,
    Int.cast_add, Int.cast_mul, Int.cast_pow]
  simp [Matrix.one_apply]

private def simpleWeyl (i : b.support) : rootGenerated P b F :=
  ⟨rootCurveTitsWord (P := P) (S := F) [i], by
    change rootCurveTitsWord [i] ∈ allRootCurveSubgroup b F
    rw [allRootCurveSubgroup_eq_simpleSubgroup]
    exact rootCurveTitsWord_mem [i]⟩

private theorem simpleWeyl_factorization (i : b.support) :
    let := P.indexNeg
    simpleWeyl (F := F) i = elementaryRoot P b F i 1 *
      elementaryRoot P b F (-i : ι) (-1) * elementaryRoot P b F i 1 := by
  let := P.indexNeg
  apply Subtype.ext
  change rootCurveTitsWord [i] =
    rootCurveUnit _ (i : ι) (1 : F) * rootCurveUnit _ (-i : ι) (-1) *
      rootCurveUnit _ (i : ι) 1
  rw [rootCurveTitsWord_cons, rootCurveTitsWord_nil, mul_one,
    rootCurveUnit_simple, rootCurveUnit_neg_simple]

private theorem simpleWeyl_conjugation (i : b.support) :
    let := P.indexNeg
    simpleWeyl (F := F) i * elementaryRoot P b F i 1 * (simpleWeyl i)⁻¹ =
      elementaryRoot P b F (-i : ι) (-1) := by
  let := P.indexNeg
  apply Subtype.ext
  apply Units.ext
  change specializeMatrix (titsWord [i]) * (rootCurveUnit _ (i : ι) (1 : F)).val *
    specializeMatrix (titsWordInv [i]) = (rootCurveUnit _ (-i : ι) (-1 : F)).val
  simp only [titsWord, titsWordInv, mul_one, one_mul, rootCurveUnit_simple,
    rootCurveUnit_neg_simple, positiveUnit_val, negativeUnit_val]
  have he := specialize_e (F := F) i 1
  have hf := specialize_f (F := F) i (-1)
  simp only [Int.cast_one, Int.cast_neg] at he hf
  rw [← he, ← hf, ← specializeMatrix_mul, ← specializeMatrix_mul,
    titsLift_conj_eUnipotent]

private theorem negative_simple_ne_positive (i : b.support) :
    let := P.indexNeg
    elementaryRoot P b F (-i : ι) (-1) ≠ elementaryRoot P b F i 1 := by
  let := P.indexNeg
  dsimp only
  intro h
  have he := congrArg (fun x : rootGenerated P b F =>
    x.val.val (Sum.inl i) (Sum.inr (-i : ι))) h
  change (rootCurveUnit _ (-i : ι) (-1 : F)).val _ _ =
    (rootCurveUnit _ (i : ι) (1 : F)).val _ _ at he
  rw [rootCurveUnit_neg_simple, rootCurveUnit_simple, negativeUnit_val,
    positiveUnit_val] at he
  have hn : negativeMatrix i (-1 : F) (Sum.inl i) (Sum.inr (-i : ι)) = 0 := by
    simp [negativeMatrix_formula, fDividedPower, Matrix.mul_apply,
      omegaMatrix, eDividedPower, eMatrix, Matrix.one_apply, P.ne_neg i,
      -RootPairing.indexNeg_neg]
  have hp := TheoremDRootNormalizer.simpleRoot_entry (F := F) i 1
  rw [rootCurveUnit_simple, positiveUnit_val] at hp
  exact zero_ne_one (hn.symm.trans (he.trans hp))

private theorem commute_of_central_quotient_eq {A : Type*} [Group A] {a b c : A}
    (h : QuotientGroup.mk' (Subgroup.center A) a =
      QuotientGroup.mk' (Subgroup.center A) b) (hc : Commute b c) : Commute a c := by
  have hz : a * b⁻¹ ∈ Subgroup.center A := by
    apply (QuotientGroup.eq_one_iff _).mp
    change QuotientGroup.mk' (Subgroup.center A) (a * b⁻¹) = 1
    rw [map_mul, map_inv, h, mul_inv_cancel]
  have hzc : Commute (a * b⁻¹) c := (Subgroup.mem_center_iff.mp hz c).symm
  simpa only [mul_assoc, inv_mul_cancel, mul_one] using hzc.mul_left hc

/-- The negative parameter-minus-one root does not enter the positive simple
root group through the central quotient. This includes fields of order two. -/
theorem rootElement_negative_simple_neg_one_not_mem_rootSubgroup (i : b.support) :
    let := P.indexNeg
    rootElement P b F (-i : ι) (-1) ∉ rootSubgroup (b := b) (F := F) i := by
  let := P.indexNeg
  dsimp only
  rintro ⟨t, ht⟩
  have hproj : projection P b F (elementaryRoot P b F (-i : ι) (-1)) =
      projection P b F (elementaryRoot P b F i t.toAdd) := ht.symm
  have hx : Commute (elementaryRoot P b F i t.toAdd) (elementaryRoot P b F i 1) := by
    change elementaryRoot P b F i t.toAdd * elementaryRoot P b F i 1 = _
    rw [← elementaryRoot_add, ← elementaryRoot_add, add_comm]
  have hy := commute_of_central_quotient_eq hproj hx
  have hw : Commute (simpleWeyl (F := F) i) (elementaryRoot P b F i 1) := by
    rw [simpleWeyl_factorization]
    exact ((Commute.refl _).mul_left hy).mul_left (Commute.refl _)
  apply negative_simple_ne_positive (F := F) i
  calc
    elementaryRoot P b F (-i : ι) (-1) =
        simpleWeyl i * elementaryRoot P b F i 1 * (simpleWeyl i)⁻¹ :=
      (simpleWeyl_conjugation i).symm
    _ = elementaryRoot P b F i 1 := by rw [hw.eq, mul_inv_cancel_right]

private theorem projectiveSimpleWeyl_conjugation (i : b.support) :
    let := P.indexNeg
    projection P b F (simpleWeyl i) * rootElement P b F i 1 *
      (projection P b F (simpleWeyl i))⁻¹ = rootElement P b F (-i : ι) (-1) := by
  dsimp only
  simpa only [map_mul, map_inv, rootElement] using congrArg (projection P b F)
    (simpleWeyl_conjugation (F := F) i)

private theorem normalizer_ne_top_of_root_bounds (i : b.support)
    (U : Subgroup (Model P b F)) (hx : rootElement P b F i 1 ∈ U)
    (hU : U ≤ rootSubgroup (b := b) (F := F) i) :
    Subgroup.normalizer (U : Set (Model P b F)) ≠ ⊤ := by
  let := P.indexNeg
  intro h
  have hw : projection P b F (simpleWeyl i) ∈ Subgroup.normalizer (U : Set _) := by
    rw [h]
    exact Subgroup.mem_top _
  have hy := (Subgroup.mem_normalizer_iff.mp hw _).mp hx
  rw [projectiveSimpleWeyl_conjugation] at hy
  exact rootElement_negative_simple_neg_one_not_mem_rootSubgroup (F := F) i (hU hy)

/-- The parameter-one root is noncentral in the literal projective model. -/
theorem rootElement_simple_one_not_mem_center_model (i : b.support) :
    rootElement P b F i 1 ∉ Subgroup.center (Model P b F) := by
  let := P.indexNeg
  intro h
  have hc := Subgroup.mem_center_iff.mp h (projection P b F (simpleWeyl i))
  have he := projectiveSimpleWeyl_conjugation (F := F) i
  rw [hc, mul_inv_cancel_right] at he
  apply rootElement_negative_simple_neg_one_not_mem_rootSubgroup (F := F) i
  rw [← he]
  exact ⟨Multiplicative.ofAdd 1, rfl⟩

namespace TheoremDRootNormalizer

/-- The actual simple-root normalizer is proper over every field. -/
theorem rootNormalizer_ne_top (i : b.support) :
    Subgroup.normalizer (rootSubgroup (b := b) (F := F) i : Set (Model P b F)) ≠ ⊤ :=
  normalizer_ne_top_of_root_bounds i _ ⟨Multiplicative.ofAdd 1, rfl⟩ le_rfl

/-- The parameter-one cyclic root subgroup also has a proper normalizer. -/
theorem rootElement_zpowers_normalizer_ne_top (i : b.support) :
    Subgroup.normalizer (Subgroup.zpowers (rootElement P b F i 1) : Set (Model P b F)) ≠ ⊤ :=
  normalizer_ne_top_of_root_bounds i _ (Subgroup.mem_zpowers _)
    (Subgroup.zpowers_le.mpr ⟨Multiplicative.ofAdd 1, rfl⟩)

/-- Actual proper two-local geometry for the exceptional Levi-section producer,
including every finite field of characteristic two. -/
theorem rootNormalizer_proper_isTwoLocal [Finite F] [CharP F 2] (i : b.support) :
    Subgroup.normalizer (rootSubgroup (b := b) (F := F) i : Set (Model P b F)) ≠ ⊤ ∧
      IsTwoLocal (Subgroup.normalizer (rootSubgroup (b := b) (F := F) i : Set (Model P b F))) :=
  ⟨rootNormalizer_ne_top i, rootNormalizer_isTwoLocal_all i⟩

end TheoremDRootNormalizer
end ExceptionalSplit
