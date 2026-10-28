module

public import Theory.SpecificGroups.LieType.TheoremDRootNormalizer.SplitNormalizer
public import Theory.SpecificGroups.LieType.ExceptionalSplit.RootGeneration

/-!
# Simple roots survive the exceptional central quotients in characteristic two

A positive simple root at parameter 1 does not commute with its simple Weyl
word. Indeed the Weyl word conjugates it to the negative root at parameter
-1, and the Cartan/negative-root matrix entry distinguishes these two
matrices over every field. Thus this element survives the literal quotient
by the center of the root-generated group.

Over a finite field of characteristic two, coroot conjugation scales root
parameters by all nonzero squares. Since every element is a square, any
nonzero parameter in the quotient kernel would force parameter 1 into the
kernel. Hence the whole simple root curve is injective, including over GF(2).

The final applications establish nontriviality of the actual positive root
subgroup and remove the q > 2 restriction from the existing projective-root
normalizer's two-locality theorem. No assertion about arbitrary abstract
automorphisms or the Sylow property is made here.

Sources: Steinberg, *Lectures on Chevalley Groups*, Section 3, rank-one Weyl
relations and simple-root generation (`refs/KGroup/GLS3/Chapter2St1.tex`);
GLS3 §§2.1--2.3 for the central quotient. These are matrix inputs to the
characteristic-two Sylow-fixer calculation used in Aschbacher--Smith B.1.13,
printed pp.73--74 of `refs/quasithin.pdf`.
-/

@[expose] public section
noncomputable section
namespace ExceptionalSplit
open RootPairing.IntegralGeckConstruction RootPairing.SimpleGeckGroup
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

private theorem negative_entry (i : b.support) (t : F) :
    let := P.indexNeg
    negativeMatrix i t (Sum.inl i) (Sum.inr (-i : ι)) = 0 := by
  let := P.indexNeg
  simp [negativeMatrix_formula, fDividedPower, Matrix.mul_apply,
    omegaMatrix, eDividedPower, eMatrix, Matrix.one_apply, P.ne_neg i,
    -RootPairing.indexNeg_neg]

/-- The parameter-one simple root is noncentral, including in characteristic two. -/
theorem elementaryRoot_simple_one_not_mem_center (i : b.support) :
    elementaryRoot P b F i 1 ∉ Subgroup.center (rootGenerated P b F) := by
  let := P.indexNeg
  intro hc
  let w : rootGenerated P b F :=
    ⟨rootCurveTitsWord (P := P) (S := F) [i], by
      change rootCurveTitsWord [i] ∈ allRootCurveSubgroup b F
      rw [allRootCurveSubgroup_eq_simpleSubgroup]
      exact rootCurveTitsWord_mem [i]⟩
  have hcomm := Subgroup.mem_center_iff.mp hc w
  have hconj : w * elementaryRoot P b F i 1 * w⁻¹ = elementaryRoot P b F i 1 := by
    rw [hcomm, mul_inv_cancel_right]
  have hm := congrArg (fun x : rootGenerated P b F => x.val.val) hconj
  have hw : w.val.val = specializeMatrix (S := F) (titsLift i) := by
    change specializeMatrix (titsWord [i]) = _
    simp [titsWord]
  have hwi : w.val.inv = specializeMatrix (S := F) (titsLiftInv i) := by
    change specializeMatrix (titsWordInv [i]) = _
    simp [titsWordInv]
  change w.val.val * (elementaryRoot P b F i 1).val.val * w.val.inv =
    (elementaryRoot P b F i 1).val.val at hm
  have he : (elementaryRoot P b F i 1).val.val =
      specializeMatrix (S := F) (eUnipotent i 1) := by
    rw [specialize_e]
    change (rootCurveUnit (integralChevalleyRootOperators (P := P) (b := b)) i (1 : F)).val = _
    rw [rootCurveUnit_simple, positiveUnit_val, Int.cast_one]
  rw [hw, hwi, he, ← specializeMatrix_mul, ← specializeMatrix_mul,
    titsLift_conj_eUnipotent, specialize_f, specialize_e] at hm
  have hentry := congrArg (fun A => A (Sum.inl i) (Sum.inr (-i : ι))) hm
  rw [negative_entry] at hentry
  have hp := TheoremDRootNormalizer.simpleRoot_entry (F := F) i 1
  rw [rootCurveUnit_simple, positiveUnit_val] at hp
  simp only [Int.cast_one] at hentry
  exact zero_ne_one (hentry.trans hp)

/-- The parameter-one simple root survives the actual central quotient over every field. -/
theorem rootElement_simple_one_ne_one (i : b.support) :
    rootElement P b F i 1 ≠ 1 := by
  intro h
  exact elementaryRoot_simple_one_not_mem_center i
    ((projection_eq_one_iff P b F _).mp h)

/-- No nonzero simple-root parameter is killed by the center quotient over a finite binary field. -/
theorem rootElement_simple_eq_one_iff [Finite F] [CharP F 2]
    (i : b.support) (t : F) : rootElement P b F i t = 1 ↔ t = 0 := by
  constructor
  · intro h
    by_contra ht
    have hc := (projection_eq_one_iff P b F (elementaryRoot P b F i t)).mp h
    obtain ⟨a, ha⟩ := FiniteField.isSquare_of_char_two (ringChar.eq F 2) t⁻¹
    have ha0 : a ≠ 0 := by
      intro hz
      apply inv_ne_zero ht
      simpa only [hz, mul_zero] using ha
    let u : Fˣ := Units.mk0 a ha0
    let v := integralChevalleySimpleCorootParameter i u
    let z := TheoremDRootNormalizer.elementaryTorus (P := P) v
    have hscale : (integralChevalleyRootScale (P := P) v i : F) * t = 1 := by
      simp only [v, integralChevalleyRootScale_simpleCorootParameter,
        RootPairing.pairingIn_same, zpow_ofNat, Units.val_pow_eq_pow_val]
      change a ^ 2 * t = 1
      rw [pow_two, ← ha, inv_mul_cancel₀ ht]
    have hcomm := Subgroup.mem_center_iff.mp hc z
    have hfixed : z⁻¹ * elementaryRoot P b F i t * z = elementaryRoot P b F i t := by
      rw [mul_assoc, ← hcomm, inv_mul_cancel_left]
    have hconj := TheoremDRootNormalizer.elementaryTorus_conjugation v (i : ι) t
    rw [hscale] at hconj
    have he : elementaryRoot P b F i t = elementaryRoot P b F i 1 :=
      hfixed.symm.trans hconj
    exact elementaryRoot_simple_one_not_mem_center i (he ▸ hc)
  · rintro rfl
    exact rootElement_zero P b F i

/-- All simple-root parameters remain distinct in the central quotient, with no exclusion of GF(2). -/
theorem rootElement_simple_injective [Finite F] [CharP F 2]
    (i : b.support) : Function.Injective (rootElement P b F i) := by
  intro s t h
  have he : rootElement P b F i (s - t) = 1 := by
    apply mul_right_cancel (b := rootElement P b F i t)
    rw [← rootElement_add, sub_add_cancel, one_mul]
    exact h
  exact sub_eq_zero.mp ((rootElement_simple_eq_one_iff i (s - t)).mp he)

/-- A positive simple root witnesses nontriviality of the full positive root subgroup. -/
theorem positiveRootSubgroup_ne_bot (i : b.support) :
    positiveRootSubgroup (P := P) (b := b) (F := F) ≠ ⊥ := by
  intro h
  have hx := rootElement_mem_positive (F := F) (b.isPos_of_mem_support i.property) 1
  rw [h, Subgroup.mem_bot] at hx
  exact rootElement_simple_one_ne_one i hx

namespace TheoremDRootNormalizer

/-- Apply the uniform injectivity theorem to the existing projective additive-root homomorphism. -/
theorem projectiveRootHom_simple_injective_all [Finite F] [CharP F 2]
    (i : b.support) : Function.Injective (projectiveRootHom (b := b) (F := F) i) := by
  intro x y h
  change rootElement P b F i x.toAdd = rootElement P b F i y.toAdd at h
  exact congrArg Multiplicative.ofAdd (ExceptionalSplit.rootElement_simple_injective (F := F) i h)

/-- The actual simple-root normalizer is two-local over every finite binary field, including GF(2). -/
theorem rootNormalizer_isTwoLocal_all [Finite F] [CharP F 2] (i : b.support) :
    IsTwoLocal (Subgroup.normalizer (rootSubgroup (b := b) (F := F) i : Set (Model P b F))) := by
  refine ⟨rootSubgroup i, ?_, rootSubgroup_isTwoGroup (b := b) (F := F) i, rfl⟩
  intro h
  have hx : rootElement P b F i 1 ∈ rootSubgroup (b := b) (F := F) i :=
    ⟨Multiplicative.ofAdd (1 : F), rfl⟩
  rw [h, Subgroup.mem_bot] at hx
  exact rootElement_simple_one_ne_one i hx

end TheoremDRootNormalizer
end ExceptionalSplit
