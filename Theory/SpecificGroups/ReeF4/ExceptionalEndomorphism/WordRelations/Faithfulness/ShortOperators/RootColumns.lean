module

public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.WordRelations.Faithfulness.ShortOperators.Geometry

/-!
# Root columns of the actual F4 operators in characteristic two

Integral Tits transport sends a root basis vector to itself up to an integral
sign. Such signs disappear in characteristic two, so the signed integral
bracket formulas give exact coordinate formulas: the column at a root is the
root-string coefficient times the sum-root vector, or zero when the sum is
absent and the roots are not opposite.

These formulas concern the canonical operators of
`F4IntegralChevalleyRepresentation`, using the signed bracket theorems of
`IntegralChevalleyBrackets` (Geck's integral construction and Steinberg's
*Lectures on Chevalley Groups*).
-/

public section

open Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction
open scoped Matrix

namespace ReeF4.WordRelations.ShortOperators
variable {K : Type*} [CommRing K] [CharP K 2]

private lemma sign_cast_one {z : ℤ} (hz : z * z = 1) : (z : K) = 1 := by
  rcases mul_self_eq_one_iff.mp hz with h | h
  · simp [h]
  · simp [h, CharTwo.neg_eq]

lemma rootVector_cast (s : typeF4Roots) :
    (Int.castRingHom K) ∘ rootVector
      (P := typeF4RootPairing) (b := typeF4RootPairing_base) s =
      Pi.single (Sum.inr s : Coordinate) 1 := by
  classical
  obtain ⟨z, hz, hs⟩ := exists_rootVector_sign
    (P := typeF4RootPairing) (b := typeF4RootPairing_base) s
  rw [hs]
  ext i
  change ((z * v (b := typeF4RootPairing_base) s i : ℤ) : K) = _
  rw [Int.cast_mul, sign_cast_one hz, one_mul]
  by_cases hi : i = Sum.inr s <;> simp [v, hi]

omit [CharP K 2] in
private lemma cast_smul (z : ℤ) (v : Coordinate → ℤ) :
    (Int.castRingHom K) ∘ (z • v) = (z : K) • ((Int.castRingHom K) ∘ v) := by
  ext i
  simp

omit [CharP K 2] in
private lemma cast_mulVec (A : Matrix Coordinate Coordinate ℤ) (v : Coordinate → ℤ) :
    (Int.castRingHom K) ∘ (A *ᵥ v) = A.map (Int.castRingHom K) *ᵥ ((Int.castRingHom K) ∘ v) := by
  ext i
  exact (Int.castRingHom K).map_mulVec A v i

/-- The non-opposite root columns have their root-string coefficient with
no sign after specialization in characteristic two. -/
lemma rootOperator_rootColumn_add (s j k : typeF4Roots)
    (h : typeF4RootPairing.root k = typeF4RootPairing.root s + typeF4RootPairing.root j) :
    (Theory.AlgebraicGroup.F4Chevalley.integralOperators.rootOperator s).map
        (Int.castRingHom K) *ᵥ Pi.single (Sum.inr j : Coordinate) 1 =
      (typeF4RootPairing.chainBotCoeff s j + 1 : K) •
        Pi.single (Sum.inr k : Coordinate) 1 := by
  change (rootOperator (P := typeF4RootPairing) (b := typeF4RootPairing_base) s).map
    (Int.castRingHom K) *ᵥ Pi.single (Sum.inr j : Coordinate) 1 = _
  obtain ⟨z, hz, he⟩ := rootOperator_mulVec_root_add_signed
    (P := typeF4RootPairing) (b := typeF4RootPairing_base) h
  have hm := congrArg (fun v : Coordinate → ℤ => (Int.castRingHom K) ∘ v) he
  rw [cast_mulVec, rootVector_cast, cast_smul, rootVector_cast] at hm
  simpa only [Int.cast_mul, sign_cast_one hz, one_mul, Int.cast_add,
    Int.cast_natCast, Int.cast_one] using hm

/-- A root column vanishes when its sum with the acting root is neither a root
nor zero. -/
lemma rootOperator_rootColumn_zero (s j : typeF4Roots)
    (hopp : letI := typeF4RootPairing.indexNeg; j ≠ -s)
    (h : typeF4RootPairing.root s + typeF4RootPairing.root j ∉
      Set.range typeF4RootPairing.root) :
    (Theory.AlgebraicGroup.F4Chevalley.integralOperators.rootOperator s).map
        (Int.castRingHom K) *ᵥ Pi.single (Sum.inr j : Coordinate) 1 = 0 := by
  change (rootOperator (P := typeF4RootPairing) (b := typeF4RootPairing_base) s).map
    (Int.castRingHom K) *ᵥ Pi.single (Sum.inr j : Coordinate) 1 = _
  have he := rootOperator_mulVec_root_eq_zero
    (P := typeF4RootPairing) (b := typeF4RootPairing_base) hopp h
  have hm := congrArg (fun v : Coordinate → ℤ => (Int.castRingHom K) ∘ v) he
  rw [cast_mulVec, rootVector_cast] at hm
  ext i
  have hi := congrFun hm i
  simpa only [Function.comp_apply, Pi.zero_apply, map_zero] using hi
end ReeF4.WordRelations.ShortOperators
