module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.AmbientCount.TorusData
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.AmbientCount.TwistedKernels.Lattice
public import Theory.AlgebraicGroup.Tori.Character.IntegralKernel
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.AmbientCount.TwistedKernels.WeightAction
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.AmbientCount.TwistedKernels.DeterminantParity
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.AmbientCount.TwistedKernels.DeterminantAverage
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.AmbientCount.TwistedKernels.DeterminantSign

/-!
# Actual twisted torus kernels in type D4

The full character-lattice equivalence identifies the literal equation
`D.map t = w • t` with annihilation of `2^n δ* - ρ(w⁻¹)`. The integral
representation `ρ` is recovered from the given torus action, using its simple
reflection formulas. Its twisted determinants are odd, so finite abelian
duality gives finite point kernels of exactly the absolute determinant order.
This includes exponent one and does not use an ambient class bound.

The total is first assembled conditionally from two root-system facts:
positivity of these determinants and their signed sum. The D4 determinant
modules discharge those premises, and `kernelTotal_eq` records the resulting
unconditional total for every positive exponent.

Source: Steinberg, `refs/KGroup/GLS3/Chapter2St2.tex`, 14.4, 14.8(a), 14.9.
-/

public noncomputable section
namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ClassBound.AmbientCount
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem D4RestrictedWeight
universe u
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k 2]
variable {K : Variety k} [AlgebraicGroup K] {S : Geometry K} {n : ℕ}

/-- Evaluation against all integral weights identifies the actual torus points. -/
def weightEvaluation (S : Geometry K) :
    Variety.Point S.torus.carrierVariety ≃ (Weight →ₗ[ℤ] Additive kˣ) :=
  torusLatticeEvalEquiv S.maximalTorus.1 S.weight

lemma weightEvaluation_apply (S : Geometry K)
    (t : Variety.Point S.torus.carrierVariety) (a : Weight) :
    ((weightEvaluation S t a).toMul : k) =
      (S.weight (Multiplicative.ofAdd a)).pointCharacter t := by
  exact torusLatticeEvalEquiv_apply S.maximalTorus.1 S.weight t a

omit [IsAlgClosed k] in
/-- The simple-reflection formula determines the action on all characters.
The inverse Weyl element records contravariance of pullback. -/
theorem weyl_weight (D : TorusData S n) (ρ : WeightRepresentation)
    (hρ : ReflectionCompatible ρ) (w : Weyl) (a : Weight)
    (t : Variety.Point S.torus.carrierVariety) :
    letI := D.action
    (S.weight (Multiplicative.ofAdd a)).pointCharacter (w • t) =
      (S.weight (Multiplicative.ofAdd (ρ w⁻¹ a))).pointCharacter t := by
  let := D.action
  obtain ⟨l, rfl⟩ := (typeDRootPairing_base 2).exists_wordProd_eq w
  induction l generalizing a with
  | nil => simp
  | cons j l ih =>
    obtain ⟨i, rfl⟩ := (typeDRootPairing_baseEquiv 2).surjective j
    rw [RootPairing.Base.wordProd_cons, mul_smul]
    change (S.weight (Multiplicative.ofAdd a)).pointCharacter
      ((RootPairing.weylGroup.ofIdx (typeDRootPairing 2)
        (typeDSimpleRootIndex 2 i)) • ((typeDRootPairing_base 2).wordProd l • t)) = _
    rw [D.reflection_weight, ih]
    simp only [mul_inv_rev, RootPairing.Base.simpleReflection_inv, map_mul,
      LinearEquiv.mul_apply]
    change (S.weight (Multiplicative.ofAdd
      (ρ ((typeDRootPairing_base 2).wordProd l)⁻¹ (reflection i a)))).pointCharacter t = _
    rw [show ρ ((typeDRootPairing_base 2).simpleReflection
        (typeDRootPairing_baseEquiv 2 i)) a = reflection i a from hρ i a]

lemma weightEvaluation_map (D : TorusData S n)
    (t : Variety.Point S.torus.carrierVariety) (a : Weight) :
    weightEvaluation S (D.map t) a =
      (2 ^ n : ℕ) • weightEvaluation S t (a ∘ typeD4DiagramPermutation) := by
  apply Additive.toMul.injective
  apply Units.ext
  exact D.map_weight a t

lemma weightEvaluation_weyl (D : TorusData S n) (ρ : WeightRepresentation)
    (hρ : ReflectionCompatible ρ) (w : Weyl)
    (t : Variety.Point S.torus.carrierVariety) (a : Weight) :
    letI := D.action
    weightEvaluation S (w • t) a = weightEvaluation S t (ρ w⁻¹ a) := by
  let := D.action
  apply Additive.toMul.injective
  apply Units.ext
  exact weyl_weight D ρ hρ w a t

/-- The literal equation on torus points is the annihilator of its integral
character endomorphism. -/
def twistedKernelEquivIntegral (D : TorusData S n) (ρ : WeightRepresentation)
    (hρ : ReflectionCompatible ρ) (w : Weyl) :
    TwistedKernel D w ≃
      IntegralCharacterKernel k (twistedWeightMap ρ (2 ^ n) w) := by
  let := D.action
  refine Equiv.subtypeEquiv (weightEvaluation S) (fun t => ?_)
  change D.map t = w • t ↔
    (weightEvaluation S t).comp (twistedWeightMap ρ (2 ^ n) w) = 0
  rw [← (weightEvaluation S).injective.eq_iff, LinearMap.ext_iff, LinearMap.ext_iff]
  apply forall_congr'
  intro a
  simp only [LinearMap.comp_apply, twistedWeightMap_apply, map_sub, map_smul,
    LinearMap.zero_apply, sub_eq_zero]
  rw [weightEvaluation_map, weightEvaluation_weyl D ρ hρ]
  norm_cast

/-- Actual twisted torus kernels are finite and have determinant cardinality,
once the integral determinant and its characteristic coprimality are proved. -/
theorem twistedKernel_finite_card_of_det (D : TorusData S n)
    (ρ : WeightRepresentation) (hρ : ReflectionCompatible ρ) (w : Weyl)
    (hdet : (twistedWeightMap ρ (2 ^ n) w).det ≠ 0)
    (hodd : Odd (twistedWeightMap ρ (2 ^ n) w).det.natAbs) :
    Finite (TwistedKernel D w) ∧ Nat.card (TwistedKernel D w) =
      (twistedWeightMap ρ (2 ^ n) w).det.natAbs := by
  have hchar : ((twistedWeightMap ρ (2 ^ n) w).det.natAbs : k) ≠ 0 := by
    intro hz
    have h := (CharP.cast_eq_zero_iff k 2 _).mp hz
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h)
  obtain ⟨hfin, hcard⟩ := integralCharacterKernel_finite_card (k := k)
    (twistedWeightMap ρ (2 ^ n) w) hdet hchar
  let := hfin
  let E := twistedKernelEquivIntegral D ρ hρ w
  exact ⟨Finite.of_equiv _ E.symm, (Nat.card_congr E).trans hcard⟩


/-- Characteristic two makes every twisted determinant odd. Hence actual kernel
finiteness and the determinant formula hold for any compatible integral action. -/
theorem twistedKernel_finite_card_of_representation (D : TorusData S n) (hn : 0 < n)
    (ρ : WeightRepresentation) (hρ : ReflectionCompatible ρ) (w : Weyl) :
    Finite (TwistedKernel D w) ∧ Nat.card (TwistedKernel D w) =
      (twistedWeightMap ρ (2 ^ n) w).det.natAbs := by
  have hodd := twistedWeightMap_det_odd ρ n hn w
  have hdet : (twistedWeightMap ρ (2 ^ n) w).det ≠ 0 := by
    intro h
    simp [h] at hodd
  exact twistedKernel_finite_card_of_det D ρ hρ w hdet hodd

/-- Every actual twisted kernel is finite, including at exponent one. -/
theorem twistedKernel_finite (D : TorusData S n) (hn : 0 < n) (w : Weyl) :
    Finite (TwistedKernel D w) :=
  (twistedKernel_finite_card_of_representation D hn (torusWeightRepresentation D)
    (torusWeightRepresentation_compatible D) w).1

/-- The order of an actual twisted torus kernel is its integral determinant. -/
theorem twistedKernel_card (D : TorusData S n) (hn : 0 < n) (w : Weyl) :
    Nat.card (TwistedKernel D w) =
      (twistedWeightMap (torusWeightRepresentation D) (2 ^ n) w).det.natAbs := by
  let := twistedKernel_finite D hn w
  exact (twistedKernel_finite_card_of_representation D hn (torusWeightRepresentation D)
    (torusWeightRepresentation_compatible D) w).2

/-- Assembly of the actual kernel total from the two remaining root-system
identities: positivity and the signed determinant sum. These explicit premises
must still be discharged to obtain Steinberg's unconditional total. -/
theorem kernelTotal_eq_of_det_pos_of_det_sum (D : TorusData S n) (hn : 0 < n)
    (ρ : WeightRepresentation) (hρ : ReflectionCompatible ρ)
    (hpos : ∀ w : Weyl, 0 < (twistedWeightMap ρ (2 ^ n) w).det)
    (hsum : (∑ w : Weyl, (twistedWeightMap ρ (2 ^ n) w).det) =
      ((2 : ℤ) ^ n) ^ 4 * (Nat.card Weyl : ℤ)) :
    kernelTotal D = (2 ^ n) ^ 4 * Nat.card Weyl := by
  have hcard (w : Weyl) :=
    (twistedKernel_finite_card_of_representation D hn ρ hρ w).2
  unfold kernelTotal
  simp_rw [hcard]
  apply Nat.cast_injective (R := ℤ)
  push_cast
  simp only [abs_of_pos (hpos _)]
  exact hsum

/-- The actual twisted torus kernels have Steinberg's total order. -/
theorem kernelTotal_eq (D : TorusData S n) (hn : 0 < n) :
    kernelTotal D = (2 ^ n) ^ 4 * Nat.card Weyl := by
  let ρ := torusWeightRepresentation D
  let hρ := torusWeightRepresentation_compatible D
  apply kernelTotal_eq_of_det_pos_of_det_sum D hn ρ hρ
  · intro w
    exact twistedWeightMap_det_pos ρ hρ n hn w
  · exact sum_twistedWeightMap_det ρ hρ ((2 : ℤ) ^ n)

end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ClassBound.AmbientCount
