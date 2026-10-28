module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.AmbientCount.TwistedKernels.Lattice
public import Theory.AlgebraicGroup.RootSystems.AffinePath

/-!
# Recovering the integral Weyl action from torus characters

Every Weyl element is a word in the numbered simple reflections. Their given
character formulas therefore supply an integral linear pullback on the full
weight lattice. Characters separate weights, so these pullbacks satisfy the
opposite multiplication law and are invertible. Pullback by the inverse Weyl
element gives the required linear representation, with the original Cartan
formulas. This construction uses the actual torus action, without a concrete
D4 algebraic-group carrier or a representation-classification assumption.

Source: Steinberg, `refs/KGroup/GLS3/Chapter2St2.tex`, §§11 and 14.8--14.9.
-/

public noncomputable section
namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ClassBound.AmbientCount
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem D4RestrictedWeight
universe u
variable {k : Type u} [Field k] [CharP k 2]
variable {K : Variety k} [AlgebraicGroup K] {S : Geometry K} {n : ℕ}

private def reflectionLinear (i : Fin 4) : Weight →ₗ[ℤ] Weight where
  toFun := reflection i
  map_add' a b := by
    funext j
    simp only [reflection, Pi.add_apply]
    ring
  map_smul' c a := by
    funext j
    simp only [reflection, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

private lemma weight_eq_of_evaluations (a b : Weight)
    (h : ∀ t : Variety.Point S.torus.carrierVariety,
      (S.weight (Multiplicative.ofAdd a)).pointCharacter t =
        (S.weight (Multiplicative.ofAdd b)).pointCharacter t) : a = b := by
  apply Multiplicative.ofAdd.injective
  apply S.weight.injective
  apply TorusCharacter.pointCharacter_injective
  exact MonoidHom.ext h

private lemma exists_weightPullback (D : TorusData S n) (w : Weyl) :
    ∃ f : Weight →ₗ[ℤ] Weight, letI := D.action
      ∀ a t, (S.weight (Multiplicative.ofAdd a)).pointCharacter (w • t) =
        (S.weight (Multiplicative.ofAdd (f a))).pointCharacter t := by
  let := D.action
  obtain ⟨l, rfl⟩ := (typeDRootPairing_base 2).exists_wordProd_eq w
  induction l with
  | nil => exact ⟨LinearMap.id, by simp⟩
  | cons j l ih =>
    obtain ⟨i, rfl⟩ := (typeDRootPairing_baseEquiv 2).surjective j
    obtain ⟨f, hf⟩ := ih
    refine ⟨f.comp (reflectionLinear i), ?_⟩
    intro a t
    rw [RootPairing.Base.wordProd_cons, mul_smul]
    change (S.weight (Multiplicative.ofAdd a)).pointCharacter
      ((RootPairing.weylGroup.ofIdx (typeDRootPairing 2)
        (typeDSimpleRootIndex 2 i)) • ((typeDRootPairing_base 2).wordProd l • t)) = _
    rw [D.reflection_weight, hf]
    rfl

private def weightPullback (D : TorusData S n) (w : Weyl) : Weight →ₗ[ℤ] Weight :=
  (exists_weightPullback D w).choose

private lemma weightPullback_spec (D : TorusData S n) (w : Weyl) :
    letI := D.action
    ∀ a t, (S.weight (Multiplicative.ofAdd a)).pointCharacter (w • t) =
      (S.weight (Multiplicative.ofAdd (weightPullback D w a))).pointCharacter t :=
  (exists_weightPullback D w).choose_spec

private lemma weightPullback_one (D : TorusData S n) :
    weightPullback D 1 = LinearMap.id := by
  let := D.action
  apply LinearMap.ext
  intro a
  apply weight_eq_of_evaluations (S := S)
  intro t
  simpa using (weightPullback_spec D 1 a t).symm

private lemma weightPullback_mul (D : TorusData S n) (v w : Weyl) :
    weightPullback D (v * w) = (weightPullback D w).comp (weightPullback D v) := by
  let := D.action
  apply LinearMap.ext
  intro a
  apply weight_eq_of_evaluations (S := S)
  intro t
  change (S.weight (Multiplicative.ofAdd (weightPullback D (v * w) a))).pointCharacter t =
    (S.weight (Multiplicative.ofAdd (weightPullback D w (weightPullback D v a)))).pointCharacter t
  rw [← weightPullback_spec, ← weightPullback_spec, ← weightPullback_spec, mul_smul]

private def weightPullbackEquiv (D : TorusData S n) (w : Weyl) : Weight ≃ₗ[ℤ] Weight where
  __ := weightPullback D w⁻¹
  invFun := weightPullback D w
  left_inv a := by
    change (weightPullback D w).comp (weightPullback D w⁻¹) a = a
    rw [← weightPullback_mul, inv_mul_cancel, weightPullback_one]
    rfl
  right_inv a := by
    change (weightPullback D w⁻¹).comp (weightPullback D w) a = a
    rw [← weightPullback_mul, mul_inv_cancel, weightPullback_one]
    rfl

/-- The integral Weyl representation forced by the actual torus action and its
simple-reflection character formulas. -/
def torusWeightRepresentation (D : TorusData S n) : WeightRepresentation where
  toFun := weightPullbackEquiv D
  map_one' := by
    apply LinearEquiv.toLinearMap_injective
    change weightPullback D (1 : Weyl)⁻¹ = LinearMap.id
    rw [inv_one, weightPullback_one]
  map_mul' v w := by
    apply LinearEquiv.toLinearMap_injective
    change weightPullback D (v * w)⁻¹ =
      (weightPullback D v⁻¹).comp (weightPullback D w⁻¹)
    rw [mul_inv_rev, weightPullback_mul]

/-- The recovered action has exactly the specified integral Cartan formulas. -/
theorem torusWeightRepresentation_compatible (D : TorusData S n) :
    ReflectionCompatible (torusWeightRepresentation D) := by
  let := D.action
  intro i a
  change weightPullback D (RootPairing.weylGroup.ofIdx (typeDRootPairing 2)
    (typeDSimpleRootIndex 2 i))⁻¹ a = reflection i a
  have hinv : (RootPairing.weylGroup.ofIdx (typeDRootPairing 2)
      (typeDSimpleRootIndex 2 i))⁻¹ =
        RootPairing.weylGroup.ofIdx (typeDRootPairing 2) (typeDSimpleRootIndex 2 i) :=
    (typeDRootPairing_base 2).simpleReflection_inv (typeDRootPairing_baseEquiv 2 i)
  rw [hinv]
  apply weight_eq_of_evaluations (S := S)
  intro t
  rw [← weightPullback_spec, D.reflection_weight]

end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ClassBound.AmbientCount
