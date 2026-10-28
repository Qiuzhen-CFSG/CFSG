module

public import Theory.Representation.SL2.BinarySmallModels
public import Theory.Representation.SL2.HighestWeightSpan
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.Algebra.CharP.Lemmas

/-!
# Pure binary highest weights and the natural module

The map `(a,b) ↦ a X₀^(2^j) + b X₁^(2^j)` intertwines the Frobenius-twisted
natural action with the polynomial action. Evaluation at `(1,0)` and `(0,1)`
proves injectivity. Both pure powers belong to the highest-weight orbit span,
and the characteristic-two power identity puts every orbit vector in the image.
This constructs the actual representation equivalence for every `j`.

The coordinate maps also identify scalar extension of the natural action and
transport its prime-field restriction along an actual field isomorphism.

Source: GLS volume 3, §§2.8.6, 2.8.10(b); Aschbacher--Smith, G.9.3(6),
combined manuscript (1 March 2004), printed p.354.
-/

public section

open scoped MatrixGroups MonoidAlgebra TensorProduct
namespace Representation.SL2.BinarySmall
noncomputable section

variable {K E F : Type*} [Field K] [Field E] [Field F]

/-- The natural column action with coefficients mapped by the specified embedding. -/
@[expose] def embeddedNatural (e : K →+* E) : Representation E SL(2,K) (Fin 2 → E) :=
  (specialLinearNatural 2).comp (Matrix.SpecialLinearGroup.map e)

/-- Tensor scalar extension agrees with entrywise extension of the natural matrices. -/
def embeddedNaturalBaseChange [Algebra E F] (e : K →+* E) :
    (extendScalars F (embeddedNatural e)).Equiv
      (embeddedNatural ((algebraMap E F).comp e)) := by
  refine Representation.Equiv.mk (TensorProduct.piScalarRight E F F (Fin 2)) (fun g => ?_)
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
  | tmul a v =>
    ext i
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, extendScalars_apply, LinearMap.baseChange_tmul,
      TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul]
    simp only [Algebra.smul_def]
    change algebraMap E F ((Matrix.mulVec (g.val.map e) v) i) * a =
      Matrix.mulVec (g.val.map ((algebraMap E F).comp e))
        (fun j => algebraMap E F (v j) * a) i
    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, RingHom.comp_apply,
      Matrix.map_apply, Finset.sum_mul, mul_assoc]

variable [CharP K 2] [Algebra (ZMod 2) E]
local instance naturalComparisonBinaryAlgebra : Algebra (ZMod 2) K := ZMod.algebra K 2

/-- A field identification intertwines the actual natural actions over the prime field. -/
def naturalFieldEquiv [Finite K] (e : K ≃+* E) :
    (natural (K := K)).Equiv (restrictScalars (k := ZMod 2) (embeddedNatural e.toRingHom)) := by
  let c : K ≃ₗ[ZMod 2] E := LinearEquiv.ofBijective
    (e.toAddEquiv.toAddMonoidHom.toZModLinearMap 2) e.bijective
  refine Representation.Equiv.mk (LinearEquiv.piCongrRight (fun _ : Fin 2 => c)) (fun g => ?_)
  apply LinearMap.ext
  intro v
  ext i
  change e (Matrix.mulVec g.val v i) = Matrix.mulVec (g.val.map e) (fun j => e (v j)) i
  simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply]


end
end Representation.SL2.BinarySmall

namespace Representation.SL2.BinarySmall
noncomputable section
variable {K F : Type*} [Field K] [Field F]
open MvPolynomial
variable [CharP F 2]

private def purePowerMap (j : ℕ) : (Fin 2 → F) →ₗ[F] MvPolynomial (Fin 2) F where
  toFun v := v 0 • X 0 ^ (2 ^ j) + v 1 • X 1 ^ (2 ^ j)
  map_add' v w := by simp [add_smul]; abel
  map_smul' a v := by simp [mul_smul, smul_add]

omit [CharP F 2] in
private theorem purePowerMap_injective (j : ℕ) : Function.Injective (purePowerMap (F := F) j) := by
  intro v w h
  have h0 := congrArg (MvPolynomial.eval (![1, 0] : Fin 2 → F)) h
  have h1 := congrArg (MvPolynomial.eval (![0, 1] : Fin 2 → F)) h
  simp [purePowerMap, Algebra.smul_def] at h0 h1
  ext i
  fin_cases i
  · exact h0
  · exact h1

private theorem purePowerMap_action (e : K →+* F) (j : ℕ) (g : SL(2,K)) (v : Fin 2 → F) :
    polynomialAction F (Matrix.SpecialLinearGroup.map e g) (purePowerMap j v) =
      purePowerMap j (embeddedNatural ((iterateFrobenius F 2 j).comp e) g v) := by
  simp only [purePowerMap, LinearMap.coe_mk, AddHom.coe_mk, map_add, map_smul, map_pow]
  simp only [polynomialAction, MvPolynomial.aeval_X, Fin.sum_univ_two,
    Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply]
  rw [add_pow_char_pow, add_pow_char_pow]
  simp only [mul_pow, ← map_pow]
  simp [embeddedNatural, specialLinearNatural_apply, Matrix.mulVec, dotProduct,
    Fin.sum_univ_two, iterateFrobenius_def, Algebra.smul_def]
  ring

omit [CharP F 2] in
private theorem purePowerMap_mem (e : K →+* F) (j : ℕ) (v : Fin 2 → F) :
    purePowerMap j v ∈ highestWeightSpan e (2 ^ j) := by
  have h0 := X_pow_mem_highestWeightSpan e (2 ^ j)
  have h1 : (X 1 : MvPolynomial (Fin 2) F) ^ (2 ^ j) ∈ highestWeightSpan e (2 ^ j) := by
    let g : SL(2,K) := ⟨!![0, -1; 1, 0], by simp [Matrix.det_fin_two]⟩
    have h := (highestWeightSpan e (2 ^ j)).apply_mem_toSubmodule g h0
    change polynomialAction F (Matrix.SpecialLinearGroup.map e g) (X 0 ^ (2 ^ j)) ∈ _ at h
    have heq : polynomialAction F (Matrix.SpecialLinearGroup.map e g) (X 0 ^ (2 ^ j)) =
        X 1 ^ (2 ^ j) := by
      simp only [map_pow, polynomialAction, MvPolynomial.aeval_X, Fin.sum_univ_two]
      change (C (e 0) * X 0 + C (e 1) * X 1) ^ (2 ^ j) = _
      simp
    rwa [heq] at h
  exact (highestWeightSpan e (2 ^ j)).toSubmodule.add_mem
    ((highestWeightSpan e (2 ^ j)).toSubmodule.smul_mem _ h0)
    ((highestWeightSpan e (2 ^ j)).toSubmodule.smul_mem _ h1)

private def purePowerToSpan (e : K →+* F) (j : ℕ) :
    (Fin 2 → F) →ₗ[F] (highestWeightSpan e (2 ^ j)).toSubmodule :=
  (purePowerMap j).codRestrict _ (purePowerMap_mem e j)

private theorem purePowerToSpan_bijective (e : K →+* F) (j : ℕ) :
    Function.Bijective (purePowerToSpan e j) := by
  refine ⟨fun v w h => purePowerMap_injective j (congrArg Subtype.val h), ?_⟩
  intro f
  have hr : (highestWeightSpan e (2 ^ j)).toSubmodule ≤ (purePowerMap j).range := by
    apply Submodule.span_le.mpr
    rintro _ ⟨g, rfl⟩
    have hv : purePowerMap (F := F) j ![1, 0] = X 0 ^ (2 ^ j) := by simp [purePowerMap]
    dsimp only
    rw [← hv, purePowerMap_action]
    exact LinearMap.mem_range_self _ _
  obtain ⟨v, hv⟩ := hr f.property
  exact ⟨v, Subtype.ext hv⟩

/-- The degree `2^j` orbit span is the natural representation with its coefficients
raised to `2^j`, through the explicit pure-power polynomial map. -/
def highestWeightPurePowerEquiv (e : K →+* F) (j : ℕ) :
    (highestWeightSpan e (2 ^ j)).toRepresentation.Equiv
      (embeddedNatural ((iterateFrobenius F 2 j).comp e)) := by
  apply Representation.Equiv.symm
  refine Representation.Equiv.mk
    (LinearEquiv.ofBijective (purePowerToSpan e j) (purePowerToSpan_bijective e j)) ?_
  intro g
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  exact (purePowerMap_action e j g v).symm


/-- The inverse intertwiner is the explicit pure-power polynomial map, allowing
its tensor factors to be multiplied in further model comparisons. -/
theorem highestWeightPurePowerEquiv_symm_apply (e : K →+* F) (j : ℕ) (v : Fin 2 → F) :
    ((highestWeightPurePowerEquiv e j).symm v : MvPolynomial (Fin 2) F) =
      v 0 • X 0 ^ (2 ^ j) + v 1 • X 1 ^ (2 ^ j) := by
  rfl

end
end Representation.SL2.BinarySmall
