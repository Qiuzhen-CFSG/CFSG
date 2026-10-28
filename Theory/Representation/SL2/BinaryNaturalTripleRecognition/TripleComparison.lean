module

public import Theory.Representation.SL2.BinaryNaturalTripleRecognition.NaturalComparison
public import Theory.Representation.SL2.HighestWeightDimension
public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# The weight-seven module and the triple Frobenius tensor

For a field `K` of eight elements embedded in a characteristic-two field `F`,
the weight-seven polynomial orbit span is equivalent to scalar extension of
the literal tensor `N ⊗ N^σ ⊗ N^(σ²)` over `K`.

Multiply the pure-power polynomial maps of degrees one, two and four.
Multiplication is equivariant, and its image contains `X₀^7`, hence the entire
highest-weight orbit span. That span has dimension eight by the binary digit
formula. The tensor source also has dimension eight, so the image is exactly
the orbit span and this specific multiplication map is bijective. Tensor base
change and natural base change identify its source with the actual scalar
extension of the three Frobenius-twisted natural factors over `K`.

This is the concrete polynomial-to-tensor comparison used in the exceptional
binary SL₂ case, independently of recognition or scalar descent.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), G.9.3(16),
printed pp.354,356--357; GLS volume 3, §§2.8.6, 2.8.8, 2.8.10(b).
-/

public section

open scoped MatrixGroups TensorProduct
namespace Representation.SL2.BinarySmall
noncomputable section

section TensorEquivalences
variable {k L G V W V' W' : Type*} [Field k] [Field L] [Algebra k L] [Group G]
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
  [AddCommGroup V'] [Module k V'] [AddCommGroup W'] [Module k W']

private def tensorEquiv {ρ : Representation k G V} {σ : Representation k G W}
    {ρ' : Representation k G V'} {σ' : Representation k G W'}
    (e : ρ.Equiv ρ') (f : σ.Equiv σ') : (ρ.tprod σ).Equiv (ρ'.tprod σ') := by
  refine Representation.Equiv.mk (TensorProduct.congr e.toLinearEquiv f.toLinearEquiv) ?_
  intro g
  ext v w
  exact congrArg₂ (fun v w => v ⊗ₜ[k] w) (congrArg (fun t => t v) (e.isIntertwining' g))
    (congrArg (fun t => t w) (f.isIntertwining' g))

private def tensorBaseChange (ρ : Representation k G V) (σ : Representation k G W) :
    (extendScalars L (ρ.tprod σ)).Equiv ((extendScalars L ρ).tprod (extendScalars L σ)) := by
  refine Representation.Equiv.mk (TensorProduct.AlgebraTensorModule.distribBaseChange k L V W) ?_
  intro g
  ext v w
  simp only [TensorProduct.AlgebraTensorModule.curry_apply, TensorProduct.curry_apply,
    LinearMap.coe_restrictScalars, LinearMap.comp_apply, LinearEquiv.coe_coe, extendScalars_apply,
    LinearMap.baseChange_tmul, Representation.tprod_apply, TensorProduct.map_tmul,
    TensorProduct.AlgebraTensorModule.distribBaseChange_tmul]
end TensorEquivalences

variable {K F : Type*} [Field K] [Field F] [CharP F 2]
open MvPolynomial

private abbrev polyRep (e : K →+* F) :
    Representation F SL(2, K) (MvPolynomial (Fin 2) F) :=
  (polynomialRepresentation F).comp (Matrix.SpecialLinearGroup.map e)

private abbrev factorRep (e : K →+* F) (j : ℕ) :=
  embeddedNatural ((iterateFrobenius F 2 j).comp e)

private abbrev productRep (e : K →+* F) :=
  ((factorRep e 0).tprod (factorRep e 1)).tprod (factorRep e 2)

private def factorMap (e : K →+* F) (j : ℕ) :
    (factorRep e j).IntertwiningMap (polyRep e) where
  toLinearMap := (highestWeightSpan e (2 ^ j)).toSubmodule.subtype.comp
    (highestWeightPurePowerEquiv e j).symm.toLinearMap
  isIntertwining' g := by
    apply LinearMap.ext
    intro v
    exact congrArg Subtype.val
      (congrArg (fun t => t v) ((highestWeightPurePowerEquiv e j).symm.isIntertwining' g))

private theorem factorMap_apply (e : K →+* F) (j : ℕ) (v : Fin 2 → F) :
    factorMap e j v = v 0 • X 0 ^ (2 ^ j) + v 1 • X 1 ^ (2 ^ j) :=
  highestWeightPurePowerEquiv_symm_apply e j v

private def polyMul (e : K →+* F) :
    ((polyRep e).tprod (polyRep e)).IntertwiningMap (polyRep e) where
  toLinearMap := LinearMap.mul' F (MvPolynomial (Fin 2) F)
  isIntertwining' g := by
    apply TensorProduct.ext'
    intro u v
    exact (map_mul (polynomialAction F (Matrix.SpecialLinearGroup.map e g)) u v).symm

private def productMap (e : K →+* F) : (productRep e).IntertwiningMap (polyRep e) :=
  (polyMul e).comp (((polyMul e).comp ((factorMap e 0).tensor (factorMap e 1))).tensor
    (factorMap e 2))

private theorem productMap_tmul (e : K →+* F) (u v w : Fin 2 → F) :
    productMap e ((u ⊗ₜ[F] v) ⊗ₜ[F] w) =
      (u 0 • X 0 + u 1 • X 1) * (v 0 • X 0 ^ 2 + v 1 • X 1 ^ 2) *
      (w 0 • X 0 ^ 4 + w 1 • X 1 ^ 4) := by
  simp [productMap, polyMul, Representation.IntertwiningMap.comp_apply,
    Representation.IntertwiningMap.tensor_apply, factorMap_apply]

private def productRange (e : K →+* F) : Subrepresentation (polyRep e) where
  toSubmodule := (productMap e).toLinearMap.range
  apply_mem_toSubmodule g := by
    rintro _ ⟨v, rfl⟩
    exact ⟨productRep e g v, Representation.IntertwiningMap.isIntertwining _ _ (productMap e) g v⟩

private theorem highestWeight_le_range (e : K →+* F) :
    highestWeightSpan e 7 ≤ productRange e := by
  apply (highestWeightSpan_le_iff e 7 (productRange e)).mpr
  refine ⟨((![1, 0] ⊗ₜ[F] ![1, 0]) ⊗ₜ[F] ![1, 0]), ?_⟩
  change productMap e _ = _
  rw [productMap_tmul]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    one_smul, zero_smul, add_zero]
  ring

omit [CharP F 2] in
private theorem tripleSpace_finrank : Module.finrank F (TripleSpace F) = 8 := by
  simp [TripleSpace, NaturalSpace, Module.finrank_tensorProduct]

private theorem seven_finrank [Finite K] (e : K →+* F) (hcard : Nat.card K = 8) :
    Module.finrank F (highestWeightSpan e 7).toSubmodule = 8 := by
  rw [highestWeightSpan_finrank_eq_prod_digits e 2 (by decide) 7 3 (by simpa using hcard) (by decide)]
  decide

private theorem productRange_eq [Finite K] (e : K →+* F) (hcard : Nat.card K = 8) :
    (highestWeightSpan e 7).toSubmodule = (productMap e).toLinearMap.range := by
  apply Submodule.eq_of_le_of_finrank_le (S₂ := (productMap e).toLinearMap.range)
    (highestWeight_le_range e)
  rw [seven_finrank e hcard]
  exact (productMap e).toLinearMap.finrank_range_le.trans_eq tripleSpace_finrank

private def productToSpan [Finite K] (e : K →+* F) (hcard : Nat.card K = 8) :
    (productRep e).IntertwiningMap (highestWeightSpan e 7).toRepresentation where
  toLinearMap := (productMap e).toLinearMap.codRestrict _ (fun v => by
    rw [productRange_eq e hcard]
    exact LinearMap.mem_range_self _ v)
  isIntertwining' g := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    exact Representation.IntertwiningMap.isIntertwining _ _ (productMap e) g v

private theorem productToSpan_surjective [Finite K] (e : K →+* F)
    (hcard : Nat.card K = 8) : Function.Surjective (productToSpan e hcard) := by
  intro v
  have hv : (v : MvPolynomial (Fin 2) F) ∈ (productMap e).toLinearMap.range :=
    (productRange_eq e hcard).le v.property
  obtain ⟨w, hw⟩ := hv
  exact ⟨w, Subtype.ext hw⟩

private def productSpanEquiv [Finite K] (e : K →+* F) (hcard : Nat.card K = 8) :
    (productRep e).Equiv (highestWeightSpan e 7).toRepresentation := by
  let f := (productToSpan e hcard).toLinearMap
  have hd : Module.finrank F (TripleSpace F) =
      Module.finrank F (highestWeightSpan e 7).toSubmodule :=
    (tripleSpace_finrank (F := F)).trans (seven_finrank e hcard).symm
  have hs : Function.Surjective f := productToSpan_surjective e hcard
  have hi : Function.Injective f :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (K := F) (V := TripleSpace F)
      (V₂ := (highestWeightSpan e 7).toSubmodule) (f := f) hd).mpr hs
  exact (productToSpan e hcard).ofBijective ⟨hi, hs⟩

variable [Finite K] [CharP K 2] [Algebra K F]

private def factorBaseChange (j : ℕ) :
    (extendScalars F (frobeniusNatural (K := K) j)).Equiv
      (factorRep (algebraMap K F) j) := by
  have he : (algebraMap K F).comp (iterateFrobeniusEquiv K 2 j).toRingHom =
      (iterateFrobenius F 2 j).comp (algebraMap K F) := by
    ext x
    exact map_pow (algebraMap K F) x (2 ^ j)
  change (extendScalars F (embeddedNatural (iterateFrobeniusEquiv K 2 j).toRingHom)).Equiv _
  unfold factorRep
  rw [← he]
  exact embeddedNaturalBaseChange (iterateFrobeniusEquiv K 2 j).toRingHom

private def tripleBaseChange :
    (extendScalars (F := K) (V := TripleSpace K) F (triple (K := K))).Equiv
      (productRep (algebraMap K F)) := by
  let e01 : (extendScalars (F := K) (V := NaturalSpace K ⊗[K] NaturalSpace K) F
      ((frobeniusNatural 0).tprod (frobeniusNatural 1))).Equiv
      ((factorRep (algebraMap K F) 0).tprod (factorRep (algebraMap K F) 1)) :=
    (tensorBaseChange (L := F) (frobeniusNatural (K := K) 0)
      (frobeniusNatural (K := K) 1)).trans
      (tensorEquiv (factorBaseChange (K := K) (F := F) 0)
        (factorBaseChange (K := K) (F := F) 1))
  exact (tensorBaseChange (L := F)
    ((frobeniusNatural (K := K) 0).tprod (frobeniusNatural (K := K) 1))
    (frobeniusNatural (K := K) 2)).trans
    (tensorEquiv e01 (factorBaseChange (K := K) (F := F) 2))

/-- The weight-seven orbit span is the scalar extension of the actual triple
Frobenius tensor of the natural module over the field of eight elements. -/
def highestWeightSevenTripleEquiv (hcard : Nat.card K = 8) :
    (highestWeightSpan (algebraMap K F) 7).toRepresentation.Equiv
      (extendScalars (F := K) (V := TripleSpace K) F (triple (K := K))) :=
  (productSpanEquiv (algebraMap K F) hcard).symm.trans tripleBaseChange.symm

end
end Representation.SL2.BinarySmall
