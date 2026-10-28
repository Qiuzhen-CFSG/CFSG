module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.TrialitySource.TensorWeights
public import Theory.Representation.SL2.BinaryNaturalTripleRecognition.NaturalComparison

/-!
# Constructing the threefold source Frobenius tensor comparison

Multiply the three pure-power polynomial maps. Their image contains the
highest-weight vector; dimension eight makes this concrete intertwiner
bijective. The field-power identities turn the three factors into the
natural matrix actions through one embedding, its composite with the
source Frobenius, and its composite with the Frobenius squared.

For an arbitrary irreducible binary 8n-dimensional action of SL₂(2^(3n)),
TensorWeights supplies its actual highest weight and Schur degree, so this
construction gives a representation equivalence after extension of its
Schur field to an algebraic closure. It assumes no tensor comparison.
TensorApplication supplies the literal source radical action. Descending
and matching the source root-coordinate basis remain separate obligations.

Source: Fong--Seitz II (4.7)(b), printed p.218 and the matrix comparison on
p.219. The polynomial construction extends the existing degree-seven proof
in BinaryNaturalTripleRecognition/TripleComparison uniformly to every n>0.
-/

@[expose] public noncomputable section
open scoped MatrixGroups TensorProduct MonoidAlgebra
open Representation Representation.SL2 Representation.SL2.BinarySmall MvPolynomial
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.TrialitySource.TensorAction
variable {F C : Type*} [Field F] [Field C]

/-- The actual threefold tensor, with all three factors using the same embedding
and the specified source field automorphism. -/
def cubicTensor (e : F →+* C) (σ : F ≃+* F) : Representation C SL(2,F) (TripleSpace C) :=
  ((embeddedNatural e).tprod (embeddedNatural (e.comp σ.toRingHom))).tprod
    (embeddedNatural ((e.comp σ.toRingHom).comp σ.toRingHom))

/-- Its action is the literal tensor of the three indicated natural matrices. -/
theorem cubicTensor_tmul (e : F →+* C) (σ : F ≃+* F) (g : SL(2,F))
    (u v w : Fin 2 → C) :
    cubicTensor e σ g ((u ⊗ₜ[C] v) ⊗ₜ[C] w) =
      ((embeddedNatural e g u ⊗ₜ[C] embeddedNatural (e.comp σ.toRingHom) g v) ⊗ₜ[C]
        embeddedNatural ((e.comp σ.toRingHom).comp σ.toRingHom) g w) := rfl

variable [CharP C 2]
private abbrev polyRep (e : F →+* C) : Representation C SL(2,F) (MvPolynomial (Fin 2) C) :=
  (polynomialRepresentation C).comp (Matrix.SpecialLinearGroup.map e)
private abbrev factorRep (e : F →+* C) (j : ℕ) :=
  embeddedNatural ((iterateFrobenius C 2 j).comp e)
private abbrev productRep (e : F →+* C) (n j : ℕ) :=
  ((factorRep e j).tprod (factorRep e (j+n))).tprod (factorRep e (j+2*n))

private def factorMap (e : F →+* C) (j : ℕ) :
    (factorRep e j).IntertwiningMap (polyRep e) where
  toLinearMap := (highestWeightSpan e (2^j)).toSubmodule.subtype.comp
    (highestWeightPurePowerEquiv e j).symm.toLinearMap
  isIntertwining' g := by
    apply LinearMap.ext
    intro v
    exact congrArg Subtype.val
      (congrArg (fun t => t v) ((highestWeightPurePowerEquiv e j).symm.isIntertwining' g))

private theorem factorMap_apply (e : F →+* C) (j : ℕ) (v : Fin 2 → C) :
    factorMap e j v = v 0 • X 0^(2^j)+v 1 • X 1^(2^j) :=
  highestWeightPurePowerEquiv_symm_apply e j v

private def polyMul (e : F →+* C) :
    ((polyRep e).tprod (polyRep e)).IntertwiningMap (polyRep e) where
  toLinearMap := LinearMap.mul' C (MvPolynomial (Fin 2) C)
  isIntertwining' g := by
    apply TensorProduct.ext'
    intro u v
    exact (map_mul (polynomialAction C (Matrix.SpecialLinearGroup.map e g)) u v).symm

private def productMap (e : F →+* C) (n j : ℕ) :
    (productRep e n j).IntertwiningMap (polyRep e) :=
  (polyMul e).comp (((polyMul e).comp ((factorMap e j).tensor (factorMap e (j+n)))).tensor
    (factorMap e (j+2*n)))

private theorem productMap_tmul (e : F →+* C) (n j : ℕ) (u v w : Fin 2 → C) :
    productMap e n j ((u ⊗ₜ[C] v) ⊗ₜ[C] w) =
      (u 0 • X 0^(2^j)+u 1 • X 1^(2^j)) *
      (v 0 • X 0^(2^(j+n))+v 1 • X 1^(2^(j+n))) *
      (w 0 • X 0^(2^(j+2*n))+w 1 • X 1^(2^(j+2*n))) := by
  simp [productMap,polyMul,Representation.IntertwiningMap.comp_apply,
    Representation.IntertwiningMap.tensor_apply,factorMap_apply]

private def productRange (e : F →+* C) (n j : ℕ) : Subrepresentation (polyRep e) where
  toSubmodule := (productMap e n j).toLinearMap.range
  apply_mem_toSubmodule g := by
    rintro _ ⟨v,rfl⟩
    exact ⟨productRep e n j g v,
      Representation.IntertwiningMap.isIntertwining _ _ (productMap e n j) g v⟩

private theorem highestWeight_le_range (e : F →+* C) (n j : ℕ) :
    highestWeightSpan e (2^j+2^(j+n)+2^(j+2*n)) ≤ productRange e n j := by
  apply (highestWeightSpan_le_iff _ _ _).mpr
  refine ⟨((![1,0] ⊗ₜ[C] ![1,0]) ⊗ₜ[C] ![1,0]),?_⟩
  change productMap e n j _ = _
  rw [productMap_tmul]
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one,
    one_smul,zero_smul,add_zero,pow_add]

omit [CharP C 2] in
private theorem triple_finrank : Module.finrank C (TripleSpace C) = 8 := by
  simp [TripleSpace,NaturalSpace,Module.finrank_tensorProduct]

private theorem productRange_eq (e : F →+* C) (n j : ℕ)
    (hd : Module.finrank C (highestWeightSpan e (2^j+2^(j+n)+2^(j+2*n))).toSubmodule = 8) :
    (highestWeightSpan e (2^j+2^(j+n)+2^(j+2*n))).toSubmodule =
      (productMap e n j).toLinearMap.range := by
  apply Submodule.eq_of_le_of_finrank_le (S₂ := (productMap e n j).toLinearMap.range)
    (highestWeight_le_range e n j)
  rw [hd]
  exact (productMap e n j).toLinearMap.finrank_range_le.trans_eq triple_finrank

private def productToSpan (e : F →+* C) (n j : ℕ)
    (hd : Module.finrank C (highestWeightSpan e (2^j+2^(j+n)+2^(j+2*n))).toSubmodule = 8) :
    (productRep e n j).IntertwiningMap
      (highestWeightSpan e (2^j+2^(j+n)+2^(j+2*n))).toRepresentation where
  toLinearMap := (productMap e n j).toLinearMap.codRestrict _ (fun v => by
    rw [productRange_eq e n j hd]
    exact LinearMap.mem_range_self _ v)
  isIntertwining' g := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    exact Representation.IntertwiningMap.isIntertwining _ _ (productMap e n j) g v

private def productSpanEquiv (e : F →+* C) (n j : ℕ)
    (hd : Module.finrank C (highestWeightSpan e (2^j+2^(j+n)+2^(j+2*n))).toSubmodule = 8) :
    (productRep e n j).Equiv
      (highestWeightSpan e (2^j+2^(j+n)+2^(j+2*n))).toRepresentation := by
  let f := (productToSpan e n j hd).toLinearMap
  have hs : Function.Surjective f := by
    intro v
    have hv : (v : MvPolynomial (Fin 2) C) ∈ (productMap e n j).toLinearMap.range :=
      (productRange_eq e n j hd).le v.property
    obtain ⟨w,hw⟩ := hv
    exact ⟨w,Subtype.ext hw⟩
  have he : Module.finrank C (TripleSpace C) =
      Module.finrank C (highestWeightSpan e (2^j+2^(j+n)+2^(j+2*n))).toSubmodule :=
    triple_finrank.trans hd.symm
  exact (productToSpan e n j hd).ofBijective
    ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (K := C) (V := TripleSpace C) (f := f) he).mpr hs,hs⟩

private theorem productRep_eq (e : F →+* C) (σ : F ≃+* F) (n j : ℕ)
    (hσ : ∀ x,σ x = x^(2^n)) :
    productRep e n j = cubicTensor ((iterateFrobenius C 2 j).comp e) σ := by
  have h1 : (iterateFrobenius C 2 (j+n)).comp e =
      ((iterateFrobenius C 2 j).comp e).comp σ.toRingHom := by
    ext x
    change (e x)^(2^(j+n)) = (e (σ x))^(2^j)
    rw [hσ,map_pow,←pow_mul,←pow_add]
    congr 2
    omega
  have h2 : (iterateFrobenius C 2 (j+2*n)).comp e =
      (((iterateFrobenius C 2 j).comp e).comp σ.toRingHom).comp σ.toRingHom := by
    ext x
    change (e x)^(2^(j+2*n)) = (e (σ (σ x)))^(2^j)
    rw [hσ,hσ,map_pow,map_pow,←pow_mul,←pow_mul]
    congr 1
    rw [pow_add,show 2*n = n*2 by omega,pow_mul]
    ring
  unfold productRep factorRep cubicTensor
  rw [h1,h2]

variable [Finite F] [CharP F 2]

/-- The actual Schur extension of every binary 8n-dimensional irreducible
SL₂(2^(3n)) module is the cubic tensor, using the original field Frobenius.
This constructs the intertwiner uniformly, including n=1. -/
theorem recognition {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) SL(2,F) V) [ρ.IsIrreducible]
    (hnt : ∃ g,ρ g ≠ 1) {n : ℕ} (hn : 0 < n)
    (hF : Nat.card F = 2^(3*n)) (hV : Module.finrank (ZMod 2) V = 8*n)
    (σ : F ≃+* F) (hσ : ∀ x,σ x = x^(2^n)) :
    ∃ e : F →+* AlgebraicClosure (Module.End (ZMod 2)[SL(2,F)] ρ.asModule),
      Nonempty ((extendScalars
        (AlgebraicClosure (Module.End (ZMod 2)[SL(2,F)] ρ.asModule)) ρ.endFieldRep).Equiv
          (cubicTensor e σ)) := by
  let E := Module.End (ZMod 2)[SL(2,F)] ρ.asModule
  let C := AlgebraicClosure E
  let : CharP E 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) E).injective 2
  let : CharP C 2 := charP_of_injective_algebraMap (algebraMap E C).injective 2
  let : Finite ρ.asModule := Module.finite_iff_finite.mp
    (inferInstance : Module.Finite (ZMod 2) ρ.asModule)
  let : Module.Finite E ρ.asModule := Module.Finite.of_finite
  obtain ⟨e,j,_,⟨φ⟩⟩ := TensorWeights.highest_weight ρ hnt hn hF hV
  have hs : Module.finrank (ZMod 2) E = n := TensorWeights.schur_degree ρ hnt hn hF hV
  have hd : Module.finrank E ρ.asModule =
      Module.finrank C (highestWeightSpan e (2^j+2^(j+n)+2^(j+2*n))).toSubmodule := by
    rw [←Module.finrank_baseChange (R := C)]
    exact φ.toLinearEquiv.finrank_eq
  have hdim : Module.finrank C (highestWeightSpan e (2^j+2^(j+n)+2^(j+2*n))).toSubmodule = 8 := by
    have ht := Module.finrank_mul_finrank (ZMod 2) E ρ.asModule
    rw [hs,ρ.asModuleEquiv.finrank_eq,hV,hd] at ht
    nlinarith
  refine ⟨(iterateFrobenius C 2 j).comp e,?_⟩
  rw [←productRep_eq e σ n j hσ]
  exact ⟨φ.trans (productSpanEquiv e n j hdim).symm⟩

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.TrialitySource.TensorAction
