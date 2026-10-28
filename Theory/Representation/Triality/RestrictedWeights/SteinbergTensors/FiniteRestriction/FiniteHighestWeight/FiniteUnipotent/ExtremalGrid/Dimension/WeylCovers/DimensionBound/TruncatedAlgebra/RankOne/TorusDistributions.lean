module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight.FiniteUnipotent.ExtremalGrid.Dimension.WeylCovers.DimensionBound.TruncatedAlgebra.RankOne.Gauss
public import Theory.AlgebraicGroup.Representations.Algebraic.WeightSpaces
public import Theory.AlgebraicGroup.Tori.Character.Classification
public import Mathlib.RingTheory.Binomial

/-!
# Finite spectral calculus for the rank-one diagonal torus

Pull back a rational representation along the actual morphism
`z ↦ f(diag(z,z⁻¹))`. Rational torus weight decomposition and classification
of algebraic characters of the one-dimensional torus give an internal direct
sum indexed by integers. Finite dimensionality makes the projection family
finitely supported. The resulting finite functional calculus includes zero
vectors and weights outside that support.

The shifted binomial operators evaluate integer binomial coefficients on these
weights before casting into the field. The integer Vandermonde identity then
expresses each shifted operator as a finite linear combination of the unshifted
operators, in every characteristic.

No semisimplicity of the ambient representation, root-algebra membership,
or root normalization is assumed. The parameter is the direct diagonal, not
the inverse source coroot.

Source: rational torus characters and integral weight calculus supporting
Steinberg, *Representations of algebraic groups* (1963), §§2–3.
-/

open Theory.AlgebraicGroup
open scoped BigOperators
namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ExtremalGrid.CyclicDimension
public noncomputable section
universe u v
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {K : Variety k} [AlgebraicGroup K]
variable {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

private instance torusTopAlgebraicGroup : AlgebraicGroup (ClosedSubgroup.top (G := KMult k)).carrierVariety :=
  ClosedSubgroup.carrierAlgebraicGroup _

private def torusTopIso :
    Theory.AlgebraicGroup.Iso (KMult k) (ClosedSubgroup.top (G := KMult k)).carrierVariety := by
  let T : ClosedSubgroup (KMult k) := ClosedSubgroup.top
  let toTop : Morphism (KMult k) T.carrierVariety :=
    (Morphism.id _).codRestrictClosedSubgroup T (fun _ => trivial)
  exact {
    hom := toTop
    inv := T.inclusion
    hom_inv_id := by intro x; rfl
    inv_hom_id := by
      intro y
      apply T.inclusion_injective
      rfl }

private def torusIntegerCharacter (m : ℤ) :
    TorusWeight (ClosedSubgroup.top (G := KMult k)) :=
  (dLaurentCharacter 1 (fun _ => m)).comp (ClosedSubgroup.top (G := KMult k)).inclusion

omit [IsAlgClosed k] in
private theorem torusIntegerCharacter_eval (m : ℤ)
    (t : Variety.Point (ClosedSubgroup.top (G := KMult k)).carrierVariety) :
    (torusIntegerCharacter m).pointCharacter t =
      (dPointEquiv 1 ((ClosedSubgroup.top (G := KMult k)).includePoint t) 0 : k) ^ m := by
  change (dPointEquiv 1 ((dLaurentCharacter 1 (fun _ => m)).onPoints
    ((ClosedSubgroup.top (G := KMult k)).includePoint t)) 0 : k) = _
  rw [dLaurentCharacter_apply]
  simp

private theorem torusIntegerCharacter_bijective :
    Function.Bijective (torusIntegerCharacter (k := k)) := by
  constructor
  · intro m n h
    have h' : dLaurentCharacter (k := k) 1 (fun _ => m) =
        dLaurentCharacter 1 (fun _ => n) := by
      apply Morphism.ext
      funext t
      exact congrArg (fun c => c.onPoints (torusTopIso.hom.onPoints t)) h
    exact congrFun (dLaurentCharacter_injective 1 h') 0
  · intro χ
    obtain ⟨a, ha⟩ := dLaurentCharacter_surjective 1 (χ.comp torusTopIso.hom)
    refine ⟨a 0, ?_⟩
    have ha' : (fun _ : Fin 1 => a 0) = a := funext fun i => congrArg a (Subsingleton.elim _ _)
    apply Morphism.ext
    funext t
    change (dLaurentCharacter 1 (fun _ => a 0)).onPoints
      ((ClosedSubgroup.top (G := KMult k)).includePoint t) = χ.onPoints t
    rw [ha', ha]
    change χ.onPoints (torusTopIso.hom.onPoints
      (torusTopIso.inv.onPoints t)) = χ.onPoints t
    rw [torusTopIso.inv_hom_id]

/-- The full integral weight space, including zero. -/
@[expose] def rankOneWeightSpace (f : Morphism (slVariety k 2) K)
    (rho : RationalRepresentation K V) (m : ℤ) : Submodule k V where
  carrier := {v | rankOneHasWeight f rho m v}
  zero_mem' := by intro z; simp
  add_mem' hv hw z := by simp [hv z, hw z, smul_add]
  smul_mem' c v hv z := by simp [hv z, smul_comm c]

omit [IsAlgClosed k] in
private theorem torusPoint_recover (t : Variety.Point (KMult k)) :
    rankOneTorusPoint (dPointEquiv 1 t 0) = t := by
  apply (dPointEquiv 1).injective
  funext i
  simp only [rankOneTorusPoint, Equiv.apply_symm_apply]
  exact congrArg (dPointEquiv 1 t) (Subsingleton.elim _ _)

omit [FiniteDimensional k V] in
private theorem rankOneWeightSpace_eq (f : Morphism (slVariety k 2) K)
    (rho : RationalRepresentation K V) (τ : RationalRepresentation (KMult k) V)
    (hτ : IsPullbackRepresentation (f.comp standardSL2DiagonalMorphism) rho τ)
    (m : ℤ) : rankOneWeightSpace f rho m =
      weightSpace τ ClosedSubgroup.top (torusIntegerCharacter m) := by
  ext v
  constructor
  · intro hv t
    rw [torusIntegerCharacter_eval, hτ]
    simpa only [rankOneDiagonal, torusPoint_recover, Morphism.comp, Morphism.onPoints,
      Variety.Morphism.comp, MonoidHom.coe_mk, OneHom.coe_mk] using
      hv (dPointEquiv 1 ((ClosedSubgroup.top (G := KMult k)).includePoint t) 0)
  · intro hv z
    have ht := hv (torusTopIso.hom.onPoints (rankOneTorusPoint z))
    rw [torusIntegerCharacter_eval, hτ] at ht
    change (rho.action ((f.comp standardSL2DiagonalMorphism).onPoints
      (torusTopIso.inv.onPoints (torusTopIso.hom.onPoints (rankOneTorusPoint z))))).val v =
      (dPointEquiv 1 (torusTopIso.inv.onPoints
        (torusTopIso.hom.onPoints (rankOneTorusPoint z))) 0 : k) ^ m • v at ht
    rw [torusTopIso.hom_inv_id, rankOneTorusPoint_coordinate] at ht
    simpa only [rankOneDiagonal, Morphism.comp, Morphism.onPoints,
      Variety.Morphism.comp, MonoidHom.coe_mk, OneHom.coe_mk] using ht

theorem rankOneWeightSpace_isInternal (f : Morphism (slVariety k 2) K)
    (rho : RationalRepresentation K V) (hr : IsRationalRepresentation rho) :
    DirectSum.IsInternal (rankOneWeightSpace f rho) := by
  obtain ⟨τ, hτ, hrτ⟩ := rationalRepresentation_pullback_exists
    (f.comp standardSL2DiagonalMorphism) rho hr
  have heq : rankOneWeightSpace f rho =
      (fun m => weightSpace τ ClosedSubgroup.top (torusIntegerCharacter m)) :=
    funext (rankOneWeightSpace_eq f rho τ hτ)
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
  · simpa only [heq, Function.comp_def] using
      (weightSpace_iSupIndep τ ClosedSubgroup.top).comp torusIntegerCharacter_bijective.1
  · rw [heq]
    rw [torusIntegerCharacter_bijective.2.iSup_comp]
    exact torusRepresentation_weightSpace_iSup_eq_top τ hrτ (dVariety_isTorus 1)

private def torusComponent (f : Morphism (slVariety k 2) K)
    (rho : RationalRepresentation K V) (hr : IsRationalRepresentation rho) (m : ℤ) :
    Module.End k V :=
  (rankOneWeightSpace f rho m).subtype ∘ₗ
    DirectSum.component k ℤ (fun n => rankOneWeightSpace f rho n) m ∘ₗ
      (LinearEquiv.ofBijective (DirectSum.coeLinearMap (rankOneWeightSpace f rho))
        (rankOneWeightSpace_isInternal f rho hr)).symm.toLinearMap

private theorem torusComponent_mem (f : Morphism (slVariety k 2) K)
    (rho : RationalRepresentation K V) (hr : IsRationalRepresentation rho) (m : ℤ) (v : V) :
    torusComponent f rho hr m v ∈ rankOneWeightSpace f rho m :=
  ((LinearEquiv.ofBijective (DirectSum.coeLinearMap (rankOneWeightSpace f rho))
    (rankOneWeightSpace_isInternal f rho hr)).symm v m).property

private theorem torusComponent_same (f : Morphism (slVariety k 2) K)
    (rho : RationalRepresentation K V) (hr : IsRationalRepresentation rho)
    (m : ℤ) (v : V) (hv : rankOneHasWeight f rho m v) :
    torusComponent f rho hr m v = v := by
  exact congrArg Subtype.val
    ((rankOneWeightSpace_isInternal f rho hr).ofBijective_coeLinearMap_of_mem hv)

private theorem torusComponent_ne (f : Morphism (slVariety k 2) K)
    (rho : RationalRepresentation K V) (hr : IsRationalRepresentation rho)
    (m n : ℤ) (hmn : m ≠ n) (v : V) (hv : rankOneHasWeight f rho n v) :
    torusComponent f rho hr m v = 0 := by
  exact congrArg Subtype.val
    ((rankOneWeightSpace_isInternal f rho hr).ofBijective_coeLinearMap_of_mem_ne hmn.symm hv)

private theorem torusComponent_finite (f : Morphism (slVariety k 2) K)
    (rho : RationalRepresentation K V) (hr : IsRationalRepresentation rho) :
    (Function.support (torusComponent f rho hr)).Finite := by
  apply (Submodule.finite_ne_bot_of_iSupIndep
    (rankOneWeightSpace_isInternal f rho hr).submodule_iSupIndep).subset
  intro m hm hbot
  apply hm
  ext v
  have hv := torusComponent_mem f rho hr m v
  simpa only [hbot, Submodule.mem_bot, LinearMap.zero_apply] using hv

/-- The finitely supported family of projections onto the actual integral
weight spaces of the direct diagonal action. -/
def rankOneTorusProjectors (f : Morphism (slVariety k 2) K)
    (rho : RationalRepresentation K V) (hr : IsRationalRepresentation rho) :
    ℤ →₀ Module.End k V :=
  Finsupp.ofSupportFinite (torusComponent f rho hr) (torusComponent_finite f rho hr)

theorem rankOneTorusProjectors_weight (f : Morphism (slVariety k 2) K)
    (rho : RationalRepresentation K V) (hr : IsRationalRepresentation rho) (m : ℤ) (v : V) :
    rankOneHasWeight f rho m (rankOneTorusProjectors f rho hr m v) :=
  torusComponent_mem f rho hr m v

theorem rankOneTorusProjectors_apply_same (f : Morphism (slVariety k 2) K)
    (rho : RationalRepresentation K V) (hr : IsRationalRepresentation rho)
    (m : ℤ) (v : V) (hv : rankOneHasWeight f rho m v) :
    rankOneTorusProjectors f rho hr m v = v :=
  torusComponent_same f rho hr m v hv

theorem rankOneTorusProjectors_apply_ne (f : Morphism (slVariety k 2) K)
    (rho : RationalRepresentation K V) (hr : IsRationalRepresentation rho)
    (m n : ℤ) (hmn : m ≠ n) (v : V) (hv : rankOneHasWeight f rho n v) :
    rankOneTorusProjectors f rho hr m v = 0 :=
  torusComponent_ne f rho hr m n hmn v hv

theorem rankOneTorusProjectors_range (f : Morphism (slVariety k 2) K)
    (rho : RationalRepresentation K V) (hr : IsRationalRepresentation rho) (m : ℤ) :
    LinearMap.range (rankOneTorusProjectors f rho hr m) = rankOneWeightSpace f rho m := by
  apply le_antisymm
  · rintro v ⟨w, rfl⟩
    exact rankOneTorusProjectors_weight f rho hr m w
  · intro v hv
    exact ⟨v, rankOneTorusProjectors_apply_same f rho hr m v hv⟩

theorem rankOneTorusProjectors_idempotent (f : Morphism (slVariety k 2) K)
    (rho : RationalRepresentation K V) (hr : IsRationalRepresentation rho) (m : ℤ) :
    rankOneTorusProjectors f rho hr m * rankOneTorusProjectors f rho hr m =
      rankOneTorusProjectors f rho hr m := by
  ext v
  exact rankOneTorusProjectors_apply_same f rho hr m _
    (rankOneTorusProjectors_weight f rho hr m v)

theorem rankOneTorusProjectors_orthogonal (f : Morphism (slVariety k 2) K)
    (rho : RationalRepresentation K V) (hr : IsRationalRepresentation rho)
    (m n : ℤ) (hmn : m ≠ n) :
    rankOneTorusProjectors f rho hr m * rankOneTorusProjectors f rho hr n = 0 := by
  ext v
  exact rankOneTorusProjectors_apply_ne f rho hr m n hmn _
    (rankOneTorusProjectors_weight f rho hr n v)

/-- Finite functional calculus on the integral weights. -/
@[expose] def rankOneTorusOperator (f : Morphism (slVariety k 2) K)
    (rho : RationalRepresentation K V) (hr : IsRationalRepresentation rho)
    (c : ℤ → k) : Module.End k V :=
  (rankOneTorusProjectors f rho hr).sum fun m p => c m • p

/-- This formula includes the zero eigenvector and weights outside the support. -/
theorem rankOneTorusOperator_apply_weight (f : Morphism (slVariety k 2) K)
    (rho : RationalRepresentation K V) (hr : IsRationalRepresentation rho)
    (c : ℤ → k) (m : ℤ) (v : V) (hv : rankOneHasWeight f rho m v) :
    rankOneTorusOperator f rho hr c v = c m • v := by
  classical
  simp only [rankOneTorusOperator, Finsupp.sum, LinearMap.sum_apply, LinearMap.smul_apply]
  rw [Finset.sum_eq_single m]
  · rw [rankOneTorusProjectors_apply_same f rho hr m v hv]
  · intro n _ hnm
    rw [rankOneTorusProjectors_apply_ne f rho hr n m hnm v hv, smul_zero]
  · intro hm
    have hv0 : v = 0 := by
      have h := rankOneTorusProjectors_apply_same f rho hr m v hv
      rw [Finsupp.notMem_support_iff.mp hm, LinearMap.zero_apply] at h
      exact h.symm
    simp [hv0]

/-- Endomorphisms are determined on all integral weight spaces. -/
theorem rankOne_weight_ext (f : Morphism (slVariety k 2) K)
    (rho : RationalRepresentation K V) (hr : IsRationalRepresentation rho)
    {A B : Module.End k V}
    (h : ∀ m v, rankOneHasWeight f rho m v → A v = B v) : A = B := by
  apply LinearMap.eqLocus_eq_top.mp
  apply top_unique
  rw [← (rankOneWeightSpace_isInternal f rho hr).submodule_iSup_eq_top]
  exact iSup_le fun m v hv => h m v hv

/-- The spectral projections sum to the identity. -/
theorem rankOneTorusProjectors_sum (f : Morphism (slVariety k 2) K)
    (rho : RationalRepresentation K V) (hr : IsRationalRepresentation rho) :
    (rankOneTorusProjectors f rho hr).sum (fun _ p => p) = 1 := by
  apply rankOne_weight_ext f rho hr
  intro m v hv
  simpa only [rankOneTorusOperator, one_smul, Module.End.one_apply] using
    rankOneTorusOperator_apply_weight f rho hr (fun _ => 1) m v hv

/-- The finite Laurent expansion of the actual direct diagonal action. -/
theorem rankOneDiagonal_laurent (f : Morphism (slVariety k 2) K)
    (rho : RationalRepresentation K V) (hr : IsRationalRepresentation rho) (z : kˣ) :
    (rho.action (rankOneDiagonal f z)).val =
      (rankOneTorusProjectors f rho hr).sum (fun m p => (z : k) ^ m • p) := by
  apply rankOne_weight_ext f rho hr
  intro m v hv
  exact (hv z).trans (rankOneTorusOperator_apply_weight f rho hr
    (fun m => (z : k) ^ m) m v hv).symm

/-- Integer binomial coefficients are formed before reduction into the field. -/
@[expose] def rankOneTorusBinomial (f : Morphism (slVariety k 2) K)
    (rho : RationalRepresentation K V) (hr : IsRationalRepresentation rho)
    (d : ℤ) (j : ℕ) : Module.End k V :=
  rankOneTorusOperator f rho hr (fun m => ((Ring.choose (m + d) j : ℤ) : k))

/-- The shifted torus operator acts by the integral binomial of the weight,
including on zero vectors and for weights outside the projector support. -/
theorem rankOneTorusBinomial_apply_weight (f : Morphism (slVariety k 2) K)
    (rho : RationalRepresentation K V) (hr : IsRationalRepresentation rho)
    (d m : ℤ) (j : ℕ) (v : V) (hv : rankOneHasWeight f rho m v) :
    rankOneTorusBinomial f rho hr d j v = ((Ring.choose (m + d) j : ℤ) : k) • v :=
  rankOneTorusOperator_apply_weight f rho hr _ m v hv

/-- Integer Vandermonde, transferred to the finite torus spectral calculus. -/
theorem rankOneTorusBinomial_vandermonde (f : Morphism (slVariety k 2) K)
    (rho : RationalRepresentation K V) (hr : IsRationalRepresentation rho)
    (d : ℤ) (j : ℕ) :
    rankOneTorusBinomial f rho hr d j =
      ∑ r ∈ Finset.range (j + 1), ((Ring.choose d (j - r) : ℤ) : k) •
        rankOneTorusBinomial f rho hr 0 r := by
  apply rankOne_weight_ext f rho hr
  intro m v hv
  simp only [LinearMap.sum_apply, LinearMap.smul_apply]
  simp_rw [rankOneTorusBinomial_apply_weight f rho hr _ m _ v hv, add_zero, smul_smul]
  rw [← Finset.sum_smul]
  congr 1
  have h := Ring.add_choose_eq (r := m) (s := d) j (Commute.all m d)
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at h
  have hc := congrArg (fun a : ℤ => (a : k)) h
  simpa only [Int.cast_sum, Int.cast_mul, mul_comm] using hc

end
end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ExtremalGrid.CyclicDimension
