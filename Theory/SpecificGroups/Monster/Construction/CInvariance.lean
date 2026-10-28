module

public import Theory.SpecificGroups.Monster.Construction.GriessCarrier
public import Theory.SpecificGroups.Monster.Construction.LocalC.Action

/-!
# The local group preserves the Griess cubic form

The five nonzero source blocks are invariant under the actual local action.
On the short cubic block, every extraspecial automorphism fixes the central
involution and therefore preserves the signed central-product coefficient.
The mixed blocks use covariance of the short rank-one tensor, orthogonal
conjugation of symmetric matrices, and the spin normalizer's intertwining law.
Signed-basis and pure-tensor extensionality extend these identities to all
vectors. The five-block assembly proves invariance of the fixed `griessBeta`.

This proves Aschbacher 28.13 for the existing tensor-image group `LocalC.C`;
the faithful embedding into `GriessGroup` is constructed in `LocalEmbedding`.
Source: Aschbacher, *Sporadic Groups*, equations 28.1–28.6 and Lemma 28.13,
printed pp. 151–154 (PDF pages 81–83).
-/

@[expose] public section
noncomputable section
open scoped TensorProduct Matrix
namespace Sporadic.Monster.Construction.CInvariance
open LocalC TrialitySpin Griess

private def pull {S R W : Type*} [AddCommGroup S] [Module ℝ S]
    [AddCommGroup R] [Module ℝ R] [AddCommGroup W] [Module ℝ W]
    (f : S →ₗ[ℝ] R →ₗ[ℝ] W →ₗ[ℝ] ℝ)
    (s : Module.End ℝ S) (r : Module.End ℝ R) (w : Module.End ℝ W) :
    S →ₗ[ℝ] R →ₗ[ℝ] W →ₗ[ℝ] ℝ where
  toFun x := (f (s x)).compl₁₂ r w
  map_add' x y := by ext z t; simp
  map_smul' a x := by ext z t; simp

private theorem pull_apply {S R W : Type*} [AddCommGroup S] [Module ℝ S]
    [AddCommGroup R] [Module ℝ R] [AddCommGroup W] [Module ℝ W]
    (f : S →ₗ[ℝ] R →ₗ[ℝ] W →ₗ[ℝ] ℝ)
    (s : Module.End ℝ S) (r : Module.End ℝ R) (w : Module.End ℝ W)
    (x : S) (y : R) (z : W) : pull f s r w x y z = f (s x) (r y) (w z) := rfl

private theorem centralCoefficient_aut (f : MulAut Q1Image) (q : Q1Image) :
    centralCoefficient (f q) = centralCoefficient q := by
  classical
  have hz : f q = q1ImageCenterGenerator ↔ q = q1ImageCenterGenerator := by
    calc
      f q = q1ImageCenterGenerator ↔ f q = f q1ImageCenterGenerator := by
        rw [automorphism_fixes_centerGenerator]
      _ ↔ q = q1ImageCenterGenerator := f.injective.eq_iff
  have h1 : f q = 1 ↔ q = 1 := by
    exact f.map_eq_one_iff
  simp only [centralCoefficient, h1, hz]

theorem shortCubic_invariant (e : LatticeComparison) (p : compatibleAutomorphisms e)
    (x y z : ShortSpace e) :
    shortCubic e (shortAction e p x) (shortAction e p y) (shortAction e p z) =
      shortCubic e x y z := by
  have h : pull (shortCubic e) (shortAction e p) (shortAction e p)
      (shortAction e p) = shortCubic e := by
    apply (shortBasis e).ext
    intro i
    apply (shortBasis e).ext
    intro j
    apply (shortBasis e).ext
    intro k
    simp only [pull_apply, shortBasis_eq_vector,
      shortAction_vector, shortCubic_vector]
    change centralCoefficient (p.val.1 _ * p.val.1 _ * p.val.1 _) = _
    rw [← map_mul, ← map_mul, centralCoefficient_aut]
    rfl
  exact congrArg (fun f => f x y z) h

theorem shortLiftTensor_action (e : LatticeComparison) (p : compatibleAutomorphisms e)
    (r : ShortLift e) :
    shortLiftTensor e (shortLiftRepresentation e p r) =
      symmetricLeechRepresentation p.val.2 (shortLiftTensor e r) := by
  rw [shortLiftTensor, shortLiftClass_action, ← symmetricLeechRepresentation_shortTensor]
  rfl

theorem sourceSRR_invariant (e : LatticeComparison) (p : compatibleAutomorphisms e)
    (A : SymmetricPart) (x y : ShortSpace e) :
    sourceSRR e (symmetricLeechRepresentation p.val.2 A)
      (shortAction e p x) (shortAction e p y) = sourceSRR e A x y := by
  have h : (sourceSRR e (symmetricLeechRepresentation p.val.2 A)).compl₁₂
      (shortAction e p) (shortAction e p) = sourceSRR e A := by
    apply (shortBasis e).ext
    intro i
    apply (shortBasis e).ext
    intro j
    simp only [LinearMap.compl₁₂_apply, shortBasis_eq_vector, shortAction_vector,
      sourceSRR_vector, shortLiftTensor_action, symmetricLeechRepresentation_form]
    rw [← shortAction_vector, ← shortAction_vector, shortAction_form]
  exact congrArg (fun f => f x y) h

private theorem matrixPairing_invariant (g : Atlas.Lattices.LeechIsometryGroup)
    (A : SymmetricPart) (a b : NaturalSpace) :
    (symmetricLeechRepresentation g A).val.toBilin'
      (realLeechRepresentation g a) (realLeechRepresentation g b) = A.val.toBilin' a b := by
  rw [Matrix.toBilin'_apply', Matrix.toBilin'_apply']
  have h : (symmetricLeechRepresentation g A).val *ᵥ realLeechRepresentation g b =
      realLeechRepresentation g (A.val *ᵥ b) := by
    change ((realLeechMatrix g * A.val) * (realLeechMatrix g)ᵀ) *ᵥ
      (realLeechMatrix g *ᵥ b) = realLeechMatrix g *ᵥ (A.val *ᵥ b)
    rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, realLeechMatrix_orthogonal,
      Matrix.mul_one, Matrix.mulVec_mulVec]
  rw [h]
  exact realLeechRepresentation_form g a (A.val *ᵥ b)

private theorem trace_invariant (g : Atlas.Lattices.LeechIsometryGroup)
    (A : SymmetricPart) :
    Matrix.trace (symmetricLeechRepresentation g A).val = Matrix.trace A.val := by
  change Matrix.trace ((realLeechMatrix g * A.val) * (realLeechMatrix g)ᵀ) = _
  rw [Matrix.trace_mul_cycle, realLeechMatrix_orthogonal, Matrix.one_mul]

theorem symmetricNaturalBlock_invariant (g : Atlas.Lattices.LeechIsometryGroup)
    (A : SymmetricPart) (a b : NaturalSpace) :
    symmetricNaturalBlock (symmetricLeechRepresentation g A)
      (realLeechRepresentation g a) (realLeechRepresentation g b) =
      symmetricNaturalBlock A a b := by
  change (symmetricLeechRepresentation g A).val.toBilin' _ _ +
    (Matrix.trace (symmetricLeechRepresentation g A).val / 8) *
      (Matrix.toBilin' 1 _ _) = A.val.toBilin' a b +
    (Matrix.trace A.val / 8) * (Matrix.toBilin' 1 a b)
  rw [matrixPairing_invariant, trace_invariant]
  simp only [Matrix.toBilin'_apply', Matrix.one_mulVec]
  rw [show (realLeechRepresentation g a) ⬝ᵥ (realLeechRepresentation g b) = a ⬝ᵥ b from
    realLeechRepresentation_form g a b]

theorem shortNaturalBlock_invariant (g : Atlas.Lattices.LeechIsometryGroup)
    (A : SymmetricPart) (a b : NaturalSpace) :
    shortNaturalBlock (symmetricLeechRepresentation g A)
      (realLeechRepresentation g a) (realLeechRepresentation g b) =
      shortNaturalBlock A a b := by
  simp only [shortNaturalBlock, map_sub, map_smul, LinearMap.sub_apply,
    LinearMap.smul_apply, smul_eq_mul]
  rw [matrixPairing_invariant]
  simp only [Matrix.toBilin'_apply', Matrix.one_mulVec]
  rw [show (realLeechRepresentation g a) ⬝ᵥ (realLeechRepresentation g b) = a ⬝ᵥ b from
    realLeechRepresentation_form g a b]

theorem sourceSWW_invariant (p : localPullback) (A : SymmetricPart)
    (x y : MinusSpace) :
    sourceSWW (symmetricLeechRepresentation p.val.2 A)
      (pullbackTensor p x) (pullbackTensor p y) = sourceSWW A x y := by
  have h : (sourceSWW (symmetricLeechRepresentation p.val.2 A)).compl₁₂
      (pullbackTensor p).toLinearMap (pullbackTensor p).toLinearMap = sourceSWW A := by
    apply TensorProduct.ext'
    intro a v
    apply TensorProduct.ext'
    intro b w
    simp only [LinearMap.compl₁₂_apply, LinearEquiv.coe_coe, pullbackTensor_tmul]
    change tensorFormMap bothAxesDomain.form
      (symmetricNaturalBlock (symmetricLeechRepresentation p.val.2 A)) _ _ =
      tensorFormMap bothAxesDomain.form (symmetricNaturalBlock A) _ _
    rw [tensorFormMap_tmul, tensorFormMap_tmul]
    change symmetricNaturalBlock (symmetricLeechRepresentation p.val.2 A)
      (realLeechRepresentation p.val.2 a) (realLeechRepresentation p.val.2 b) *
      bothAxesDomain.form (p.val.1.val.1 v) (p.val.1.val.1 w) =
      symmetricNaturalBlock A a b * bothAxesDomain.form v w
    rw [symmetricNaturalBlock_invariant, p.val.1.prop.2]
  exact congrArg (fun f => f x y) h

theorem sourceRWW_invariant (p : localPullback) (r : BShort) (x y : MinusSpace) :
    sourceRWW sourceLatticeComparison (pullbackShort p r)
      (pullbackTensor p x) (pullbackTensor p y) = sourceRWW sourceLatticeComparison r x y := by
  have h : pull (sourceRWW sourceLatticeComparison) (pullbackShort p)
      (pullbackTensor p).toLinearMap (pullbackTensor p).toLinearMap =
        sourceRWW sourceLatticeComparison := by
    apply (shortBasis sourceLatticeComparison).ext
    intro i
    apply TensorProduct.ext'
    intro a v
    apply TensorProduct.ext'
    intro b w
    simp only [pull_apply, shortBasis_eq_vector]
    change sourceRWW sourceLatticeComparison
      (shortAction sourceLatticeComparison (pullbackCompatible p) _)
      (pullbackTensor p (a ⊗ₜ[ℝ] v)) (pullbackTensor p (b ⊗ₜ[ℝ] w)) = _
    rw [shortAction_vector, sourceRWW_vector, sourceRWW_vector,
      pullbackTensor_tmul, pullbackTensor_tmul, shortTensorBlock_tmul,
      shortTensorBlock_tmul, shortLiftTensor_action]
    change shortNaturalBlock
      (symmetricLeechRepresentation p.val.2 (shortLiftTensor sourceLatticeComparison _))
      (realLeechRepresentation p.val.2 a) (realLeechRepresentation p.val.2 b) *
      bothAxesDomain.form (SpinAction.imageRepresentation (p.val.1.val.2 _) (p.val.1.val.1 v))
        (p.val.1.val.1 w) / 8 = _
    rw [shortNaturalBlock_invariant, ← p.val.1.prop.1, p.val.1.prop.2]
  exact congrArg (fun f => f r x y) h

theorem symmetricBeta_invariant (g : Atlas.Lattices.LeechIsometryGroup)
    (A B D : SymmetricPart) :
    symmetricBeta (symmetricLeechRepresentation g A)
      (symmetricLeechRepresentation g B) (symmetricLeechRepresentation g D) =
      symmetricBeta A B D := by
  unfold symmetricBeta
  rw [symmetricLeechRepresentation_product, symmetricLeechRepresentation_form]

private theorem c_symmetric (g : C) (A B D : SymmetricPart) :
    symmetricBeta (cSymmetric g A) (cSymmetric g B) (cSymmetric g D) =
      symmetricBeta A B D := by
  obtain ⟨p,rfl⟩ := pullbackToC_surjective g
  simp only [cSymmetric_pullback]
  exact symmetricBeta_invariant p.val.2 A B D

private theorem c_short (g : C) (x y z : BShort) :
    shortCubic sourceLatticeComparison (cShort g x) (cShort g y) (cShort g z) =
      shortCubic sourceLatticeComparison x y z := by
  obtain ⟨p,rfl⟩ := pullbackToC_surjective g
  simp only [cShort_pullback]
  exact shortCubic_invariant sourceLatticeComparison (pullbackCompatible p) x y z

private theorem c_srr (g : C) (A : SymmetricPart) (x y : BShort) :
    sourceSRR sourceLatticeComparison (cSymmetric g A) (cShort g x) (cShort g y) =
      sourceSRR sourceLatticeComparison A x y := by
  obtain ⟨p,rfl⟩ := pullbackToC_surjective g
  simp only [cShort_pullback, cSymmetric_pullback]
  exact sourceSRR_invariant sourceLatticeComparison (pullbackCompatible p) A x y

private theorem c_sww (g : C) (A : SymmetricPart) (x y : MinusSpace) :
    sourceSWW (cSymmetric g A) (g.val x) (g.val y) = sourceSWW A x y := by
  obtain ⟨p,rfl⟩ := pullbackToC_surjective g
  rw [cSymmetric_pullback]
  exact sourceSWW_invariant p A x y

private theorem c_rww (g : C) (r : BShort) (x y : MinusSpace) :
    sourceRWW sourceLatticeComparison (cShort g r) (g.val x) (g.val y) =
      sourceRWW sourceLatticeComparison r x y := by
  obtain ⟨p,rfl⟩ := pullbackToC_surjective g
  rw [cShort_pullback]
  exact sourceRWW_invariant p r x y

/-- Aschbacher 28.13: the actual local group preserves all five cubic blocks. -/
theorem cRepresentation_beta (g : C) (x y z : GriessSpace) :
    griessBeta (cRepresentation g x) (cRepresentation g y) (cRepresentation g z) =
      griessBeta x y z := by
  simp only [griessBeta_components, cRepresentation_apply]
  apply congrArg₂ (· + ·)
  · apply congrArg₂ (· + ·)
    · apply congrArg₂ (· + ·)
      · exact congrArg₂ (· + ·) (c_symmetric g _ _ _) (c_short g _ _ _)
      · exact congrArg₂ (· + ·)
          (congrArg₂ (· + ·) (c_srr g _ _ _) (c_srr g _ _ _)) (c_srr g _ _ _)
    · exact congrArg₂ (· + ·)
        (congrArg₂ (· + ·) (c_sww g _ _ _) (c_sww g _ _ _)) (c_sww g _ _ _)
  · exact congrArg₂ (· + ·)
      (congrArg₂ (· + ·) (c_rww g _ _ _) (c_rww g _ _ _)) (c_rww g _ _ _)

end Sporadic.Monster.Construction.CInvariance
