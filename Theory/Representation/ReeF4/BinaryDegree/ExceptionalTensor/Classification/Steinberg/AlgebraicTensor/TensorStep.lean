module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Parameters
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor.RootOperators
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor.TensorStep.PolynomialExpansion
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# The exceptional tensor step from short-root density

For a short root, the exceptional endomorphism squares the parameter. The
first-degree coefficient on the tensor is therefore the first-factor root
coefficient tensored with the identity. Coefficient extraction preserves an
invariant subspace; density then gives every first-factor endomorphism.

A basis projection extracts a nonzero second-factor vector from any nonzero
invariant tensor subspace. The vectors whose tensors with every first-factor
vector lie in that subspace form a nonzero submodule of the second factor:
use the inverse first-factor action and surjectivity of the twist. Its
irreducibility forces the original tensor subspace to be the whole space.

This is the conditional one-step theorem. The short-root density theorem for
basic highest weights, iteration, and highest-weight identification remain
separate inputs to the full algebraic tensor theorem.

Sources: Steinberg, *Representations of Algebraic Groups* (1963), proof of
Theorem 5.1(3) and §11; GLS3, Theorem 2.8.5 and Remark 2.8.4.
-/

public section

open Theory.AlgebraicGroup
open scoped TensorProduct
namespace ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor
universe u v w
variable {F : Type u} [Field F] [IsAlgClosed F]
variable {V : Type v} [AddCommGroup V] [Module F V]
variable {W : Type w} [AddCommGroup W] [Module F W]

/-- The constant root coefficient is the identity, since the root parameter zero
is the identity point. -/
theorem RootExpansion.coeff_zero {ρ : RationalRepresentation (F4Chevalley.Carrier (k := F)) V}
    (p : RootExpansion ρ) (r : F4Chevalley.Root) : p.coeff r 0 = 1 := by
  have h := p.eval_eq r 0
  have hz : (p.coeff r).sum (fun n A => (0 : F) ^ n • A) = p.coeff r 0 := by
    rw [Finsupp.sum_eq_single 0]
    · simp
    · intro n _ hn
      simp [zero_pow hn]
    · simp
  rw [hz] at h
  have h0 : kPlusPoint (0 : F) = (1 : Variety.Point (KPlus F)) := by
    apply (additiveGroupPointEquiv F).injective
    rfl
  simpa [algebraicRootElement, h0] using h

private noncomputable def tensorCoeffs (p : ℕ →₀ Module.End F V)
    (q : ℕ →₀ Module.End F W) (d : ℕ) : ℕ →₀ Module.End F (V ⊗[F] W) :=
  p.sum fun i A => q.sum fun j B => Finsupp.single (i + d * j) (TensorProduct.map A B)

omit [IsAlgClosed F] in
private lemma tensorCoeffs_eval (p : ℕ →₀ Module.End F V)
    (q : ℕ →₀ Module.End F W) (d : ℕ) (t : F) :
    (tensorCoeffs p q d).sum (fun n A => t ^ n • A) =
      TensorProduct.map (p.sum fun i A => t ^ i • A)
        (q.sum fun j B => (t ^ d) ^ j • B) := by
  classical
  simp only [tensorCoeffs, Finsupp.sum_sum_index (fun n => smul_zero (t ^ n))
    (fun n A B => smul_add (t ^ n) A B), Finsupp.sum_single_index,
    smul_zero]
  apply TensorProduct.ext
  ext v w
  simp only [LinearMap.compr₂ₛₗ_apply, TensorProduct.mk_apply]
  simp only [Finsupp.sum, LinearMap.sum_apply, LinearMap.smul_apply,
    TensorProduct.map_tmul, TensorProduct.sum_tmul, TensorProduct.tmul_sum,
    TensorProduct.smul_tmul, TensorProduct.tmul_smul, Finset.smul_sum, smul_smul, pow_add, pow_mul]
  rw [Finset.sum_comm]
  simp only [mul_comm]

omit [IsAlgClosed F] in
private lemma tensorCoeffs_one (p : ℕ →₀ Module.End F V)
    (q : ℕ →₀ Module.End F W) :
    tensorCoeffs p q 2 1 = TensorProduct.map (p 1) (q 0) := by
  classical
  simp only [tensorCoeffs, Finsupp.sum_apply]
  have hin (i : ℕ) (A : Module.End F V) :
      q.sum (fun j B => (Finsupp.single (i + 2 * j) (TensorProduct.map A B)) 1) =
      if i = 1 then TensorProduct.map A (q 0) else 0 := by
    rw [Finsupp.sum_eq_single 0]
    · simp [Finsupp.single_apply]
    · intro j _ hj
      have h : i + 2 * j ≠ 1 := by omega
      simp [h]
    · simp
  simp_rw [hin]
  rw [Finsupp.sum_eq_single 1]
  · simp
  · intro i _ hi; simp [hi]
  · simp

private noncomputable def tensorStepAction (B C : AlgebraicFactor F) (ψ : Monoid.End (PointGroup F)) :
    RationalRepresentation (F4Chevalley.Carrier (k := F)) (B.Space ⊗[F] C.Space) :=
  ⟨(Representation.tprod (B.restrict (MonoidHom.id _)).ρ (C.restrict ψ).ρ).asGroupHom⟩

private noncomputable def tensorStepExpansion (B C : AlgebraicFactor F)
    (ψ : Monoid.End (PointGroup F)) (hψ : HasExceptionalRootFormula ψ)
    (p : RootExpansion B.action) (q : RootExpansion C.action) :
    RootExpansion (tensorStepAction B C ψ) := by
  classical
  exact {
    coeff r := tensorCoeffs (p.coeff r) (q.coeff (exceptionalRootPermutation r))
      (if IsLongRoot r then 1 else 2)
    eval_eq r t := by
      rw [tensorCoeffs_eval, p.eval_eq, q.eval_eq]
      change _ = (Representation.tprod (B.restrict (MonoidHom.id _)).ρ (C.restrict ψ).ρ) (algebraicRootElement r t)
      change _ = TensorProduct.map (B.action.action (algebraicRootElement r t)).val
        (C.action.action (ψ (algebraicRootElement r t))).val
      rw [hψ]
      congr 3
      by_cases hr : IsLongRoot r
      · simp [hr, exceptionalParameter_of_long hr]
      · simp [hr, exceptionalParameter_of_short hr]
  }

private theorem tensorStepExpansion_short (B C : AlgebraicFactor F)
    (ψ : Monoid.End (PointGroup F)) (hψ : HasExceptionalRootFormula ψ)
    (p : RootExpansion B.action) (q : RootExpansion C.action)
    (r : F4Chevalley.Root) (hr : ¬ IsLongRoot r) :
    (tensorStepExpansion B C ψ hψ p q).coeff r 1 =
      TensorProduct.map (p.coeff r 1) (LinearMap.id : Module.End F C.Space) := by
  simp only [tensorStepExpansion, if_neg hr, tensorCoeffs_one, q.coeff_zero]
  rfl


set_option backward.isDefEq.respectTransparency false in
private lemma separate (B C : AlgebraicFactor F) (ψ : Monoid.End (PointGroup F))
    (hψ : Function.Surjective ψ)
    (U : Subrepresentation (Representation.tprod (B.restrict (MonoidHom.id _)).ρ (C.restrict ψ).ρ))
    (hfirst : ∀ A : Module.End F B.Space, ∀ z ∈ U,
      TensorProduct.map A (LinearMap.id : Module.End F C.Space) z ∈ U) :
    U = ⊥ ∨ U = ⊤ := by
  classical
  by_cases hU : U = ⊥
  · exact Or.inl hU
  right
  let D : Submodule F C.Space :=
    { carrier := {w | ∀ v : B.Space, v ⊗ₜ[F] w ∈ U.toSubmodule}
      zero_mem' := by intro v; simp
      add_mem' := by
        intro w x hw hx v
        simpa only [TensorProduct.tmul_add] using U.toSubmodule.add_mem (hw v) (hx v)
      smul_mem' := by
        intro c w hw v
        simpa only [TensorProduct.tmul_smul] using U.toSubmodule.smul_mem c (hw v) }
  have hD : IsInvariantSubmodule C.action D := by
    intro g w hw v
    obtain ⟨x, rfl⟩ := hψ g
    have hm := U.apply_mem_toSubmodule x (hw ((B.action.action x⁻¹).val v))
    change TensorProduct.map (B.action.action x).val (C.action.action (ψ x)).val
      ((B.action.action x⁻¹).val v ⊗ₜ[F] w) ∈ U.toSubmodule at hm
    simpa [TensorProduct.map_tmul, ← Module.End.mul_apply, ← Units.val_mul,
      ← map_mul] using hm
  have hDbot : D ≠ ⊥ := by
    obtain ⟨z, hz, hnz⟩ := (Submodule.ne_bot_iff U.toSubmodule).mp
      (show U.toSubmodule ≠ ⊥ from fun h => hU (by ext; exact SetLike.ext_iff.mp h _))
    let b := Module.finBasis F B.Space
    let e := TensorProduct.equivFinsuppOfBasisLeft (N := C.Space) b
    have he : e z ≠ 0 := fun h => hnz (e.injective (h.trans (map_zero e).symm))
    obtain ⟨i, hi⟩ : ∃ i, e z i ≠ 0 := by
      by_contra! h
      exact he (Finsupp.ext h)
    have hd : e z i ∈ D := by
      intro v
      have hm := hfirst ((b.coord i).smulRight v) z hz
      have heq (x : B.Space ⊗[F] C.Space) :
          TensorProduct.map ((b.coord i).smulRight v) (LinearMap.id : Module.End F C.Space) x =
          v ⊗ₜ[F] e x i := by
        induction x using TensorProduct.induction_on with
        | zero => simp
        | tmul x y => simp [e, Module.Basis.coord_apply, TensorProduct.smul_tmul]
        | add x y hx hy => simp [hx, hy, TensorProduct.tmul_add]
      change TensorProduct.map ((b.coord i).smulRight v)
        (LinearMap.id : Module.End F C.Space) z ∈ U.toSubmodule at hm
      rwa [heq] at hm
    exact fun h => hi (by simpa [h] using hd)
  have htop : D = ⊤ := (C.irreducible.2 D hD).resolve_left hDbot
  apply Subrepresentation.toSubmodule_injective
  apply top_unique
  have hall : ∀ z : B.Space ⊗[F] C.Space, z ∈ U.toSubmodule := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => exact U.toSubmodule.zero_mem
    | tmul v w => exact (show w ∈ D by rw [htop]; trivial) v
    | add x y hx hy => exact U.toSubmodule.add_mem hx hy
  intro z _
  exact hall z


set_option backward.isDefEq.respectTransparency false in
private theorem first_factor_stable (B C : AlgebraicFactor F)
    (ψ : Monoid.End (PointGroup F)) (hψ : HasExceptionalRootFormula ψ)
    (p : RootExpansion B.action) (q : RootExpansion C.action) (hp : p.HasShortRootDensity)
    (U : Subrepresentation (Representation.tprod (B.restrict (MonoidHom.id _)).ρ (C.restrict ψ).ρ)) :
    ∀ A : Module.End F B.Space, ∀ z ∈ U,
      TensorProduct.map A (LinearMap.id : Module.End F C.Space) z ∈ U := by
  let f := Module.End.rTensorAlgHom F B.Space C.Space
  have hU : IsInvariantSubmodule (tensorStepAction B C ψ) U.toSubmodule := by
    intro g z hz
    change (((Representation.tprod (B.restrict (MonoidHom.id _)).ρ
      (C.restrict ψ).ρ).asGroupHom g).val z) ∈ U.toSubmodule
    rw [Representation.asGroupHom_apply]
    exact U.apply_mem_toSubmodule g hz
  have hgen (r : {r : F4Chevalley.Root // ¬ IsLongRoot r}) :
      ∀ z ∈ U, f (p.coeff r.val 1) z ∈ U := by
    intro z hz
    have hm := (tensorStepExpansion B C ψ hψ p q).coeff_mem U.toSubmodule hU r.val 1 hz
    rw [tensorStepExpansion_short B C ψ hψ p q r.val r.property] at hm
    exact hm
  intro A
  change ∀ z ∈ U.toSubmodule, f A z ∈ U.toSubmodule
  have hA : A ∈ Algebra.adjoin F (Set.range fun r : {r : F4Chevalley.Root // ¬ IsLongRoot r} =>
      p.coeff r.val 1) := by rw [hp]; trivial
  induction hA using Algebra.adjoin_induction with
  | mem A hA => obtain ⟨r, rfl⟩ := hA; exact hgen r
  | algebraMap a =>
      intro z hz
      simpa only [AlgHom.commutes, Module.algebraMap_end_apply] using U.toSubmodule.smul_mem a hz
  | add A D _ _ hA hD =>
      intro z hz
      simpa only [map_add, LinearMap.add_apply] using U.toSubmodule.add_mem (hA z hz) (hD z hz)
  | mul A D _ _ hA hD =>
      intro z hz
      simpa only [map_mul, Module.End.mul_apply] using hA (f D z) (hD z hz)

set_option backward.isDefEq.respectTransparency false in
/-- The exceptional tensor step: short-root density on the first factor and
surjectivity of the exceptional endomorphism imply irreducibility of the whole
tensor. The basic highest-weight theory supplying density is a separate input. -/
theorem tensorStep_irreducible [CharP F 2] (B C : AlgebraicFactor F)
    (Ψ : Theory.AlgebraicGroup.Morphism (F4Chevalley.Carrier (k := F))
      (F4Chevalley.Carrier (k := F)))
    (ψ : Monoid.End (PointGroup F)) (hΨ : Ψ.onPoints = ψ)
    (hsurj : Function.Surjective ψ) (hroot : HasExceptionalRootFormula ψ)
    (p : RootExpansion B.action) (hp : p.HasShortRootDensity) :
    Representation.IsIrreducible
      (Representation.tprod (B.restrict (MonoidHom.id _)).ρ (C.restrict ψ).ρ) := by
  subst ψ
  obtain ⟨q⟩ := rootExpansion_nonempty C.action C.irreducible.1
  apply (isSimpleOrder_iff _).mpr
  refine ⟨?_, fun U => separate B C Ψ.onPoints hsurj U
    (first_factor_stable B C Ψ.onPoints hroot p q hp U)⟩
  refine ⟨⟨⊥, ⊤, ?_⟩⟩
  intro h
  have he := congrArg Subrepresentation.toSubmodule h
  exact (bot_ne_top : (⊥ : Submodule F (B.Space ⊗[F] C.Space)) ≠ ⊤) he

end ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor
