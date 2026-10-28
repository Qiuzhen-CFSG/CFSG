module

public import Theory.Representation.SymplecticFourOrthogonalCover
public import Theory.Representation.FirstCohomologySymplecticFour
public import Theory.Representation.FirstCohomologyDuality.QuotientGeometry
public import Mathlib.Algebra.Algebra.ZMod

/-!
# The universal binary orthogonal cover of Sp₄(K)′

Compose the nondegenerate natural polar pairing with a binary linear
functional taking 1 to 1. This gives equivariant binary self-duality on the
literal derived natural representation. The completed binary and nonbinary
cocycle normal forms then give the dual H¹ dimension: the binary degree of K.
It equals the dimension of the orthogonal cover's central kernel.

The maximal-kernel comparison therefore identifies the five-space with the
cohomological universal binary L-cover, equivariantly and over the original
projection. Every finite-dimensional binary L-cover is its quotient; its
kernel need not carry an additional K-module structure. All statements here
include K = F₂ and use the actual derived group.

Source: Aschbacher–Smith, Remark I.1.5 and Lemmas I.1.6(5), I.2.3(1),
printed pp.408, 413 of the combined manuscript (1 March 2004).
-/

public section

noncomputable section
namespace Representation.SymplecticFourOrthogonalCover
open Matrix ClassicalOrthogonal Representation.OneCohomology
variable {K : Type*} [Field K] [Finite K] [CharP K 2]

lemma polar_invariant (g : L (K := K)) (v w : Natural (K := K)) :
    (formD 2 K).polarBilin (symplecticDerivedNatural 2 g v)
      (symplecticDerivedNatural 2 g w) = (formD 2 K).polarBilin v w := by
  have hp : (formB 2 K).polarBilin (action g (v, 0)) (action g (w, 0)) =
      (formB 2 K).polarBilin (v, 0) (w, 0) := by
    simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar,
      ← map_add, action_preserves]
  simpa only [polarB_apply, action_apply, symplecticDerivedNatural_apply,
    CharTwo.two_eq_zero, zero_mul, add_zero] using hp

section Binary
variable [Algebra (ZMod 2) K]
abbrev binaryNatural : Representation (ZMod 2) (L (K := K)) (Natural (K := K)) :=
  restrictScalars (symplecticDerivedNatural 2)
abbrev binaryAction : Representation (ZMod 2) (L (K := K)) (Space (K := K)) :=
  restrictScalars action

@[expose] def binaryProjection : binaryAction.IntertwiningMap (binaryNatural (K := K)) :=
  restrictCoverMap (k := ZMod 2) projection

omit [Finite K] in
/-- The binary natural module remains fixed-point-free on the genuine derived group. -/
lemma binary_natural_fixed : fixed (binaryNatural (K := K)) = ⊥ := by
  apply bot_unique
  intro v hv
  exact (natural_fixed (K := K)).le hv

omit [Finite K] in
/-- The fixed space of any binary cover is its literal central kernel. -/
lemma cover_fixed_kernel
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    {σ : Representation (ZMod 2) (L (K := K)) W}
    (p : σ.IntertwiningMap (binaryNatural (K := K))) (hp : IsCover p) :
    fixed σ = p.toLinearMap.ker := by
  apply le_antisymm _ hp.2.1
  intro w hw
  have h : p w ∈ fixed (binaryNatural (K := K)) := by
    intro g
    rw [← p.isIntertwining, hw g]
  exact (binary_natural_fixed (K := K)).le h

lemma binaryProjection_isCover : IsCover (binaryProjection (K := K)) :=
  isCover_restrictScalars (k := ZMod 2) (projection (K := K)) projection_isCover

private def fieldFunctional : K →ₗ[ZMod 2] ZMod 2 :=
  Classical.choose (Module.Projective.exists_dual_eq_one (ZMod 2) (one_ne_zero : (1 : K) ≠ 0))
omit [Finite K] [CharP K 2] in
private lemma fieldFunctional_one : fieldFunctional (1 : K) = 1 :=
  Classical.choose_spec (Module.Projective.exists_dual_eq_one (ZMod 2) (one_ne_zero : (1 : K) ≠ 0))

def binaryPairing : Natural (K := K) →ₗ[ZMod 2] Module.Dual (ZMod 2) (Natural (K := K)) where
  toFun v := (fieldFunctional (K := K)).comp (((formD 2 K).polarBilin v).restrictScalars (ZMod 2))
  map_add' v w := by
    apply LinearMap.ext
    intro x
    change fieldFunctional ((formD 2 K).polarBilin (v + w) x) = _
    simp only [map_add, LinearMap.add_apply]
    rfl
  map_smul' c v := by
    apply LinearMap.ext
    intro w
    change fieldFunctional ((formD 2 K).polarBilin (c • v) w) = _
    rw [LinearMap.map_smul_of_tower, LinearMap.smul_apply, map_smul]
    rfl

omit [Finite K] [CharP K 2] in
lemma binaryPairing_injective : Function.Injective (binaryPairing (K := K)) := by
  apply LinearMap.ker_eq_bot.mp
  apply bot_unique
  intro v hv
  change v = 0
  apply polarD_separating
  intro w
  by_contra hn
  have h := LinearMap.congr_fun hv (((formD 2 K).polarBilin v w)⁻¹ • w)
  change fieldFunctional ((formD 2 K).polarBilin v (((formD 2 K).polarBilin v w)⁻¹ • w)) = 0 at h
  rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hn, fieldFunctional_one] at h
  exact one_ne_zero h

def binarySelfDual : Natural (K := K) ≃ₗ[ZMod 2] Module.Dual (ZMod 2) (Natural (K := K)) :=
  LinearEquiv.ofBijective binaryPairing ⟨binaryPairing_injective,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (Subspace.dual_finrank_eq (K := ZMod 2) (V := Natural (K := K))).symm).mp binaryPairing_injective⟩

lemma binarySelfDual_equivariant (g : L (K := K)) (v : Natural (K := K)) :
    (binarySelfDual (K := K)) ((binaryNatural (K := K)) g v) =
      (binaryNatural (K := K)).dual g ((binarySelfDual (K := K)) v) := by
  apply LinearMap.ext
  intro w
  change fieldFunctional ((formD 2 K).polarBilin (symplecticDerivedNatural 2 g v) w) =
    fieldFunctional ((formD 2 K).polarBilin v (symplecticDerivedNatural 2 g⁻¹ w))
  apply congrArg fieldFunctional
  have h := polar_invariant g v (symplecticDerivedNatural 2 g⁻¹ w)
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] at h
  exact h

lemma binary_dual_H1_finrank :
    Module.finrank (ZMod 2) (H1 (binaryNatural (K := K)).dual) = Module.finrank (ZMod 2) K := by
  let e := H1Congr (binaryNatural (K := K)) (binaryNatural (K := K)).dual (MulEquiv.refl _)
    (binarySelfDual (K := K)) (fun g v => binarySelfDual_equivariant g v)
  rw [← e.finrank_eq, finrank_restrictScalars, SymplecticFour.finrank_H1_eq_one, mul_one]

lemma binary_kernel_finrank :
    Module.finrank (ZMod 2) (binaryProjection (K := K)).toLinearMap.ker = Module.finrank (ZMod 2) K := by
  have he : (binaryProjection (K := K)).toLinearMap.ker =
      ((projection (K := K)).toLinearMap.ker).restrictScalars (ZMod 2) := rfl
  rw [he, projection_kernel,
    ((Submodule.restrictScalarsEquiv (ZMod 2) K (Space (K := K)) radical).restrictScalars (ZMod 2)).finrank_eq]
  exact ((radicalEquiv (K := K)).restrictScalars (ZMod 2)).finrank_eq

/-- The model is the universal binary L-cover over the original natural projection. -/
lemma universal_equiv :
    ∃ e : Module.Dual (ZMod 2) (cocycles (binaryNatural (K := K)).dual) ≃ₗ[ZMod 2] Space (K := K),
      (∀ g u, e ((universalAction (binaryNatural (K := K)).dual).dual g u) = binaryAction g (e u)) ∧
      ∀ u, binaryProjection (e u) = universalCoverProjection (binaryNatural (K := K)) u := by
  exact exists_equiv_universalCover_of_finrank_ker_eq (k := ZMod 2)
    (ρ := binaryNatural (K := K)) (σ := binaryAction (K := K))
    (binaryProjection (K := K)) binaryProjection_isCover
    (binary_kernel_finrank.trans binary_dual_H1_finrank.symm)

/-- Every binary L-cover is a quotient of this explicit model over its original projection. -/
lemma exists_cover_quotient
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    {σ : Representation (ZMod 2) (L (K := K)) W}
    (p : σ.IntertwiningMap (binaryNatural (K := K))) (hp : IsCover p) :
    ∃ f : binaryAction.IntertwiningMap σ, Function.Surjective f ∧
      ∀ v, p (f v) = binaryProjection v :=
  exists_quotient_of_finrank_ker_eq (k := ZMod 2)
    (ρ := binaryNatural (K := K)) (σ := binaryAction (K := K))
    (binaryProjection (K := K)) binaryProjection_isCover
    (binary_kernel_finrank.trans binary_dual_H1_finrank.symm) p hp
end Binary
end Representation.SymplecticFourOrthogonalCover
