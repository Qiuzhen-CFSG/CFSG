module

public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.RingTheory.TwoSidedIdeal.Operations
public import Mathlib.RingTheory.TwoSidedIdeal.Kernel
public import Mathlib.RingTheory.Ideal.Maps
/-!
# A nilpotent-kernel criterion for equivalence of irreducible representations

A two-sided ideal whose triple products act as zero annihilates every
irreducible module: its common annihilator is invariant, and the zero case
can be peeled three times. If the reference representation spans its full
endomorphism algebra, kernel containment then produces an equivalence.
The latter proof descends the second action to the endomorphism algebra
and constructs a nonzero intertwiner using a rank-one operator.

The concrete consumer is the normalized M₁₁ involution problem associated
with the James input in Aschbacher--Smith G.7.3(2), printed p.348 (PDF
p.359). This module has no Mathieu classification premise or character-table
input. The finite algebra certificate is a separate obligation.
-/

public section
open scoped MonoidAlgebra
namespace Representation.MathieuSmall.M12Recognition.PointClassification.NormalizedInvolution
variable {k G V W : Type*} [Field k] [Group G]
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]

/-- A two-sided ideal with zero triple products annihilates an irreducible action. -/
theorem kernel_le_of_cube (τ : Representation k G W) [τ.IsIrreducible]
    (J : TwoSidedIdeal k[G])
    (hcube : ∀ x ∈ J, ∀ y ∈ J, ∀ z ∈ J, τ.asAlgebraHom (x*y*z) = 0) :
    J ≤ TwoSidedIdeal.ker τ.asAlgebraHom := by
  let U : Subrepresentation τ := {
    toSubmodule := {
      carrier := {v | ∀ x ∈ J, τ.asAlgebraHom x v = 0}
      zero_mem' := by simp
      add_mem' := by intro v w hv hw x hx; simp [map_add, hv x hx, hw x hx]
      smul_mem' := by intro c v hv x hx; simp [map_smul, hv x hx] }
    apply_mem_toSubmodule := by
      intro g v hv x hx
      have he := hv (x * MonoidAlgebra.single g 1) (J.mul_mem_right _ _ hx)
      simpa only [map_mul, Representation.asAlgebraHom_single_one,
        Module.End.mul_apply] using he }
  rcases eq_bot_or_eq_top U with hU | hU
  · have kill (v : W) (hv : ∀ x ∈ J, τ.asAlgebraHom x v = 0) : v = 0 := by
      have hm : v ∈ U := hv
      rwa [hU] at hm
    have htwo (y : k[G]) (hy : y ∈ J) (z : k[G]) (hz : z ∈ J) (v : W) :
        τ.asAlgebraHom y (τ.asAlgebraHom z v) = 0 := by
      apply kill
      intro x hx
      have he := LinearMap.congr_fun (hcube x hx y hy z hz) v
      simpa only [map_mul, Module.End.mul_apply, LinearMap.zero_apply] using he
    intro z hz
    change τ.asAlgebraHom z = 0
    apply LinearMap.ext
    intro v
    exact kill _ (fun y hy => htwo y hy z hz v)
  · intro x hx
    change τ.asAlgebraHom x = 0
    apply LinearMap.ext
    intro v
    have hv : v ∈ U := hU.symm ▸ (show v ∈ (⊤ : Subrepresentation τ) from by trivial)
    exact hv x hx

private noncomputable def descend (σ : Representation k G V) (τ : Representation k G W)
    (hs : Function.Surjective σ.asAlgebraHom)
    (hk : TwoSidedIdeal.ker σ.asAlgebraHom ≤ TwoSidedIdeal.ker τ.asAlgebraHom) :
    Module.End k V →ₐ[k] Module.End k W := by
  let f := σ.asAlgebraHom.toRingHom
  let g := τ.asAlgebraHom.toRingHom
  have hk' : RingHom.ker f ≤ RingHom.ker g := hk
  let d := f.liftOfSurjective hs ⟨g, hk'⟩
  refine { toRingHom := d, commutes' := ?_ }
  intro c
  have he := f.liftOfSurjective_comp_apply hs ⟨g, hk'⟩ (algebraMap k k[G] c)
  change d (σ.asAlgebraHom (algebraMap k k[G] c)) =
    τ.asAlgebraHom (algebraMap k k[G] c) at he
  change d (algebraMap k (Module.End k V) c) = algebraMap k (Module.End k W) c
  simpa only [AlgHom.commutes] using he

private theorem descend_apply (σ : Representation k G V) (τ : Representation k G W)
    (hs : Function.Surjective σ.asAlgebraHom)
    (hk : TwoSidedIdeal.ker σ.asAlgebraHom ≤ TwoSidedIdeal.ker τ.asAlgebraHom)
    (x : k[G]) : descend σ τ hs hk (σ.asAlgebraHom x) = τ.asAlgebraHom x := by
  unfold descend
  exact RingHom.liftOfSurjective_comp_apply σ.asAlgebraHom.toRingHom hs
    ⟨τ.asAlgebraHom.toRingHom, hk⟩ x

private noncomputable def rankOneIntertwiner (σ : Representation k G V) (τ : Representation k G W)
    (d : Module.End k V →ₐ[k] Module.End k W) (hd : ∀ g, d (σ g) = τ g)
    (l : V →ₗ[k] k) (w : W) : σ.IntertwiningMap τ where
  toLinearMap := (LinearMap.applyₗ w).comp (d.toLinearMap.comp (LinearMap.smulRightₗ l))
  isIntertwining' g := by
    apply LinearMap.ext
    intro v
    change d (l.smulRight (σ g v)) w = τ g (d (l.smulRight v) w)
    have he : l.smulRight (σ g v) = σ g * l.smulRight v := by
      ext x
      simp only [LinearMap.smulRight_apply, Module.End.mul_apply, map_smul]
    rw [he, map_mul, hd, Module.End.mul_apply]

/-- A full reference matrix algebra and containment of annihilators identify simple modules. -/
theorem equiv_of_kernel_le [FiniteDimensional k V] [Nontrivial W]
    (σ : Representation k G V) (τ : Representation k G W)
    [σ.IsIrreducible] [τ.IsIrreducible]
    (hs : Function.Surjective σ.asAlgebraHom)
    (hk : TwoSidedIdeal.ker σ.asAlgebraHom ≤ TwoSidedIdeal.ker τ.asAlgebraHom) :
    Nonempty (σ.Equiv τ) := by
  classical
  let d := descend σ τ hs hk
  have hd (g : G) : d (σ g) = τ g := by
    simpa only [Representation.asAlgebraHom_single_one] using
      descend_apply σ τ hs hk (MonoidAlgebra.single g 1)
  let b := Module.finBasis k V
  have hone : (∑ i, (b.coord i).smulRight (b i)) = (1 : Module.End k V) := by
    apply LinearMap.ext
    intro v
    simpa only [LinearMap.sum_apply, LinearMap.smulRight_apply, Module.Basis.coord_apply,
      Module.End.one_apply] using b.sum_repr v
  obtain ⟨w, hw⟩ := exists_ne (0 : W)
  have hex : ∃ i, d ((b.coord i).smulRight (b i)) w ≠ 0 := by
    by_contra! h
    have he := congrArg (fun f : Module.End k W => f w) (congrArg d hone)
    simp only [map_sum, map_one, LinearMap.sum_apply, Module.End.one_apply, h,
      Finset.sum_const_zero] at he
    exact hw he.symm
  obtain ⟨i, hi⟩ := hex
  let f := rankOneIntertwiner σ τ d hd (b.coord i) w
  have hf : f ≠ 0 := by
    intro he
    have hh := DFunLike.congr_fun he (b i)
    exact hi hh
  exact ⟨f.ofBijective ((Representation.IsIrreducible.bijective_or_eq_zero f).resolve_right hf)⟩
end Representation.MathieuSmall.M12Recognition.PointClassification.NormalizedInvolution
