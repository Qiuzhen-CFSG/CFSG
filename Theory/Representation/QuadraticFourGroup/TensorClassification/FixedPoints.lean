module

public import Theory.Representation.QuadraticFourGroup.TensorClassification.ExternalTensor
public import Theory.Representation.EndFieldRep

/-!
# Cubic fixed-point conditions through scalar extension and tensor factors

An element is fixed-point free precisely when its action minus the identity
is injective. Flatness preserves this condition under field extension. The
Schur-field action has the same underlying additive action, and a tensor
fixed vector in either factor would give one in the external tensor.

These transfers connect GLS2 Theorem 25.14, Step 4 to the natural-module
classification in Step 5. No irreducibility of a binary scalar extension
or tensor decomposition is assumed by the transfer lemmas.
-/

@[expose] public section

open scoped TensorProduct MonoidAlgebra
namespace Representation.QuadraticFourGroup.TensorClassification

variable {k G V W : Type*} [Field k] [Monoid G]
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]

/-- The action of one element has zero fixed space. -/
def FixedPointFreeAt (ρ : Representation k G V) (g : G) : Prop :=
  ∀ v, ρ g v = v → v = 0

/-- Every element of order three has zero fixed space. -/
def CubicFixedPointFree (ρ : Representation k G V) : Prop :=
  ∀ g, orderOf g = 3 → FixedPointFreeAt ρ g

/-- The cubic fixed-point condition on each embedded direct factor. -/
def CubicFreeOnFactors {H : Type*} [Monoid H]
    (ρ : Representation k (G × H) V) : Prop :=
  (∀ g, orderOf g = 3 → FixedPointFreeAt ρ (g,1)) ∧
  (∀ h, orderOf h = 3 → FixedPointFreeAt ρ (1,h))

theorem fixedPointFreeAt_iff_injective_sub_one (ρ : Representation k G V) (g : G) :
    FixedPointFreeAt ρ g ↔ Function.Injective (ρ g - (1 : Module.End k V)) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  simp only [FixedPointFreeAt, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]

theorem FixedPointFreeAt.of_equiv {ρ : Representation k G V} {σ : Representation k G W}
    {g : G} (h : FixedPointFreeAt ρ g) (e : ρ.Equiv σ) : FixedPointFreeAt σ g := by
  intro w hw
  obtain ⟨v, rfl⟩ := e.toLinearEquiv.surjective w
  have hv : ρ g v = v := e.toLinearEquiv.injective (by
    calc
      e (ρ g v) = σ g (e v) := Representation.IntertwiningMap.isIntertwining ρ σ
        e.toIntertwiningMap g v
      _ = e v := hw)
  rw [h v hv]
  exact map_zero e.toLinearEquiv

theorem FixedPointFreeAt.extendScalars {ρ : Representation k G V} {g : G}
    (h : FixedPointFreeAt ρ g) (F : Type*) [Field F] [Algebra k F] :
    FixedPointFreeAt (extendScalars F ρ) g := by
  apply (fixedPointFreeAt_iff_injective_sub_one _ _).mpr
  have hf := Module.Flat.lTensor_preserves_injective_linearMap (M := F) (ρ g - 1)
    ((fixedPointFreeAt_iff_injective_sub_one _ _).mp h)
  simpa only [← LinearMap.baseChange_eq_ltensor, LinearMap.baseChange_sub,
    LinearMap.baseChange_one, extendScalars_apply] using hf

theorem FixedPointFreeAt.endFieldRep [Finite k] [FiniteDimensional k V]
    {ρ : Representation k G V} [ρ.IsIrreducible] {g : G}
    (h : FixedPointFreeAt ρ g) : FixedPointFreeAt ρ.endFieldRep g := by
  intro v hv
  apply ρ.asModuleEquiv.injective
  change ρ.asModuleEquiv v = ρ.asModuleEquiv 0
  rw [map_zero]
  apply h
  exact congrArg ρ.asModuleEquiv hv

theorem CubicFixedPointFree.of_equiv {ρ : Representation k G V} {σ : Representation k G W}
    (h : CubicFixedPointFree ρ) (e : ρ.Equiv σ) : CubicFixedPointFree σ :=
  fun g hg => (h g hg).of_equiv e

theorem CubicFreeOnFactors.of_equiv {H : Type*} [Monoid H]
    {ρ : Representation k (G × H) V} {σ : Representation k (G × H) W}
    (h : CubicFreeOnFactors ρ) (e : ρ.Equiv σ) : CubicFreeOnFactors σ :=
  ⟨fun g hg => (h.1 g hg).of_equiv e, fun g hg => (h.2 g hg).of_equiv e⟩

theorem CubicFreeOnFactors.extendScalars {H : Type*} [Monoid H]
    {ρ : Representation k (G × H) V} (h : CubicFreeOnFactors ρ)
    (F : Type*) [Field F] [Algebra k F] : CubicFreeOnFactors (extendScalars F ρ) :=
  ⟨fun g hg => (h.1 g hg).extendScalars F, fun g hg => (h.2 g hg).extendScalars F⟩

theorem CubicFreeOnFactors.endFieldRep {H : Type*} [Monoid H]
    [Finite k] [FiniteDimensional k V] {ρ : Representation k (G × H) V}
    [ρ.IsIrreducible] (h : CubicFreeOnFactors ρ) : CubicFreeOnFactors ρ.endFieldRep :=
  ⟨fun g hg => (h.1 g hg).endFieldRep, fun g hg => (h.2 g hg).endFieldRep⟩

theorem FixedPointFreeAt.left_of_externalTensor {H : Type*} [Monoid H] [Nontrivial W]
    {ρ : Representation k G V} {σ : Representation k H W} {g : G}
    (h : FixedPointFreeAt (externalTensor ρ σ) (g,1)) : FixedPointFreeAt ρ g := by
  obtain ⟨w, hw⟩ := exists_ne (0 : W)
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one k hw
  intro v hv
  have ht : v ⊗ₜ[k] w = 0 := h _ (by
    simp only [externalTensor_apply, map_one, TensorProduct.map_tmul, hv,
      Module.End.one_apply])
  have hc := congrArg (fun z => _root_.TensorProduct.rid k V
    (TensorProduct.map (LinearMap.id : V →ₗ[k] V) f z)) ht
  simpa [hf] using hc

theorem FixedPointFreeAt.right_of_externalTensor {H : Type*} [Monoid H] [Nontrivial V]
    {ρ : Representation k G V} {σ : Representation k H W} {g : H}
    (h : FixedPointFreeAt (externalTensor ρ σ) (1,g)) : FixedPointFreeAt σ g := by
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one k hv
  intro w hw
  have ht : v ⊗ₜ[k] w = 0 := h _ (by
    simp only [externalTensor_apply, map_one, TensorProduct.map_tmul, hw,
      Module.End.one_apply])
  have hc := congrArg (fun z => _root_.TensorProduct.lid k W
    (TensorProduct.map f (LinearMap.id : W →ₗ[k] W) z)) ht
  simpa [hf] using hc

theorem CubicFreeOnFactors.factors {H : Type*} [Monoid H] [Nontrivial V] [Nontrivial W]
    {ρ : Representation k G V} {σ : Representation k H W}
    (h : CubicFreeOnFactors (externalTensor ρ σ)) :
    CubicFixedPointFree ρ ∧ CubicFixedPointFree σ :=
  ⟨fun g hg => (h.1 g hg).left_of_externalTensor,
    fun g hg => (h.2 g hg).right_of_externalTensor⟩

end Representation.QuadraticFourGroup.TensorClassification

end
