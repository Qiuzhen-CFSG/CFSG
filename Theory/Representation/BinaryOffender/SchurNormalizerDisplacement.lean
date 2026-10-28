module

public import Theory.Representation.BinaryOffender.NormalizerExtension
public import Theory.Representation.BinaryOffender.NaturalTensorFixedCodimension.Basic
public import Theory.Representation.EndFieldRep

/-!
# Displacement of a nontrivial action on the Schur field

An invertible normalizer conjugates the ring of intertwining endomorphisms.
If this action is nontrivial, choose an endomorphism `f` with nonzero difference
`T f T⁻¹ - f`. Schur's lemma makes that difference injective. On fixed vectors
it equals `(T - 1) f`, embedding the fixed space in the displacement space.
Thus the actor moves at least half the binary dimension.

The definition of Schur linearity is also identified with linearity for the
existing endomorphism-field action on `ρ.asModule`. No absolute-irreducibility
or coefficient-linearity assumption is made on the full normalizer.

Source: the scalar and induced-constituent distinction in Guralnick–Malle,
Classification of 2F-modules II, §3.5, equations (3.3)–(3.5), manuscript p.20.
The G₂ application is in Chapter K's `G2CubicDegree.TensorWindow`.
-/

public section
open scoped MonoidAlgebra
open Representation
open Representation.BinaryOffender
open Subgroup

namespace Representation.BinaryOffender.SchurNormalizer
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

private def conjugate (t : linearNormalizer ρ) (f : IntertwiningMap ρ ρ) :
    IntertwiningMap ρ ρ where
  toLinearMap := t.val.val * f.toLinearMap * (↑t.val⁻¹ : Module.End (ZMod 2) V)
  isIntertwining' := by
    intro g
    obtain ⟨h, hh⟩ := (Subgroup.mem_normalizer_iff''.mp t.property
      (ρ.asGroupHom g)).mp ⟨g, rfl⟩
    have he : ρ h = (↑t.val⁻¹ : Module.End (ZMod 2) V) * ρ g * t.val.val :=
      congrArg Units.val hh
    have hf : f.toLinearMap * ρ h = ρ h * f.toLinearMap := f.isIntertwining' h
    have hc := congrArg (fun a : Module.End (ZMod 2) V =>
      t.val.val * a * (↑t.val⁻¹ : Module.End (ZMod 2) V)) hf
    change (_ * _ * _) * ρ g = ρ g * (_ * _ * _)
    simpa [he, mul_assoc] using hc

/-- The literal actor commutes with every element of its component's Schur ring. -/
@[expose] def IsSchurLinear (t : linearNormalizer ρ) : Prop :=
  ∀ (f : IntertwiningMap ρ ρ) (v : V), t.val.val (f v) = f (t.val.val v)

private theorem conjugate_ne_of_not_schurLinear (t : linearNormalizer ρ)
    (h : ¬ IsSchurLinear ρ t) : ∃ f, conjugate ρ t f ≠ f := by
  by_contra! hh
  apply h
  intro f v
  have he := congrArg (fun a : IntertwiningMap ρ ρ => a (t.val.val v)) (hh f)
  change t.val.val (f ((↑t.val⁻¹ : Module.End (ZMod 2) V) (t.val.val v))) = _ at he
  simpa [← Module.End.mul_apply] using he

/-- A nontrivial action on the Schur field moves at least half the binary space. -/
theorem finrank_le_twice_fixedCodim [FiniteDimensional (ZMod 2) V]
    [IsIrreducible ρ] (t : linearNormalizer ρ) (h : ¬ IsSchurLinear ρ t) :
    Module.finrank (ZMod 2) V ≤
      2 * fixedCodim (normalizerRepresentation ρ) (zpowers t) := by
  obtain ⟨f, hf⟩ := conjugate_ne_of_not_schurLinear ρ t h
  let δ := conjugate ρ t f - f
  have hδ : Function.Injective δ :=
    (IsIrreducible.injective_or_eq_zero δ).resolve_right (sub_ne_zero.mpr hf)
  let T := t.val.val
  let K := LinearMap.ker (T - 1)
  let q : K →ₗ[ZMod 2] LinearMap.range (T - 1) :=
    ((T - 1).comp (f.toLinearMap.comp K.subtype)).codRestrict _
      (fun v => ⟨f v, rfl⟩)
  have he (v : K) : (q v : V) = δ v := by
    have hv : T (v : V) = v := sub_eq_zero.mp v.property
    have hv' : (↑t.val⁻¹ : Module.End (ZMod 2) V) (v : V) = v := by
      rw [← hv]
      change ((↑t.val⁻¹ : Module.End (ZMod 2) V) * t.val.val) v = T v
      simpa using hv.symm
    change T (f v) - f v = T (f ((↑t.val⁻¹ : Module.End (ZMod 2) V) v)) - f v
    rw [hv']
  have hq : Function.Injective q := by
    intro x y hxy
    apply Subtype.ext
    apply hδ
    simpa only [he] using congrArg Subtype.val hxy
  have hb := LinearMap.finrank_le_finrank_of_injective hq
  dsimp only [K] at hb
  have hd := (T - 1).finrank_range_add_finrank_ker
  have hm := NaturalTensor.operatorFixedCodim_le_fixedCodim
    (normalizerRepresentation ρ) (zpowers t) (mem_zpowers t)
  change Module.finrank (ZMod 2) (LinearMap.range (T - 1)) ≤ _ at hm
  calc
    Module.finrank (ZMod 2) V =
        Module.finrank (ZMod 2) (LinearMap.range (T - 1)) +
          Module.finrank (ZMod 2) (LinearMap.ker (T - 1)) := hd.symm
    _ ≤ fixedCodim (normalizerRepresentation ρ) (zpowers t) +
          fixedCodim (normalizerRepresentation ρ) (zpowers t) :=
      Nat.add_le_add hm (hb.trans hm)
    _ = 2 * fixedCodim (normalizerRepresentation ρ) (zpowers t) := by omega

/-- This is linearity over the actual endomorphism field, on its existing carrier. -/
theorem isSchurLinear_iff_endField (t : linearNormalizer ρ) :
    IsSchurLinear ρ t ↔
      ∀ (c : Module.End (ZMod 2)[G] ρ.asModule) (v : ρ.asModule),
        t.val.val (ρ.asModuleEquiv (c • v)) =
          ρ.asModuleEquiv (c • ρ.asModuleEquiv.symm (t.val.val (ρ.asModuleEquiv v))) := by
  constructor
  · intro h c v
    exact h ((IntertwiningMap.equivAlgEnd ρ).symm c) (ρ.asModuleEquiv v)
  · intro h f v
    exact h (IntertwiningMap.equivAlgEnd ρ f) (ρ.asModuleEquiv.symm v)

end Representation.BinaryOffender.SchurNormalizer
