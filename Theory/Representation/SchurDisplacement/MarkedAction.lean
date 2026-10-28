module

public import Theory.Representation.SchurDisplacement
public import Theory.Representation.EndFieldRep
public import Theory.GroupAction.AutomorphismFixedTransport

/-!
# Schur-linear actors on a marked layer

An ambient actor commuting with the literal layer endomorphisms acts linearly
on the endomorphism-ring module for any isomorphic marking of that layer.
Transport each intertwining map through the marking to prove scalar linearity;
the representation law gives the exact conjugation intertwining equation.
This avoids identifying two endomorphism fields merely by their degrees.

The binary SL₂ application is in `Theory.Representation.SL2.SchurOuterPeriod`.
Source: the Schur-field and extendability argument in Guralnick--Malle,
Classification of 2F-modules II, §3.5 and Proposition 4.1(2), pp.20,22.
-/

public section

open scoped MonoidAlgebra
namespace Representation
variable {k G H V : Type*} [Field k] [Group G] [Group H]
  [AddCommGroup V] [Module k V]
  (ρ : Representation k G V) (L : Subgroup G) (e : H ≃* L)

private def markedEnd (f : IntertwiningMap ((ρ.comp L.subtype).comp e.toMonoidHom)
    ((ρ.comp L.subtype).comp e.toMonoidHom)) :
    IntertwiningMap (ρ.comp L.subtype) (ρ.comp L.subtype) where
  toLinearMap := f.toLinearMap
  isIntertwining' g := by
    have hh := f.isIntertwining' (e.symm g)
    change f.toLinearMap * ρ (e (e.symm g) : G) =
      ρ (e (e.symm g) : G) * f.toLinearMap at hh
    change f.toLinearMap * ρ (g : G) = ρ (g : G) * f.toLinearMap
    simpa only [MulEquiv.apply_symm_apply] using hh

/-- A Schur-linear ambient actor is linear over the actual Schur ring of any
marking of the layer. -/
noncomputable def schurLinearMarkedEquiv (t : G) (ht : IsSchurLinear ρ L t) :
    let σ : Representation k H V := (ρ.comp L.subtype).comp e.toMonoidHom
    σ.asModule ≃ₗ[Module.End k[H] σ.asModule] σ.asModule := by
  let σ : Representation k H V := (ρ.comp L.subtype).comp e.toMonoidHom
  let T : Module.End (Module.End k[H] σ.asModule) σ.asModule := {
    toFun v := σ.asModuleEquiv.symm (ρ t (σ.asModuleEquiv v))
    map_add' x y := by simp
    map_smul' c v := by
      have hh := LinearMap.congr_fun
        (ht (markedEnd ρ L e ((IntertwiningMap.equivAlgEnd σ).symm c)))
          (σ.asModuleEquiv v)
      exact congrArg σ.asModuleEquiv.symm hh }
  refine LinearEquiv.ofBijective T ⟨?_, ?_⟩
  · intro v w hvw
    have hh := congrArg (fun v => ρ t⁻¹ (σ.asModuleEquiv v)) hvw
    have hv : ρ t⁻¹ (ρ t (σ.asModuleEquiv v)) = σ.asModuleEquiv v := by
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    have hw : ρ t⁻¹ (ρ t (σ.asModuleEquiv w)) = σ.asModuleEquiv w := by
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    exact σ.asModuleEquiv.injective (hv.symm.trans (hh.trans hw))
  · intro v
    refine ⟨σ.asModuleEquiv.symm (ρ t⁻¹ (σ.asModuleEquiv v)), ?_⟩
    apply σ.asModuleEquiv.injective
    change ρ t (ρ t⁻¹ (σ.asModuleEquiv v)) = σ.asModuleEquiv v
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

@[simp] theorem schurLinearMarkedEquiv_apply (t : G) (ht : IsSchurLinear ρ L t)
    (v : Representation.asModule ((ρ.comp L.subtype).comp e.toMonoidHom)) :
    schurLinearMarkedEquiv ρ L e t ht v =
      (Representation.asModuleEquiv ((ρ.comp L.subtype).comp e.toMonoidHom)).symm
        (ρ t (Representation.asModuleEquiv ((ρ.comp L.subtype).comp e.toMonoidHom) v)) := (rfl)

variable [L.Normal]

/-- The marked Schur-linear map intertwines the actual conjugation on the layer. -/
theorem schurLinearMarkedEquiv_intertwines (t : G) (ht : IsSchurLinear ρ L t)
    (g : H) (v : Representation.asModule ((ρ.comp L.subtype).comp e.toMonoidHom)) :
    schurLinearMarkedEquiv ρ L e t ht
      (Representation.endFieldRep ((ρ.comp L.subtype).comp e.toMonoidHom) g v) =
    Representation.endFieldRep ((ρ.comp L.subtype).comp e.toMonoidHom)
      (MulAut.congr e.symm (MulAut.conjNormal (H := L) t) g)
      (schurLinearMarkedEquiv ρ L e t ht v) := by
  let σ : Representation k H V := (ρ.comp L.subtype).comp e.toMonoidHom
  apply σ.asModuleEquiv.injective
  change ρ t (ρ (e g : G) (σ.asModuleEquiv v)) =
    ρ (e (MulAut.congr e.symm (MulAut.conjNormal (H := L) t) g) : G)
      (ρ t (σ.asModuleEquiv v))
  have he : (e (MulAut.congr e.symm (MulAut.conjNormal (H := L) t) g) : G) =
      t * (e g : G) * t⁻¹ := by simp [MulAut.congr]
  rw [he]
  simp only [← Module.End.mul_apply, ← map_mul, mul_assoc, inv_mul_cancel, mul_one]
end Representation
