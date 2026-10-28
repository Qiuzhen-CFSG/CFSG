module

public import Theory.SpecificGroups.BinaryLinear.SmallParabolicLevi.TwoBlocks
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.RadicalOrientation.Basic
public import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Literal displacement coordinates for a binary radical

The radical at W is the additive group Hom(V/W,W). The coordinates are
the actual displacement g(v)-v, and conjugation acts through the two
geometric diagonal blocks. This supplies an action comparison, not only
a cardinality identification, for the surviving binary flags.
-/

public noncomputable section
namespace BinaryLinear
open Subgroup SmallParabolicLevi
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

private def radicalDisplacement (W : Submodule (ZMod 2) V) (g : radical W) :
    (V ⧸ W) →ₗ[ZMod 2] W :=
  W.liftQ ((g.val.toLinearMap-LinearMap.id).codRestrict W g.property.2) (by
    intro v hv
    apply Subtype.ext
    exact sub_eq_zero.mpr (g.property.1 v hv))

private def radicalShear (W : Submodule (ZMod 2) V) (f : (V ⧸ W) →ₗ[ZMod 2] W) : BinaryLinear.GL V where
  toFun v := v+(f (W.mkQ v) : V)
  invFun v := v-(f (W.mkQ v) : V)
  map_add' v w := by simp only [map_add,Submodule.coe_add]; abel
  map_smul' a v := by simp only [map_smul,Submodule.coe_smul,smul_add,RingHom.id_apply]
  left_inv v := by
    have hz (w : W) : W.mkQ (w : V)=0 := Submodule.Quotient.mk_eq_zero W |>.mpr w.property
    simp only [map_add,hz,add_zero,add_sub_cancel_right]
  right_inv v := by
    have hz (w : W) : W.mkQ (w : V)=0 := Submodule.Quotient.mk_eq_zero W |>.mpr w.property
    simp only [map_sub,hz,sub_zero,sub_add_cancel]

private theorem radicalShear_mem (W : Submodule (ZMod 2) V) (f : (V ⧸ W) →ₗ[ZMod 2] W) :
    radicalShear W f ∈ radical W := by
  constructor
  · intro v hv
    change v+(f (W.mkQ v) : V)=v
    have hz : W.mkQ v=0 := (Submodule.Quotient.mk_eq_zero W).mpr hv
    rw [hz,map_zero,Submodule.coe_zero,add_zero]
  · intro v
    change v+(f (W.mkQ v) : V)-v ∈ W
    rw [add_sub_cancel_left]
    exact (f _).property

/-- The actual displacement, with its original quotient and subspace, is a
group equivalence onto the full additive Hom group. -/
def radicalDisplacementEquiv (W : Submodule (ZMod 2) V) :
    radical W ≃* Multiplicative ((V ⧸ W) →ₗ[ZMod 2] W) where
  toFun g := Multiplicative.ofAdd (radicalDisplacement W g)
  invFun f := ⟨radicalShear W f.toAdd,radicalShear_mem W f.toAdd⟩
  left_inv g := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    change v+(g.val v-v)=g.val v
    abel
  right_inv f := by
    apply Multiplicative.toAdd.injective
    apply LinearMap.ext
    intro v
    obtain ⟨w,rfl⟩ := W.mkQ_surjective v
    apply Subtype.ext
    change w+(f.toAdd (W.mkQ w) : V)-w=(f.toAdd (W.mkQ w) : V)
    abel
  map_mul' g h := by
    apply Multiplicative.toAdd.injective
    apply LinearMap.ext
    intro v
    obtain ⟨w,rfl⟩ := W.mkQ_surjective v
    apply Subtype.ext
    change g.val (h.val w)-w=(g.val w-w)+(h.val w-w)
    have hh := g.property.1 (h.val w-w) (h.property.2 w)
    rw [map_sub] at hh
    rw [sub_eq_iff_eq_add] at hh
    rw [hh]
    abel

/-- Displacement coordinates retain their literal element formula. -/
theorem radicalDisplacementEquiv_apply (W : Submodule (ZMod 2) V)
    (g : radical W) (v : V) :
    ((radicalDisplacementEquiv W g).toAdd (W.mkQ v) : V)=g.val v-v := by rfl

/-- Conjugation on the radical is exactly postcomposition by the subspace
block and precomposition by the inverse quotient block. -/
theorem radicalDisplacementEquiv_conjugation (W : Submodule (ZMod 2) V)
    (g : parabolic W) (x y : radical W)
    (hy : y.val=g.val*x.val*g.val⁻¹) :
    (radicalDisplacementEquiv W y).toAdd =
      (subspaceAction W g).toLinearMap.comp
        ((radicalDisplacementEquiv W x).toAdd.comp
          (quotientAction W g⁻¹).toLinearMap) := by
  apply LinearMap.ext
  intro v
  obtain ⟨w,rfl⟩ := W.mkQ_surjective v
  apply Subtype.ext
  change y.val w-w = g.val ((radicalDisplacementEquiv W x).toAdd
    (quotientAction W g⁻¹ (W.mkQ w)))
  rw [quotientAction_mk,radicalDisplacementEquiv_apply,hy]
  change g.val (x.val (g.val.symm w))-w=g.val (x.val (g.val.symm w)-g.val.symm w)
  rw [map_sub,g.val.apply_symm_apply]

end BinaryLinear
