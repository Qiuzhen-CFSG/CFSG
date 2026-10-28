module
public import Theory.SpecificGroups.BinaryLinear.FourParabolicAction.Geometry
public import Theory.LinearAlgebra.BinaryFourFixedSpace

/-!
# Orders of binary two-space parabolics

Restriction to the defining two-space is onto GL₂(2). Its kernel fixes that
space pointwise, so the independent-frame count gives order 96 for the kernel
and order 576 for the parabolic. The ambient order 20160 then gives index 35.
The source Mathieu point–plane intersection uses these exact stabilizers.

Source: Aschbacher, *Sporadic Groups* (1994), 41.1, pp.219–220.
-/

public noncomputable section
open Subgroup Module
namespace BinaryLinear.FourParabolicAction
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
private noncomputable def restriction (W : Submodule (ZMod 2) V) : parabolic W →* (W ≃ₗ[ZMod 2] W) where
  toFun g :=
    { toFun := fun w => ⟨g.val w, (g.property w).mpr w.property⟩
      invFun := fun w => ⟨g.val.symm w, ((parabolic W).inv_mem g.property w).mpr w.property⟩
      left_inv := fun w => Subtype.ext (g.val.symm_apply_apply w)
      right_inv := fun w => Subtype.ext (g.val.apply_symm_apply w)
      map_add' := fun a b => Subtype.ext (g.val.map_add a b)
      map_smul' := fun a b => Subtype.ext (g.val.map_smul a b) }
  map_one' := by ext; rfl
  map_mul' _ _ := by ext; rfl

private theorem restriction_surjective (W : Submodule (ZMod 2) V) : Function.Surjective (restriction W) := by
  intro f
  obtain ⟨g, hg⟩ := Submodule.exists_linearEquiv_restrict_eq f
  have hm : g ∈ parabolic W := by
    intro v
    constructor
    · intro hv
      have h := hg (f.symm ⟨g v, hv⟩)
      have he : g ((f.symm ⟨g v, hv⟩ : W) : V) = g v := by simpa using h.symm
      exact g.injective he ▸ (f.symm ⟨g v, hv⟩).property
    · intro hv
      rw [← hg ⟨v, hv⟩]
      exact (f ⟨v, hv⟩).property
  exact ⟨⟨g, hm⟩, by ext w; exact (hg w).symm⟩

/-- The two-space stabilizer in a binary four-space has order 576. -/
theorem twoSpace_parabolic_card (W : Submodule (ZMod 2) V)
    (hV : finrank (ZMod 2) V = 4) (hW : finrank (ZMod 2) W = 2) :
    Nat.card (parabolic W) = 576 := by
  classical
  let : Finite V := Module.finite_of_finite (ZMod 2)
  have hi := BinaryFourFixedSpace.index_pointwiseFixer W
  rw [hV, hW] at hi
  norm_num [Fin.prod_univ_succ] at hi
  have hfix : Nat.card (BinaryFourFixedSpace.pointwiseFixer W) = 96 := by
    have hc := (BinaryFourFixedSpace.pointwiseFixer W).card_mul_index
    rw [BinaryFourFixedSpace.card_GL_four hV, hi] at hc
    omega
  have hGL : Nat.card (W ≃ₗ[ZMod 2] W) = 6 := by
    let b : Basis (Fin 2) (ZMod 2) W := (finBasis (ZMod 2) W).reindex (finCongr hW)
    let e := (Matrix.GeneralLinearGroup.toLin' b).trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) W)
    rw [← Nat.card_congr e.toEquiv, Matrix.card_GL_field]
    norm_num [Fin.prod_univ_succ]
  have hk : (restriction W).ker =
      (BinaryFourFixedSpace.pointwiseFixer W).subgroupOf (parabolic W) := by
    ext g
    change restriction W g = 1 ↔ ∀ w ∈ W, g.val w = w
    constructor
    · intro h w hw
      exact congrArg Subtype.val (LinearEquiv.congr_fun h ⟨w, hw⟩)
    · intro h
      ext w
      exact h w w.property
  have hle : BinaryFourFixedSpace.pointwiseFixer W ≤ parabolic W := by
    intro g hg v
    constructor
    · intro hv
      exact g.injective (hg (g v) hv) ▸ hv
    · intro hv
      rw [hg v hv]
      exact hv
  have hc := (restriction W).ker.card_mul_index
  rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr (restriction_surjective W),
    Subgroup.card_top, hGL, hk,
    Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv, hfix] at hc
  omega
/-- The same stabilizer has index 35, counting the two-spaces of the four-space. -/
theorem twoSpace_parabolic_index (W : Submodule (ZMod 2) V)
    (hV : finrank (ZMod 2) V = 4) (hW : finrank (ZMod 2) W = 2) :
    (parabolic W).index = 35 := by
  have h := (parabolic W).card_mul_index
  rw [twoSpace_parabolic_card W hV hW, BinaryFourFixedSpace.card_GL_four hV] at h
  omega

end BinaryLinear.FourParabolicAction
