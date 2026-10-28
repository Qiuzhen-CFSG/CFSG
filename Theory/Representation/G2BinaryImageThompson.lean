module
public import Theory.Representation.G2BinaryThompson
/-!
# Thompson centralization through a faithful module image

A central quotient that is injective on a marked binary natural module
preserves its action and the absence of derived G₂ offenders. Descending
the actor and transporting the module coordinates therefore makes every
maximum elementary subgroup centralize the image module.

The original Rudvalis residual application retains its actual central
quotient map. Source: Aschbacher--Smith B.2.4, B.4.6(13), C.1.37 and
4.2.13, printed pp.75,90,141,611--612.
-/

public section
open Subgroup Stellmacher
open scoped IsMulCommutative
namespace Atlas.G2.Natural.BinaryNormalizer
variable {X Y : Type*} [Group X] [Group Y] [Finite Y]
/-- Central quotients faithful on the module preserve the derived-action
Thompson centralizer bound, for every containing subgroup. -/
theorem image_thompson_centralizes (U : Subgroup X) [U.Normal] [IsElementaryAbelian 2 U]
    (q : X →* Full) (E : Additive U ≃ₗ[ZMod 2] Space (ZMod 2))
    (he : ∀ g v, E (Additive.ofMul (MulAut.conjNormal g v)) =
      action (ZMod 2) (q g) (E (Additive.ofMul v)))
    (hq : q.range ≤ Derived)
    (f : X →* Y) (hf : Function.Surjective f) (hk : f.ker ≤ center X)
    (hi : Function.Injective (f.comp U.subtype))
    (R : Subgroup Y) (hUR : U.map f ≤ R) :
    elementaryAbelianMaxJ R ≤ centralizer (U.map f : Set Y) := by
  let D := U.map f
  let : D.Normal := Subgroup.Normal.map inferInstance f hf
  let : IsElementaryAbelian 2 D := IsElementaryAbelian.map _
  let d : U ≃* D := MulEquiv.ofBijective (f.subgroupMap U)
    ⟨fun x y h => hi (congrArg Subtype.val h),f.subgroupMap_surjective U⟩
  let ed : Additive D ≃ₗ[ZMod 2] Additive U :=
    { d.symm.toAdditive with map_smul' := ZMod.map_smul d.symm.toAdditive }
  have hker : f.ker ≤ q.ker := by
    rw [marked_kernel_eq_centralizer U q E he]
    exact hk.trans (center_le_centralizer _)
  let r : Y →* Full := f.liftOfSurjective hf ⟨q,hker⟩
  have hr (x : X) : r (f x) = q x :=
    f.liftOfRightInverse_comp_apply (Function.surjInv hf)
      (Function.rightInverse_surjInv hf) ⟨q,hker⟩ x
  have hmark (g : Y) (v : D) :
      (ed.trans E) (Additive.ofMul (MulAut.conjNormal g v)) =
        action (ZMod 2) (r g) ((ed.trans E) (Additive.ofMul v)) := by
    obtain ⟨x,rfl⟩ := hf g
    obtain ⟨u,rfl⟩ := d.surjective v
    have hc : MulAut.conjNormal (f x) (d u) = d (MulAut.conjNormal x u) := by
      apply Subtype.ext
      change f x * f u * (f x)⁻¹ = f (x * (u : X) * x⁻¹)
      simp only [map_mul,map_inv]
    rw [hc,hr]
    change E (Additive.ofMul (d.symm (d (MulAut.conjNormal x u)))) =
      action (ZMod 2) (q x) (E (Additive.ofMul (d.symm (d u))))
    simpa only [d.symm_apply_apply] using he x u
  apply thompson_centralizes_of_image_le_derived D r (ed.trans E) hmark R hUR
  rintro _ ⟨y,hy,rfl⟩
  obtain ⟨x,rfl⟩ := hf y
  rw [hr]
  exact hq ⟨x,rfl⟩
end Atlas.G2.Natural.BinaryNormalizer
