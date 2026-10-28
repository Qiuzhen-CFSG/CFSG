module
public import Theory.SpecificGroups.GL2.ThreeResidualImages.Basic
public import Theory.GroupTheory.FrobeniusKernelNormalSubgroup

/-!
# The quaternion preimage and a Sylow two-subgroup

For any map to GL₂(3), take a Sylow two-subgroup of the determinant-one
preimage. The quaternion preimage is exactly its product with the full map
kernel, hence is normal in the original group. The proof uses the literal
matrix image, so it makes no assertion that the Sylow subgroup times a smaller
kernel is normal.

Source application: the outer-action step of Aschbacher–Smith 14.7.21,
printed p.1049. This supplies the corrected preimage for that step.
-/

public noncomputable section
open Subgroup Matrix
namespace Matrix.GeneralLinearGroup
private theorem special_four_mem : ∀ A : Matrix (Fin 2) (Fin 2) (ZMod 3),
    A.det = 1 → A^4 = 1 → A = 1 ∨ A = -1 ∨ A^2 = -1 := by decide +kernel

variable {G : Type*} [Group G] [Finite G]

/-- The entire kernel is required in the preimage of the normal quaternion subgroup. -/
theorem quaternion_preimage_eq_sylow_sup_kernel
    (f : G →* GL (Fin 2) (ZMod 3))
    (S : Sylow 2 (threeSpecialLinear.comap f)) :
    threeQuaternion.comap f =
      (S : Subgroup (threeSpecialLinear.comap f)).map (threeSpecialLinear.comap f).subtype ⊔
        f.ker := by
  let Y := threeSpecialLinear.comap f
  let g := f.comp Y.subtype
  let D := threeQuaternion.comap g
  have hS : (S : Subgroup Y) ≤ D := by
    intro s hs
    -- Apply the odd power bijection to the image, not to the original actor.
    have hi := S.isPGroup'.map g
    let a : (S : Subgroup Y).map g := ⟨g s,mem_map_of_mem g hs⟩
    have ha : a^12=1 := Subtype.ext (three_special_pow_twelve (f s) s.property)
    have h4 : a^4=1 := (hi.powEquiv (by decide : Nat.Coprime 2 3)).injective
      (by change (a^4)^3 = (1 : (S : Subgroup Y).map g)^3
          simpa only [←pow_mul,one_pow] using ha)
    apply (three_mem_quaternion (g s)).mpr
    exact special_four_mem (g s).val
      ((three_mem_specialLinear (f s)).mp s.property)
      (congrArg (fun a : (S : Subgroup Y).map g => a.val.val) h4)
  let a : D →* threeQuaternion :=
    (g.comp D.subtype).codRestrict threeQuaternion (fun d => d.property)
  have hq : IsPGroup 2 (D ⧸ a.ker) :=
    (threeQuaternion_isPGroup.to_subgroup a.range).of_equiv
      (QuotientGroup.quotientKerEquivRange a).symm
  have hk : a.ker = g.ker.subgroupOf D := by
    ext d
    change a d = 1 ↔ g d = 1
    exact Subtype.ext_iff
  have hker : g.ker ≤ D := by intro y hy; change g y ∈ threeQuaternion; rw [hy]; exact one_mem _
  have he := congrArg (Subgroup.map D.subtype)
    ((S.subtype hS).sup_eq_top_of_quotient_isPGroup a.ker hq)
  rw [Subgroup.map_sup,Sylow.coe_subtype,hk,map_subgroupOf_eq_of_le hS,
    map_subgroupOf_eq_of_le hker,←MonoidHom.range_eq_map,range_subtype] at he
  have he' := congrArg (Subgroup.map Y.subtype) he
  rw [Subgroup.map_sup] at he'
  have hkY : g.ker.map Y.subtype = f.ker := by
    change (f.ker.subgroupOf Y).map Y.subtype = f.ker
    apply map_subgroupOf_eq_of_le
    intro x hx
    change f x ∈ threeSpecialLinear
    rw [hx]
    exact one_mem _
  have hDY : D.map Y.subtype = threeQuaternion.comap f := by
    change ((threeQuaternion.comap f).subgroupOf Y).map Y.subtype = _
    exact map_subgroupOf_eq_of_le (comap_mono threeQuaternion_le_specialLinear)
  rw [hkY,hDY] at he'
  exact he'.symm
end Matrix.GeneralLinearGroup
