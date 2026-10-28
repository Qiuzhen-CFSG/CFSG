module
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Core.Automizers.Models.Actions

/-!
# No fixed vector in the lower tensor layer

A cubic in the first actual Y factor fixes no nonzero binary matrix.
The common layer coordinates transport this to C_V(Y)=1, the remaining
fixed-space premise in the final local-core calculation.

Source: Aschbacher–Smith, 15.3.54 and 15.3.59, printed pp.1146,1149.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50
open Core.Automizers.Models
variable {G : Type*} [Group G] {I Y P V : Subgroup G}
  {hIP : I ≤ normalizer (P : Set G)} {hIV : I ≤ normalizer (V : Set G)}
  [(V.subgroupOf P).Normal]

theorem LayerActions.lower_fixed_eq_bot (d : LayerActions I Y P V hIP hIV) :
    V ⊓ centralizer (Y : Set G) = ⊥ := by
  apply eq_bot_iff.mpr
  rintro v ⟨hv,hc⟩
  change v=1
  have ha : (rotation,1) ∈ (Y.subgroupOf I).map d.actor := by
    rw [d.image_Y]
    exact ⟨mem_zpowers rotation,one_mem _⟩
  obtain ⟨y,hy,he⟩ := ha
  have hf : Core.Automizers.lowerAction I V hIV y ⟨v,hv⟩ = ⟨v,hv⟩ := by
    apply Subtype.ext
    change (y:G)*v*(y:G)⁻¹=v
    have hc' : (y:G)*v=v*(y:G) := hc _ hy
    rw [hc',mul_inv_cancel_right]
  have hm := congrArg d.lowerCoordinates hf
  rw [d.lower_compatible,he] at hm
  have cert : ∀ x : TensorVector, tensorAction (rotation,1) x=x → x=1 := by
    decide +kernel
  have hv1 := d.lowerCoordinates.injective ((cert _ hm).trans (map_one _).symm)
  exact congrArg Subtype.val hv1

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50
