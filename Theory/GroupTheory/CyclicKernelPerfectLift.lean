module

public import Theory.GroupTheory.CyclicNormalCentralizer
public import Mathlib.GroupTheory.IsPerfect

/-!
# Commuting lifts through a cyclic kernel

A perfect subgroup centralizes every cyclic normal kernel. If the original
homomorphism is injective on that subgroup, commuting elements of its image
have commuting lifts anywhere in the full preimage: changing a lift only
multiplies it by a commuting kernel element.

Source: the standard cyclic-normal centralizer argument, applied to the
nonsplit cubic Held local extensions in GLS3 Table 5.3p.
-/

public section
open Subgroup
namespace Theory.GroupTheory

/-- Every pair of lifts of commuting image elements commutes when a perfect
subgroup maps injectively onto that image and the whole kernel is cyclic. -/
theorem commute_lifts_of_perfect_subgroup {E H : Type*} [Group E] [Group H]
    (f : E →* H) [IsCyclic f.ker] (U : Subgroup E) [Group.IsPerfect U]
    (hi : Function.Injective (f.comp U.subtype)) {x y : E}
    (hx : f x ∈ U.map f) (hy : f y ∈ U.map f) (hc : Commute (f x) (f y)) :
    Commute x y := by
  obtain ⟨a,ha,hax⟩ := mem_map.mp hx
  obtain ⟨b,hb,hby⟩ := mem_map.mp hy
  have hab : Commute a b := by
    have hh : (⟨a,ha⟩ : U) * ⟨b,hb⟩ = ⟨b,hb⟩ * ⟨a,ha⟩ := by
      apply hi
      change f (a*b) = f (b*a)
      simpa only [map_mul,hax,hby] using hc.eq
    exact congrArg Subtype.val hh
  have hUK : U ≤ centralizer (f.ker : Set E) := by
    apply le_trans _ (commutator_le_centralizer_of_isCyclic_normal f.ker)
    rw [←Subgroup.commutator_eq_self (H := U)]
    exact commutator_mono le_top le_top
  let k : f.ker := ⟨x*a⁻¹,by simp only [MonoidHom.mem_ker,map_mul,map_inv,hax,mul_inv_cancel]⟩
  let l : f.ker := ⟨y*b⁻¹,by simp only [MonoidHom.mem_ker,map_mul,map_inv,hby,mul_inv_cancel]⟩
  have hkl : Commute (k : E) (l : E) := by
    exact congrArg Subtype.val ((inferInstance : IsMulCommutative f.ker).is_comm.comm k l)
  have hal : Commute a (l : E) := (hUK ha l l.property).symm
  have hkb : Commute (k : E) b := hUK hb k k.property
  have h := (hkl.mul_right hkb).mul_left (hal.mul_right hab)
  simpa only [k,l,inv_mul_cancel_right] using h

end Theory.GroupTheory
