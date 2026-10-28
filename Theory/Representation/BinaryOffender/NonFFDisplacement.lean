module
public import Theory.Representation.BinaryOffender.RankOneCentralizer
public import Theory.Representation.BinaryOffender.RankOneNormalClosure

/-!
# No rank-one displacement in a faithful non-FF action

An invertible binary operator fixes its one-dimensional displacement space,
so it is an involution. Faithfulness transfers that identity to its group
actor. Its cyclic subgroup is then a best offender, contradicting the
absence of FF-offenders. This uses the literal representation throughout.

Source: Aschbacher–Smith, D.2.1 and the transvection step of 13.8.20,
printed pp.178 and955.
-/

public section
open Subgroup Representation

namespace Representation.BinaryOffender
variable {J E : Type*} [Group J] [Finite J] [AddCommGroup E] [Module (ZMod 2) E]
  [FiniteDimensional (ZMod 2) E]

/-- A faithful non-FF binary action has no rank-one displacement. -/
theorem not_rank_one_of_not_ff (ρ : Representation (ZMod 2) J E)
    (hf : Function.Injective ρ) (hn : ¬ IsFFModule ρ) (g : J) :
    Module.finrank (ZMod 2) (LinearMap.range (ρ g - LinearMap.id)) ≠ 1 := by
  intro hr
  have hne : g ≠ 1 := by
    intro he
    rw [he,map_one,show (1 : Module.End (ZMod 2) E) = LinearMap.id from rfl,
      sub_self,LinearMap.range_zero,finrank_bot] at hr
    omega
  have hg : g ^ 2 = 1 := by
    apply hf
    apply LinearMap.ext
    intro v
    have hh := fixes_displacement_of_commute_rank_one ρ g g hr (Commute.refl g) v
    have hneg (w : E) : -w = w := neg_eq_of_add_eq_zero_left (ZModModule.add_self w)
    rw [map_sub] at hh
    have ht := (sub_eq_iff_eq_add).mp hh
    simp only [sub_eq_add_neg,hneg,add_comm _ (ρ g v),←add_assoc,
      ZModModule.add_self,zero_add] at ht
    simpa only [pow_two,map_mul,Module.End.mul_apply,map_one,Module.End.one_apply] using ht
  exact hn ⟨zpowers g,(bestOffender_of_involution_displacement_le_one ρ g hg hne hr.le).isOffender⟩
end Representation.BinaryOffender
