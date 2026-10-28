module
public import Theory.GroupTheory.PGroup.NormalSubgroups
public import Theory.Representation.BinaryOffender.InvolutionRatio

/-!
# Central involutions in a Sylow-normal elementary actor

A nontrivial normal subgroup of a finite two-group meets its center. Apply
this to the elementary actor inside its marked Sylow subgroup, and then use
faithfulness to make the displacement of the resulting involution positive.
This retains the original actor and Sylow, rather than selecting an
unrelated involution of the ambient linear group.

The source consumer is the partner chief action in Aschbacher--Smith,
original 15.2.27(2), printed p.1119 (refs/quasithin.pdf p.1136).
-/

public section
open Subgroup
namespace Representation.BinaryOffender
variable {G W : Type*} [Group G] [Finite G]
  [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]

/-- A nontrivial Sylow-normal elementary actor contains a central involution. -/
theorem exists_sylow_central_involution_of_normal_elementary
    (A : Subgroup G) (S : Sylow 2 G) (hA : IsElementaryAbelian 2 A)
    (hne : A ≠ ⊥) (hAS : A ≤ S) (hn : (S : Subgroup G) ≤ normalizer (A : Set G)) :
    ∃ a : G, a ∈ A ∧ orderOf a = 2 ∧
      ∀ s ∈ (S : Subgroup G), Commute a s := by
  let N := A.subgroupOf (S : Subgroup G)
  let : N.Normal := normal_subgroupOf_of_le_normalizer hn
  let : Nontrivial A := (nontrivial_iff_ne_bot A).mpr hne
  let : Nontrivial N := (subgroupOfEquivOfLe hAS).toEquiv.nontrivial
  let : Fact (IsPGroup 2 S) := ⟨S.isPGroup'⟩
  obtain ⟨a, ha, hc⟩ := exists_nontrivial_center_mem_normal (p := 2) N
  let := hA
  have ha1 : ((a : S) : G) ≠ 1 := by
    intro he
    exact ha (Subtype.ext (Subtype.ext he))
  refine ⟨a, a.property, orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian (p := 2) _ a.property) ha1, ?_⟩
  intro s hs
  exact (congrArg Subtype.val ((mem_center_iff.mp hc) ⟨s,hs⟩)).symm

/-- The same central involution has positive displacement in a faithful action. -/
theorem exists_sylow_central_displacement
    (ρ : Representation (ZMod 2) G W) (hf : Function.Injective ρ)
    (A : Subgroup G) (S : Sylow 2 G) (hA : IsElementaryAbelian 2 A)
    (hne : A ≠ ⊥) (hAS : A ≤ S) (hn : (S : Subgroup G) ≤ normalizer (A : Set G))
    (hd : ∀ a ∈ A, Module.finrank (ZMod 2) (LinearMap.range (ρ a - 1)) ≤ 2) :
    ∃ a : G, a ∈ A ∧ orderOf a = 2 ∧
      (∀ s ∈ (S : Subgroup G), Commute a s) ∧
      1 ≤ Module.finrank (ZMod 2) (LinearMap.range (ρ a - 1)) ∧
      Module.finrank (ZMod 2) (LinearMap.range (ρ a - 1)) ≤ 2 := by
  obtain ⟨a,ha,ho,hc⟩ := exists_sylow_central_involution_of_normal_elementary A S hA hne hAS hn
  refine ⟨a,ha,ho,hc,?_,hd a ha⟩
  have hm : ρ a ≠ 1 := by
    intro he
    have he1 : a = 1 := hf (he.trans (map_one ρ).symm)
    simp [he1] at ho
  by_contra hh
  have hz : Module.finrank (ZMod 2) (LinearMap.range (ρ a - 1)) = 0 := by omega
  exact hm (sub_eq_zero.mp (LinearMap.range_eq_bot.mp (Submodule.finrank_eq_zero.mp hz)))

end Representation.BinaryOffender
