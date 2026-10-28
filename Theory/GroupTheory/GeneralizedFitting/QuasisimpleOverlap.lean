module
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus
public import Theory.GroupTheory.PerfectCentralQuotientNormalizer

/-!
# Quasisimple overlap and central-quotient rigidity

A quasisimple subgroup with a nonabelian overlap with a normal subgroup
lies in that subgroup. A quasisimple subgroup of a finite quasisimple
group is the whole group when their central quotients have equal order.
The latter follows by quotient order comparison and perfect recovery
across a central kernel.

These retain the full covering component when reselecting an involution
centralizer in Aschbacher--Smith 4.2.13, printed p.612.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise IsMulCommutative

namespace Theory.GroupTheory
open Subgroup
variable {G : Type*} [Group G] [Finite G] [IsQuasisimple G]

theorem quasisimple_subgroup_eq_top_of_central_quotient_card
    (K : Subgroup G) [IsQuasisimple K]
    (hcard : Nat.card (K ⧸ center K) = Nat.card (G ⧸ center G)) : K = ⊤ := by
  let q := QuotientGroup.mk' (center G)
  let f := q.comp K.subtype
  have hk : f.ker ≤ center K := by
    intro x hx
    have hz : (x : G) ∈ center G := (QuotientGroup.eq_one_iff _).mp hx
    exact mem_center_iff.mpr (fun y => Subtype.ext (mem_center_iff.mp hz y))
  let a : (K ⧸ f.ker) →* (K ⧸ center K) :=
    QuotientGroup.map f.ker (center K) (MonoidHom.id K) hk
  have ha : Function.Surjective a := by
    intro y
    obtain ⟨k,rfl⟩ := QuotientGroup.mk'_surjective (center K) y
    exact ⟨QuotientGroup.mk' f.ker k,rfl⟩
  have hsize : Nat.card (K ⧸ center K) ≤ Nat.card f.range := by
    calc
      _ ≤ Nat.card (K ⧸ f.ker) := Nat.card_le_card_of_surjective _ ha
      _ = _ := Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv
  have hr : f.range = ⊤ := by
    apply eq_top_of_card_eq
    apply le_antisymm (card_le_card_group _)
    rwa [←hcard]
  have hmap : K.map q = ⊤ := by
    simpa only [f,MonoidHom.range_comp,range_subtype] using hr
  apply top_unique
  apply perfect_le_of_map_le_of_central_kernel q (by rw [QuotientGroup.ker_mk']) ⊤ K
  rw [hmap]
  exact le_top

end Theory.GroupTheory

namespace Theory.GroupTheory
open Subgroup
variable {G : Type*} [Group G]

theorem quasisimple_le_normal_of_nonabelian_overlap
    (K N F : Subgroup G) [IsQuasisimple K] [N.Normal]
    (hFK : F ≤ K) (hFN : F ≤ N) (hne : ⁅F,F⁆ ≠ ⊥) : K ≤ N := by
  rcases IsQuasisimple.normal_le_center_or_eq_top (N.subgroupOf K) with hc | ht
  · exfalso
    apply hne
    apply commutator_eq_bot_iff_le_centralizer.mpr
    intro x hx y hy
    exact congrArg K.subtype (mem_center_iff.mp
      (hc (show (⟨x,hFK hx⟩ : K) ∈ N.subgroupOf K from hFN hx)) ⟨y,hFK hy⟩)
  · exact subgroupOf_eq_top.mp ht

end Theory.GroupTheory
