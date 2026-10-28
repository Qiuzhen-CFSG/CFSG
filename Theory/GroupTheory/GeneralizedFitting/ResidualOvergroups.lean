module

public import Theory.GroupTheory.SolvableResidual
public import Theory.GroupTheory.Commutator.PerfectLocalReduction
public import Theory.GroupTheory.CComponent.RadicalFree
public import Theory.GroupTheory.GeneralizedFitting.ComponentLayerStructure
public import Theory.GroupTheory.PGroup.NormalChain
public import Theory.GroupTheory.PResidual.NormalSubgroup
public import Theory.GroupTheory.PResidual.SylowSupplement

/-!
# Overgroups of the two-residual in a radical-free group

An overgroup of O²(G) is subnormal, since its image in G/O²(G) is a
subgroup of a two-group. When O²(G)=E(G) and the radical is trivial,
restriction identifies the literal layer and both residuals of every such
overgroup. This supplies the intrinsic structure for the paired E.1.11
members, without replacing their radicals by ambient quotient labels.

Source: Aschbacher–Smith, E.1.11, printed pp.213–214.
-/

public section

open Subgroup Theory.GroupTheory
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

theorem residual_overgroup_subnormal (X : Subgroup G) (hX : pResidual 2 G ≤ X) :
    X.IsSubnormal := by
  let q := QuotientGroup.mk' (pResidual 2 G)
  have h := ((isPGroup_quotient_pResidual 2 (G := G)).subgroup_isSubnormal (X.map q)).comap q
  rwa [comap_map_eq_self (by simpa only [q, QuotientGroup.ker_mk'] using hX)] at h

theorem residual_overgroup_structure (hrad : solvableRadical G = ⊥)
    (hlayer : pResidual 2 G = componentLayer G)
    (X : Subgroup G) (hX : pResidual 2 G ≤ X) :
    solvableRadical X = ⊥ ∧
    (componentLayer X).map X.subtype = pResidual 2 G ∧
    pResidual 2 X = componentLayer X ∧
    pResidual 2 X = solvableResidual X := by
  have hn := residual_overgroup_subnormal X hX
  have hE : (componentLayer X).map X.subtype = pResidual 2 G :=
    (map_componentLayer_subtype_eq_of_le X hn (hlayer ▸ hX)).trans hlayer.symm
  have hp : pResidual 2 X = componentLayer X := by
    apply le_antisymm
    · apply map_le_map_iff_of_injective X.subtype_injective |>.mp
      rw [hE]
      exact map_pResidual_le 2 X.subtype
    · let : Group.IsPerfect (componentLayer X) := componentLayer_isPerfect
      let : Group.IsNilpotent (X ⧸ pResidual 2 X) :=
        (isPGroup_quotient_pResidual 2).isNilpotent
      exact le_of_isPerfect_of_solvable_quotient _ _
  refine ⟨solvableRadical_eq_bot_of_isSubnormal hrad hn, hE, hp, ?_⟩
  apply le_antisymm
  · rw [hp]
    let : Group.IsPerfect (componentLayer X) := componentLayer_isPerfect
    exact le_solvableResidual_of_isPerfect _
  · let : Group.IsNilpotent (X ⧸ pResidual 2 X) :=
      (isPGroup_quotient_pResidual 2).isNilpotent
    exact solvableResidual_le_of_solvable_quotient _


end Theory.GroupTheory
