module
public import CFSG.Quasithin.Chapter2.Section04.DoubleA3.ComponentActionSource
public import Theory.SpecificGroups.AlternatingSix.CubicAbsorption

/-!
# Absorption of the actual cubic block in the A₆ row

The original second involution centralizer has three-rank at most two.
The first block is its actual two-perfect A₄ subgroup, so the intrinsic
A₆ component theorem gives both normality and containment. This removes
the absorption premise for the retained A₆ branch of 2.4.32.

Source: Aschbacher–Smith, printed p.547.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.DoubleA3
open AlternatingSix.ShadowLocal
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}
variable {d : MinimalBlockSetup M} {T : Sylow 2 G} {c : SourcePairCoordinates d T}

/-- The retained A₆ model contains the original first cubic block. -/
theorem SourceCentralizerGeometry.alternating_six_component_absorbs_first_block
    (g : SourceCentralizerGeometry c) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (K : Subgroup (involutionCentralizer g.z₂))
    (hK : IsComponent (involutionCentralizer g.z₂) K) (e : K ≃* A6) :
    K.Normal ∧ d.block.map d.H.subtype ≤ K.map (involutionCentralizer g.z₂).subtype := by
  let H := involutionCentralizer g.z₂
  let L := (d.block.map d.H.subtype).subgroupOf H
  have hr : primeRank 3 H ≤ 2 :=
    (hG.twoLocal_sqtk (isTwoLocal_involution_centralizer g.order_second)).stronglyQuasithin
      3 Nat.prime_three (by decide)
  let eL := subgroupOfEquivOfLe g.first_block_le_second_centralizer
  have hp : IsPPerfect 2 L := c.first.short.twoPerfect.of_surjective
    eL.symm.toMonoidHom eL.symm.surjective
  obtain ⟨eA⟩ := c.cubic_first.equiv_alternatingFour
  have hc : Nat.card L ∣ 12 := by
    rw [Nat.card_congr (eL.trans eA).toEquiv,
      alternatingGroup.card_of_card_eq_four (by simp)]
  have hl := cubic_twoPerfect_le_component K hK e hr L hp hc
  refine ⟨component_normal_of_three_rank K hK e hr,?_⟩
  have hh := map_mono (f:=H.subtype) hl
  rwa [map_subgroupOf_eq_of_le g.first_block_le_second_centralizer] at hh
end CFSG.Quasithin.Chapter2.DoubleA3
