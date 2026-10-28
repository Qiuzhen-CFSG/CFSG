module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.NaturalDualParabolic.Classification.ChiefLayers.Quotients

/-!
# Relative chief intervals for the marked point parabolic

This is the precise remaining chief-factor contract for the three already
specified intervals. Normality is in the original point parabolic, intermediate
subgroups lie in the original ambient group, and noncentrality concerns actual
commutators. The contract itself asserts no existence theorem. The coordinate
flag and the natural and annihilator quotient markings are proved in the
imported modules; chiefness and the radical's dual marking are separate inputs
to their final assembly.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.24, printed pp.1129–1130.
-/

@[expose] public section
open Subgroup BinaryLinear.OuterCyclic
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.NaturalDualParabolic.ChiefLayers
variable {G : Type*} [Group G] {d : LocalData G} {L : Subgroup G}

/-- A noncentral chief interval for the actual point parabolic. The normality
fields are relative to P, not normality in the ambient group G. -/
structure IsNoncentralChiefInterval (h : NaturalDual d L) (x : Space 4)
    (A B : Subgroup G) : Prop where
  strict : A < B
  upper_le : B ≤ point h x
  lower_normal : (A.subgroupOf (point h x)).Normal
  upper_normal : (B.subgroupOf (point h x)).Normal
  chief : ∀ D : Subgroup G, A ≤ D → D ≤ B →
    (D.subgroupOf (point h x)).Normal → D = A ∨ D = B
  noncentral : ¬ ⁅point h x, B⁆ ≤ A

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.NaturalDualParabolic.ChiefLayers
end
