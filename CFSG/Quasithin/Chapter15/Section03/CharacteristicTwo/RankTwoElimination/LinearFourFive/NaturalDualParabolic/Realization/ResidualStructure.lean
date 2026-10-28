module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.NaturalDualParabolic.Realization.ResidualStructure.PointInvariance
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.NaturalDualParabolic.Realization.ResidualStructure.CoreReduction
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.NaturalDualParabolic.Realization.ResidualStructure.ResidualGeometry
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.NaturalDualParabolic.Realization.Assembly

/-!
# Point invariance and the residual-core reduction in 15.3.24

The actual inner S-action on L/O₂(L) now proves S-invariance of every
point parabolic containing S∩L. Together with projected noncentrality and
the universal 15.3.11(12) witness, this constructs all BinaryMS.Input fields.

The comparison needed for MSData still requires the local containment
[O₂(L),O₂(L)] ≤ [O₂(O²(P)),O²(P)]. CoreReduction proves this is exactly
the remaining obstruction; neither that containment nor MSData is asserted
here. The parent realization task retains the source-theorem assembly.

ResidualGeometry independently proves the bounds |K| ≥ 128 and |Z(K)| ≥ 16
for the actual K = [O₂(O²(P)),O²(P)]. `binaryInput_core_bounds_of_theta`
transports these to the literal BinaryMS core. This provides an alternative
route for the classification consumer, without the unresolved comparison
in the old MSData interface. It does not establish that interface's equality.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.11(12), 15.3.17(2), 15.3.24 and C.1.31–34,
printed pp.1123–1130 and 135–137.
-/

public section
open Subgroup BinaryLinear.OuterCyclic
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.NaturalDualParabolic.Realization
universe u
variable {G : Type u} [Group G] [Finite G]
  {κ : GroupClass.{u}} {d : LocalData G} {L I : Subgroup G}

/-- The displayed earlier theta and inner-action formulas discharge point
normalization in the existing conditional BinaryMS construction. -/
theorem exists_binaryInput_of_inner [IsElementaryAbelian 2 (d.componentSpan L)]
    (h : NaturalDual d L) (plane : PlaneParabolic d L h.model)
    {x : Space 4} (hx : x ≠ 0)
    (hS : Chapter1.IsSylowIn 2 d.S I) (hθ : L = theta I)
    (hi : Preparation.IsInnerOnComponent d L
      ((Chapter1.isSylowIn_iff.mp hS).2.1.trans (normalizes_of_eq_theta hθ)))
    (hSP : d.S ⊓ L ≤ point h x)
    (hf : HasCharacteristicTwo I) (hq : IsSQTK κ I)
    (hsplit : spanCommutator d L ⊔ d.Z =
      spanCommutator d L ⊔ centralSupplement d L)
    (hact : ⁅projectedCenter d L, Stellmacher.twoResidualAmbient (d.Yplus ⊓ point h x)⁆ ≠ ⊥)
    (h11 : ∀ J : Subgroup G, J ≤ I →
      ⁅d.V, Stellmacher.twoResidualAmbient (d.Y ⊓ J)⁆ ≠ ⊥ → ¬ J ≤ d.M →
      ∀ C : Subgroup d.S, C.Characteristic → C ≠ ⊥ →
        ¬ ((C.map d.S.subtype).subgroupOf (J ⊔ d.S)).Normal) :
    Nonempty (ChapterC.BinaryMS.Input κ (residualComponent h x) (sylowPart h x)) :=
  exists_binaryInput_of_point_calculations h plane hx (hθ ▸ theta_le I) hS
    (sylow_intersection_of_eq_theta d hS hθ) hSP
    (point_normalized_of_theta h hx hS hθ hi hSP) hf hq hsplit hact h11

/-- The actual binary MS core has the two geometric bounds used by the
classification consumer, independently of the unresolved MSData equality.
The elementary-span and theta hypotheses discharge the module-core placement. -/
theorem binaryInput_core_bounds_of_theta [IsElementaryAbelian 2 (d.componentSpan L)]
    (h : NaturalDual d L) {x : Space 4} (hx : x ≠ 0)
    (hS : Chapter1.IsSylowIn 2 d.S I) (hθ : L = theta I)
    (input : ChapterC.BinaryMS.Input κ (residualComponent h x) (sylowPart h x)) :
    128 ≤ Nat.card (ChapterC.BinaryMS.commutatorCore (residualComponent h x)) ∧
      16 ≤ Nat.card (center (ChapterC.BinaryMS.commutatorCore (residualComponent h x))) := by
  have hU := (spanCommutator_le_componentCore_of_theta hS hθ).trans
    (componentCore_le_pointCore h x)
  let e : ChapterC.BinaryMS.commutatorCore (residualComponent h x) ≃*
      (⁅(Stellmacher.twoResidualAmbient (point h x)).pCoreIn 2,
        Stellmacher.twoResidualAmbient (point h x)⁆ : Subgroup G) :=
    ((ChapterC.BinaryMS.commutatorCore (residualComponent h x)).equivMapOfInjective
      (residualOvergroup h x).subtype (residualOvergroup h x).subtype_injective).trans
        (MulEquiv.subgroupCongr (mapped_commutatorCore h x input))
  constructor
  · rw [Nat.card_congr e.toEquiv]
    exact residualCore_card_ge h hx hU
  · rw [Nat.card_congr (centerCongr e).toEquiv]
    exact residualCore_center_card_ge_sixteen h hx hU

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.NaturalDualParabolic.Realization
