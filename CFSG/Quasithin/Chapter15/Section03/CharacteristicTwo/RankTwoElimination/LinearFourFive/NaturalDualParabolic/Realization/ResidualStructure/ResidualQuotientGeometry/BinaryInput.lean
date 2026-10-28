module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.NaturalDualParabolic.Realization.ResidualStructure.ResidualQuotientGeometry
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.NaturalDualParabolic.Realization.Assembly

/-!
# The actual binary input inherits the opposing central-quotient factors

The intrinsic BinaryMS core maps isomorphically onto the literal residual
commutator K. Transport through the full centers identifies its actual central
quotient with K/Z(K). The natural injection and dual surjection retain these
canonical maps. For the original theta component, its Sylow and elementary-span
hypotheses discharge the sole module-core placement assumption.

This is the literal input transport for Aschbacher–Smith 15.3.24,
combined manuscript (1 March 2004), printed pp.1129–1130.
-/

@[expose] public noncomputable section
open Subgroup BinaryLinear.OuterCyclic
open BinaryNaturalDual.VectorStabilizers BinaryNaturalDual.VectorStabilizers.Pure
open Theory.LinearAlgebra.BinaryFivePointStabilizer
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.NaturalDualParabolic.Realization
open ChiefLayers
universe u
variable {G : Type u} [Group G] [Finite G] {d : LocalData G} {L : Subgroup G}

/-- Transport from the actual binary MS core retains its original ambient element. -/
def binaryInputResidualCoreEquiv {κ : GroupClass.{u}} (h : NaturalDual d L) (x : Space 4)
    (input : ChapterC.BinaryMS.Input κ (residualComponent h x) (sylowPart h x)) :
    ChapterC.BinaryMS.commutatorCore (residualComponent h x) ≃* residualCore h x :=
  ((ChapterC.BinaryMS.commutatorCore (residualComponent h x)).equivMapOfInjective
    (residualOvergroup h x).subtype (residualOvergroup h x).subtype_injective).trans
      (MulEquiv.subgroupCongr (mapped_commutatorCore h x input))

@[simp] theorem binaryInputResidualCoreEquiv_apply {κ : GroupClass.{u}} (h : NaturalDual d L)
    (x : Space 4) (input : ChapterC.BinaryMS.Input κ (residualComponent h x) (sylowPart h x))
    (k : ChapterC.BinaryMS.commutatorCore (residualComponent h x)) :
    (binaryInputResidualCoreEquiv h x input k:G) = (k.val:G) := rfl

/-- The actual binary-input core quotient, identified using only its literal
ambient image and the full centers. -/
def binaryInputResidualCentralEquiv {κ : GroupClass.{u}} (h : NaturalDual d L) (x : Space 4)
    (input : ChapterC.BinaryMS.Input κ (residualComponent h x) (sylowPart h x)) :
    (ChapterC.BinaryMS.commutatorCore (residualComponent h x) ⧸
      center (ChapterC.BinaryMS.commutatorCore (residualComponent h x))) ≃*
        (residualCore h x ⧸ center (residualCore h x)) :=
  QuotientGroup.congr _ _ (binaryInputResidualCoreEquiv h x input) (by
    let e := binaryInputResidualCoreEquiv h x input
    ext z
    constructor
    · rintro ⟨k,hk,rfl⟩
      exact (centerCongr e ⟨k,hk⟩).property
    · intro hz
      obtain ⟨k,hk⟩ := (centerCongr e).surjective ⟨z,hz⟩
      exact mem_map.mpr ⟨k,k.property,congrArg Subtype.val hk⟩)

@[simp] theorem binaryInputResidualCentralEquiv_mk {κ : GroupClass.{u}} (h : NaturalDual d L)
    (x : Space 4) (input : ChapterC.BinaryMS.Input κ (residualComponent h x) (sylowPart h x))
    (k : ChapterC.BinaryMS.commutatorCore (residualComponent h x)) :
    binaryInputResidualCentralEquiv h x input (QuotientGroup.mk' _ k) =
      QuotientGroup.mk' _ (binaryInputResidualCoreEquiv h x input k) := rfl

/-- The natural injection on the actual BinaryMS core central quotient. -/
def binaryInputNaturalIntoCentral {κ : GroupClass.{u}} (h : NaturalDual d L)
    {x : Space 4} (hx : x ≠ 0) (hU : spanCommutator d L ≤ (point h x).pCoreIn 2)
    (input : ChapterC.BinaryMS.Input κ (residualComponent h x) (sylowPart h x)) :
    Multiplicative (pointQuotient x) →*
      (ChapterC.BinaryMS.commutatorCore (residualComponent h x) ⧸
        center (ChapterC.BinaryMS.commutatorCore (residualComponent h x))) :=
  (binaryInputResidualCentralEquiv h x input).symm.toMonoidHom.comp
    (naturalIntoResidualCentral h hx hU)

/-- The dual projection on the same actual BinaryMS core central quotient. -/
def binaryInputCentralDualProjection {κ : GroupClass.{u}} (h : NaturalDual d L)
    {x : Space 4} (hx : x ≠ 0) (hU : spanCommutator d L ≤ (point h x).pCoreIn 2)
    (input : ChapterC.BinaryMS.Input κ (residualComponent h x) (sylowPart h x)) :
    (ChapterC.BinaryMS.commutatorCore (residualComponent h x) ⧸
      center (ChapterC.BinaryMS.commutatorCore (residualComponent h x))) →*
        Multiplicative (Module.Dual (ZMod 2) (pointQuotient x)) :=
  (residualCentralDualProjection h hx hU).comp
    (binaryInputResidualCentralEquiv h x input).toMonoidHom

/-- Actual source 15.3.24 application: theta-normality discharges placement in
O₂(P), and the literal BinaryMS input has both opposing marked factors. -/
theorem binaryInput_central_factors_of_theta {κ : GroupClass.{u}}
    [IsElementaryAbelian 2 (d.componentSpan L)] {I : Subgroup G}
    (h : NaturalDual d L) {x : Space 4} (hx : x ≠ 0)
    (hS : Chapter1.IsSylowIn 2 d.S I) (hθ : L = theta I)
    (input : ChapterC.BinaryMS.Input κ (residualComponent h x) (sylowPart h x)) :
    let hU := (spanCommutator_le_componentCore_of_theta hS hθ).trans
      (componentCore_le_pointCore h x)
    Function.Injective (binaryInputNaturalIntoCentral h hx hU input) ∧
      Function.Surjective (binaryInputCentralDualProjection h hx hU input) := by
  dsimp only
  constructor
  · exact (binaryInputResidualCentralEquiv h x input).symm.injective.comp
      (naturalIntoResidualCentral_injective h hx
        ((spanCommutator_le_componentCore_of_theta hS hθ).trans (componentCore_le_pointCore h x)))
  · exact (residualCentralDualProjection_surjective h hx
      ((spanCommutator_le_componentCore_of_theta hS hθ).trans (componentCore_le_pointCore h x))).comp
      (binaryInputResidualCentralEquiv h x input).surjective

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.NaturalDualParabolic.Realization
