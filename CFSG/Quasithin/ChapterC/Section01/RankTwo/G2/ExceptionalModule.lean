module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.G2.ExceptionalStructure
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.G2.NaturalLayerRecognition
public import Theory.Representation.NormalElementaryQuotient.IrrPlusCommutator
public import Theory.Quasithin.Rank

/-!
# The initial natural module for the exceptional root-eight MS pair

The original quotient component is simple of order 6048 and self-centralizing.
The faithful FF action on the actual central omega layer therefore has the
canonical six-dimensional moved/fixed quotient. Its moving part equals that
of the original radical-center orbit. This establishes the initial module
under MS2(b), without substituting the whole point-parabolic radical.

The whole-core reconstruction still requires the MS93 Frattini containment;
recognition of this initial layer alone is not the block theorem.
Source: AS C.1.31–32, pp.135–136; MS93 (3.2), pp.863–866.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.G2Exceptional.Input
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
variable (h : G2Exceptional.Input KnownSimple.IsKnownSimple L R)
include h

local notation "C" => L.map (QuotientGroup.mk' (pCore 2 G))
local notation "X" => omegaCenterIn (pCore 2 G)

noncomputable def quotientComponentEquiv : C ≃* commutator (Atlas.G2.Model (ZMod 2)) :=
  (cComponentTwoCoreQuotientEquiv h.component).symm.trans h.componentQuotient

theorem quotientComponent_card : Nat.card C = 6048 :=
  (Nat.card_congr h.quotientComponentEquiv.toEquiv).trans
    (Atlas.G2.DerivedEvenOrder.card_derived_binary (by simp))

theorem quotientComponent_structure : (C).Normal ∧ IsSimpleGroup C ∧
    IsQuasisimple C ∧ centralizer (C : Set (G ⧸ pCore 2 G)) = ⊥ := by
  let := Atlas.G2.isSimple_commutator_binary
  let := h.componentQuotient.isSimpleGroup
  exact (MSCentralOrbit.component_image_structure L R h.component
    h.radical_two_group h.product).2

theorem quotientComponent_sqtk : IsSQTK KnownSimple.IsKnownSimple C := by
  have hsq : IsSQTK KnownSimple.IsKnownSimple (G ⧸ pCore 2 G) :=
    ⟨fun p hp ho => by
      let _ : Fact p.Prime := ⟨hp⟩
      exact (primeRank_quotient_le_of_isTwoGroup p ho (pCore 2 G) pCore_isPGroup).trans
        (h.sqtk.stronglyQuasithin p hp ho), h.sqtk.isKGroup.quotient _⟩
  exact hsq.subgroup _

/-- The literal central-omega moved/fixed section is the natural G₂(2)′ module. -/
theorem initial_moved_natural :
    let := h.quotientComponent_structure.1
    Representation.BinaryOffender.IsIrrPlus h.centralOmegaAction C
      (Representation.BinaryOffender.subspaceCommutator h.centralOmegaAction ⊤ C) ∧
      Nonempty (ChapterB.QuasisimpleSource.ActionEquiv
        ((ChapterB.QuasisimpleSource.MovedSection.ofNormal h.centralOmegaAction C).action.comp
          (C).subtype) (Representation.g2DerivedNatural (ZMod 2))) := by
  let := h.quotientComponent_structure.1
  let := h.quotientComponent_structure.2.1
  let := h.quotientComponent_structure.2.2.1
  exact RankTwo.G2.ff_card_g2_two_moved_natural _ _ h.quotientComponent_card
    h.quotientComponent_structure.2.2.2 h.quotientComponent_sqtk
    h.centralOmegaAction_faithful h.centralOmega_FF

/-- The original orbit and the full central omega have the same moving part. -/
theorem initialCore_eq :
    ⁅MSCentralOrbit.omegaOrbit R,L⁆ = ⁅X,L⁆ := by
  let := h.quotientComponent_structure.1
  let := h.quotientComponent_structure.2.2.1
  let : IsElementaryAbelian 2 (MSCentralOrbit.omegaOrbit R) :=
    MSCentralOrbit.omegaOrbit_elementary _ h.core_le_radical h.core_self_centralizing
  have hne : C ≠ ⊥ := by
    intro hz
    have hc := h.quotientComponent_card
    rw [hz,card_bot] at hc
    omega
  exact Representation.NormalElementaryQuotient.commutator_eq_of_irrPlus
    (MSCentralOrbit.omegaOrbit R) X
    (MSCentralOrbit.omegaOrbit_le_centralOmega _ h.core_le_radical h.core_self_centralizing)
    (QuotientGroup.mk' (pCore 2 G)) (QuotientGroup.mk'_surjective _)
    ((QuotientGroup.ker_mk' _).trans h.omegaOrbit_centralizer.symm)
    ((QuotientGroup.ker_mk' _).trans h.centralOmega_centralizer.symm)
    L C rfl hne h.initial_moved_natural.1

end CFSG.Quasithin.ChapterC.G2Exceptional.Input
