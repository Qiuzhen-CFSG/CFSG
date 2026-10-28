module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.G2.ExceptionalModule
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.FrattiniCore
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.MovingSection
public import Theory.GroupTheory.SelfCentralizingCoreInheritance
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizingPrimeCore

/-!
# Whole-core reduction for the exceptional G₂ MS pair

The explicit MS93 Frattini containment identifies the entire intrinsic
[O₂(L),L] with the moving central omega layer. The exceptional initial
module theorem then constructs its genuine natural block-module model.
This retains the missing Frattini containment as a premise, rather than
claiming that initial-module recognition already proves C.1.32.
The source noncentrality owner discharges that premise before final assembly.
Source: MS93 (3.6), p.870; AS C.1.32 and 13.3.10(2).
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.G2Exceptional.Input
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}

/-- Exact whole-core reconstruction after the remaining source containment. -/
theorem core_of_frattini_small (h : G2Exceptional.Input KnownSimple.IsKnownSimple L R)
    (hsmall : ⁅pCore 2 G,L⁆ ≤
      (frattini (pCore 2 G)).map (pCore 2 G).subtype ⊔ omegaCenterIn (pCore 2 G)) :
    IsElementaryAbelian 2 (blockU L) ∧
      blockU L ≤ centralizer (pCore 2 L : Set L) ∧
      IsLinearBlockModel L (Representation.g2DerivedNatural (ZMod 2)) := by
  let := h.component_normal
  let := h.quotientComponent_structure.1
  obtain ⟨hcore,helem,hcentral⟩ :=
    MSCentralOrbit.intrinsic_core_of_frattini_small L h.component_twoPerfect hsmall
  obtain ⟨E⟩ := h.initial_moved_natural.2
  exact ⟨helem,hcentral,BlockMovingSection.model_of_moving
    (omegaCenterIn (pCore 2 G)) L
    (QuotientGroup.mk' (pCore 2 G)) (QuotientGroup.mk'_surjective _)
    ((QuotientGroup.ker_mk' _).trans h.centralOmega_centralizer.symm)
    hcore (cComponentTwoCoreQuotientEquiv h.component) (fun _ => rfl)
    (Representation.g2DerivedNatural (ZMod 2)) E⟩

/-- Every block clause follows from the same literal Frattini containment.
The containment remains the source reconstruction obligation. -/
theorem block_of_frattini_small (h : G2Exceptional.Input KnownSimple.IsKnownSimple L R)
    (hsmall : ⁅pCore 2 G,L⁆ ≤
      (frattini (pCore 2 G)).map (pCore 2 G).subtype ⊔ omegaCenterIn (pCore 2 G)) :
    IsBlock L ∧ IsG2TwoBlock L := by
  let := h.component_normal
  let := h.quotientComponent_structure.1
  let := h.quotientComponent_structure.2.2.1
  obtain ⟨helem,hcentral,hmodel⟩ := h.core_of_frattini_small hsmall
  have hcore := (MSCentralOrbit.intrinsic_core_of_frattini_small L
    h.component_twoPerfect hsmall).1
  have hi : BlockModuleIrreducible L :=
    BlockMovingSection.irreducible_of_moving (omegaCenterIn (pCore 2 G)) L
      (QuotientGroup.mk' (pCore 2 G)) (QuotientGroup.mk'_surjective _)
      ((QuotientGroup.ker_mk' _).trans h.centralOmega_centralizer.symm)
      hcore h.initial_moved_natural.1
  have hshort : IsShort L := {
    finite := inferInstance
    twoPerfect := h.component_twoPerfect
    fitting := generalizedFitting_eq_pCore_of_selfCentralizing 2
      (subnormal_core_selfCentralizing h.core_self_centralizing L h.component.subnormal)
    elementary := helem
    central := hcentral
    quotient := Or.inl (IsQuasisimple.of_mulEquiv
      (cComponentTwoCoreQuotientEquiv h.component).symm)
    irreducible := hi }
  exact ⟨⟨inferInstance,hshort,h.component.subnormal⟩,hshort,hmodel⟩

end CFSG.Quasithin.ChapterC.G2Exceptional.Input
