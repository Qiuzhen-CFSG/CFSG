module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.G2.MarkedAction.Recognition.ClassifiedComponent.Groups
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.G2.MarkedAction.Recognition.Thompson

/-!
# Recognition of the classified G₂ component action

For a component C marked by the actual higher-field G₂ group, the complete
adequate B.5.6 alternatives force its moved/fixed quotient to be the natural
G₂ module. In the quasisimple branch C is first identified with F*(D), and the
full B.5.1 list is compared. The other four branches are excluded through their
actual group structures. The surviving field is identified by its cardinality,
and the resulting equivalence includes the group map and a binary linear
intertwiner on the literal quotient.

ModelSeparation is the independent group-calculation contract; it remains an
explicit input as prescribed for this helper. There are no selected-row,
irreducibility, extra exclusion or quotient-intertwiner assumptions. The result
holds for every moved section, and the final two exports apply it to the actual
best-offender actor and its retained K⁺ component. Constructing ModelSeparation
and applying the natural marking to the parabolics remain with source assembly.

Source: Aschbacher–Smith B.4.2, B.5.1 and B.5.6 (printed pp.86, 99 and 105),
as used before 13.6.14 and in 13.6.19, pp.929–931.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.ChapterB.SourceInduction
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.G2.MarkedAction.Recognition
/-- The full adequate alternatives recognize every literal component moved section. -/
theorem classified_component_action {D V : Type*} [Group D] [Finite D]
    [AddCommGroup V] [Module (ZMod 2) V] (ρ : Representation (ZMod 2) D V)
    {C : Subgroup D} (hC : IsComponent D C) {F : BinaryField}
    (mark : C ≃* Atlas.G2.Model F.Carrier) (sep : ModelSeparation F)
    (h : NontrivialAdequateAlternative ρ) (s : MovedSection (ρ.comp C.subtype) ⊤) :
    Nonempty (ActionEquiv s.action (binaryG2 F)) := by
  cases h with
  | quasisimple hq q => exact ClassifiedComponent.quasisimple_branch sep hC mark hq q s
  | symmetricThree c => exact (ClassifiedComponent.no_symmetricThree sep mark c).elim
  | twoFactors c => exact (ClassifiedComponent.no_twoFactors sep mark hC c).elim
  | outerSixThree c => exact (ClassifiedComponent.no_outerSixThree sep mark hC c).elim
  | hyperplane c => exact (ClassifiedComponent.no_hyperplane sep mark hC c).elim

/-- The requested specialization to the canonical moved/fixed quotient. -/
theorem classified_component_canonical_action {D V : Type*} [Group D] [Finite D]
    [AddCommGroup V] [Module (ZMod 2) V] (ρ : Representation (ZMod 2) D V)
    {C : Subgroup D} (hC : IsComponent D C) {F : BinaryField}
    (mark : C ≃* Atlas.G2.Model F.Carrier) (sep : ModelSeparation F)
    (h : NontrivialAdequateAlternative ρ) :
    Nonempty (ActionEquiv (MovedSection.ofNormal (ρ.comp C.subtype) ⊤).action (binaryG2 F)) :=
  classified_component_action ρ hC mark sep h _

open ComponentSelection
universe u
variable {G : Type u} [Group G] [Finite G]
variable (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
variable [IsElementaryAbelian 2 (WK K L T z v)]

/-- Apply the comparison to the actual offender actor containing the original component. -/
theorem classified_offender_component {𝒦 : GroupClass.{u}}
    (classification : AdequateClassificationInput.{u,u} 𝒦)
    (hW : WK K L T z v ≤ Tv T v)
    (hK : K ∈ Yz L T z v) (hn : Tv T v ≤ normalizer (K : Set G))
    (hSQ : IsSQTK 𝒦 (plusActor K L T v))
    (hR : pCore 2 (Gplus K L T z v hL hz) = ⊥)
    {F : BinaryField} (mark : plusImage K L T z v hL hz K ≃* Atlas.G2.Model F.Carrier)
    (sep : ModelSeparation F)
    (s : MovedSection ((offenderRepresentation K L T z v hL hz).comp
      (componentInOffender K L T z v hL hz).subtype) ⊤) :
    Nonempty (ActionEquiv s.action (binaryG2 F)) :=
  classified_component_action (offenderRepresentation K L T z v hL hz)
    (component_isComponent K L T z v hL hz hW hK hn hR)
    ((componentEquiv K L T z v hL hz hW hK hn).trans mark) sep
    (classify_nontrivial_offenderActor K L T z v hL hz hW classification hK hn hSQ hR) s

/-- The source local hypotheses supply containment and the SQTK cover for this action. -/
theorem source_offender_component_action {𝒦 : GroupClass.{u}}
    (classification : AdequateClassificationInput.{u,u} 𝒦)
    (hK : K ∈ Yz L T z v) (hn : Tv T v ≤ normalizer (K : Set G))
    (hU : Uv z v ≤ Tv T v) (hlocal : IsSQTK 𝒦 (Gv v))
    (hR : pCore 2 (Gplus K L T z v hL hz) = ⊥)
    {F : BinaryField} (mark : plusImage K L T z v hL hz K ≃* Atlas.G2.Model F.Carrier)
    (sep : ModelSeparation F) :
    Nonempty (ActionEquiv (MovedSection.ofNormal
      ((offenderRepresentation K L T z v hL hz).comp
        (componentInOffender K L T z v hL hz).subtype) ⊤).action (binaryG2 F)) := by
  have hW := (WK_le_Uv K L T z v hK.1.1).trans hU
  have hSQ : IsSQTK 𝒦 (plusActor K L T v) :=
    (IsSQTK.equiv (subgroupOfEquivOfLe (plusActor_le_Gv K L T v hK.1.1))).mp
      (hlocal.subgroup _)
  exact classified_offender_component K L T z v hL hz classification hW hK hn hSQ hR mark sep _

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.G2.MarkedAction.Recognition
