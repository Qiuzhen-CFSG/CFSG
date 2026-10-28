module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.LinearThree.MarkedAction.FlagTypes.Preparation
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.LinearThree.MarkedAction.FlagTypes.ComponentAction.Restriction
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.LinearThree.MarkedAction.FlagTypes.ComponentAction.Quasisimple
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.LinearThree.MarkedAction.FlagTypes.ComponentAction.ProductRows

/-!
# Extracting the repeated natural action of the actual plus component

Elementary abelianness of W_K follows from W_K ≤ Uᵥ. The plus component is
normal and quasisimple inside the actual offender subgroup. Thus the S₃
alternative is impossible, and in the quasisimple alternative the classified
generalized Fitting subgroup is precisely the original plus component.

The canonical moved quotient for the restricted offender action is identified
with the published plusComponentSection, retaining the actual component map
and binary linear intertwiner. The quasisimple and two-factor alternatives
give repeated natural SL₃ coordinates on this quotient; the outer and
hyperplane alternatives are excluded by their actual group structures.
Thus the full adequate classifier supplies the repeated-natural existential
used by flag exclusion, with no extra component-action hypothesis. Its group
marking remains arbitrary, permitting the dual coordinate choice. The full
adequate classification input remains explicit, as the earlier-source input.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, the B.5.6
application preceding 13.6.14, printed p.929, and its use in 13.6.19, p.931.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.LinearThree.MarkedAction
open ComponentSelection ChapterB.QuasisimpleSource ChapterB.SourceInduction
universe u
variable {G : Type u} [Group G] [Finite G]
variable (K L T : Subgroup G) (z v : G)
variable (hL : Tv T v ≤ normalizer (Lv L v : Set G))
variable (hz : Tv T v ≤ centralizer ({z} : Set G))
variable [IsElementaryAbelian 2 (Uv z v)]

/-- The literal plus component remains a normal component of the actual offender
actor. The elementary instance on W_K is derived from the source Uᵥ hypothesis. -/
theorem plus_component_offender_data (hK : K ∈ Yz L T z v)
    (hn : Tv T v ≤ normalizer (K : Set G))
    (hU : Uv z v ≤ (Gv v).pCoreIn 2)
    (hSyl : Chapter1.IsSylowIn 2 (Tv T v) (Gv v))
    (hcore : pCore 2 (Gplus K L T z v hL hz) = ⊥) :
    letI : IsElementaryAbelian 2 (WK K L T z v) :=
      IsElementaryAbelian.of_le (WK_le_Uv K L T z v hK.1.1)
    let ρ := plusRepresentation K L T z v hL hz
    let I := offenderSubgroup ρ
    let C := plusImage K L T z v hL hz K
    C ≤ I ∧ (C.subgroupOf I).Normal ∧ IsComponent I (C.subgroupOf I) := by
  let : IsElementaryAbelian 2 (WK K L T z v) :=
    IsElementaryAbelian.of_le (WK_le_Uv K L T z v hK.1.1)
  let ρ := plusRepresentation K L T z v hL hz
  let I := offenderSubgroup ρ
  let C := plusImage K L T z v hL hz K
  have hCI : C ≤ I := plus_component_le_offender K L T z v hL hz hK hn hU hSyl
  let : C.Normal := plus_component_normal K L T z v hL hz hK hn
  let : IsQuasisimple C := plusImage_K_quasisimple K L T z v hL hz hK hcore
  exact ⟨hCI, inferInstance, (inferInstance : (C.subgroupOf I).Normal).isSubnormal,
    IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe hCI).symm⟩

/-- All surviving source alternatives refer to the original component. In the
first branch no independent identification with the generalized Fitting subgroup
is required. The product and extension alternatives are retained in full. -/
theorem plus_component_classifier_cases
    {𝒦 : GroupClass.{u}} (source : AdequateClassificationInput.{u,u} 𝒦)
    (hSQ : IsSQTK 𝒦 (Gv v)) (hK : K ∈ Yz L T z v)
    (hn : Tv T v ≤ normalizer (K : Set G))
    (hU : Uv z v ≤ (Gv v).pCoreIn 2)
    (hSyl : Chapter1.IsSylowIn 2 (Tv T v) (Gv v))
    (hcore : pCore 2 (Gplus K L T z v hL hz) = ⊥) :
    letI : IsElementaryAbelian 2 (WK K L T z v) :=
      IsElementaryAbelian.of_le (WK_le_Uv K L T z v hK.1.1)
    let ρ := plusRepresentation K L T z v hL hz
    let I := offenderSubgroup ρ
    let C := plusImage K L T z v hL hz K
    Nonempty (ProjectiveLine.QuasisimpleSourceConclusion (ρ.comp I.subtype)
      (C.subgroupOf I)) ∨
      Nonempty (SourceTwoFactorCase (ρ.comp I.subtype)) ∨
      Nonempty (ChapterB.OuterSixThreeShape I) ∨
      Nonempty (HyperplaneCase (ρ.comp I.subtype)) := by
  let : IsElementaryAbelian 2 (WK K L T z v) :=
    IsElementaryAbelian.of_le (WK_le_Uv K L T z v hK.1.1)
  exact ComponentAction.classifier_at_component
    (plus_component_offender_data K L T z v hL hz hK hn hU hSyl hcore).2.2
    (plus_nontrivial_offender_classification K L T z v hL hz source hSQ hK hn hU hSyl hcore)

/-- A repeated natural identification on any construction of the offender
component's moved section gives the exact existential consumed by flag exclusion.
This is a transport theorem; its classification premise still needs extraction. -/
theorem plus_component_repeated_of_offender_section (hK : K ∈ Yz L T z v)
    (hn : Tv T v ≤ normalizer (K : Set G))
    (hU : Uv z v ≤ (Gv v).pCoreIn 2)
    (hSyl : Chapter1.IsSylowIn 2 (Tv T v) (Gv v)) :
    letI : IsElementaryAbelian 2 (WK K L T z v) :=
      IsElementaryAbelian.of_le (WK_le_Uv K L T z v hK.1.1)
    let ρ := plusRepresentation K L T z v hL hz
    let I := offenderSubgroup ρ
    let C := plusImage K L T z v hL hz K
    ∀ t : MovedSection (ρ.comp I.subtype) (C.subgroupOf I),
      (∃ (E : BinaryField) (r : ℕ), 0 < r ∧
        IsRepeatedLinearNatural (t.action.comp (C.subgroupOf I).subtype) E 3 r) →
      ∃ (E : BinaryField) (r : ℕ), 0 < r ∧
        IsRepeatedLinearNatural
          ((plusComponentSection K L T z v hL hz hK hn).action.comp C.subtype) E 3 r := by
  let : IsElementaryAbelian 2 (WK K L T z v) :=
    IsElementaryAbelian.of_le (WK_le_Uv K L T z v hK.1.1)
  intro ρ I C t h
  have hCI : C ≤ I := plus_component_le_offender K L T z v hL hz hK hn hU hSyl
  obtain ⟨E, r, hr, he⟩ := h
  exact ⟨E, r, hr, ComponentAction.repeated_of_restrictedSection
    (plusComponentSection K L T z v hL hz hK hn) I hCI t E 3 r he⟩

/-- The full adequate B.5.6 classifier identifies the canonical plus component
quotient with repeated copies of one natural SL₃ action. This discharges the
component-module premise of flag-type exclusion in 13.6.19. The elementary
structure on W_K is inherited from Uᵥ, and the existential action marking need
not agree with the supplied group isomorphism `e`. -/
theorem plus_component_repeated_natural
    {𝒦 : GroupClass.{u}} (source : AdequateClassificationInput.{u,u} 𝒦)
    (hSQ : IsSQTK 𝒦 (Gv v)) (hK : K ∈ Yz L T z v)
    (hn : Tv T v ≤ normalizer (K : Set G))
    (hU : Uv z v ≤ (Gv v).pCoreIn 2)
    (hSyl : Chapter1.IsSylowIn 2 (Tv T v) (Gv v))
    (hcore : pCore 2 (Gplus K L T z v hL hz) = ⊥)
    {F : Type*} [Field F] [Finite F] [CharP F 2] {m : ℕ}
    (hF : Nat.card F = 2 ^ m) (hm : 1 < m)
    (e : plusImage K L T z v hL hz K ≃* SL(3, F)) :
    letI : IsElementaryAbelian 2 (WK K L T z v) :=
      IsElementaryAbelian.of_le (WK_le_Uv K L T z v hK.1.1)
    let C := plusImage K L T z v hL hz K
    let s := plusComponentSection K L T z v hL hz hK hn
    ∃ (E : BinaryField) (r : ℕ), 0 < r ∧
      IsRepeatedLinearNatural (s.action.comp C.subtype) E 3 r := by
  let : IsElementaryAbelian 2 (WK K L T z v) :=
    IsElementaryAbelian.of_le (WK_le_Uv K L T z v hK.1.1)
  intro C s
  rcases plus_component_classifier_cases K L T z v hL hz source hSQ hK hn hU hSyl hcore
    with h | h
  · obtain ⟨c⟩ := h
    exact plus_component_repeated_of_quasisimple K L T z v hL hz hK hn hU hSyl hF hm e c
  · exact ComponentAction.ProductRows.plus_repeated_of_product_cases
      K L T z v hL hz hK hn hU hSyl hcore hF hm e h

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.LinearThree.MarkedAction
