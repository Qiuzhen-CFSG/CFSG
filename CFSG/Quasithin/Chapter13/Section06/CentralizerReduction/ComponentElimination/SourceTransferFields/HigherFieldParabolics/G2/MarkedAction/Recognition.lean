module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.G2.MarkedAction.Recognition.Thompson
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.G2.MarkedAction.Recognition.SectionTransport
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.G2.MarkedAction.Recognition.ModelContract
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.G2.MarkedAction.Recognition.ClassifiedComponent
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.G2.MarkedAction.Recognition.ModelSeparation

/-!
# Recognition of the higher-field G₂ moved quotient

The literal W_K action restricts to its best-offender actor, containing K⁺
by the Y_z commutator relation and the maximum-elementary calculation. The
earlier U_v containment, SQTK condition and R₂ two-core condition supply
every hypothesis needed to apply the complete adequate B.5.6 classifier.
The component and its original group marking are retained in that actor.

The exhaustive comparison of all adequate B.5 alternatives, using the proved
model separation, recognizes the component's natural G₂ action. Transport
through the original K⁺ parametrization constructs a `NaturalMarking` on the
published `MarkedAction.quotientRepresentation`, preserving the actual fixed
kernel and linear intertwiner. Its conjugation transport then supplies the
moving nonshort parabolic for the G₂ branch of 13.6.19.

The earlier universal B.5 classification, U_v containment, SQTK and R₂ inputs
remain explicit for the centralizer-reduction assembly. The parabolic
application also retains the independently owned literal two-group kernel
premise. No selected action row, model separation, irreducibility or natural
marking remains an input.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, the paragraph
preceding 13.6.14 and Lemma 13.6.19, printed pp.929–931; B.5.1 and B.5.6.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.G2.MarkedAction.Recognition
open ComponentSelection ChapterB.QuasisimpleSource ChapterB.SourceInduction
private def inverseActionEquiv {D E V W : Type*} [Group D] [Group E]
    [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) D V} {σ : Representation (ZMod 2) E W}
    (e : ActionEquiv ρ σ) : ActionEquiv σ ρ where
  groupEquiv := e.groupEquiv.symm
  linearEquiv := e.linearEquiv.symm
  intertwines g w := by
    apply e.linearEquiv.injective
    rw [e.linearEquiv.apply_symm_apply, e.intertwines,
      e.groupEquiv.apply_symm_apply, e.linearEquiv.apply_symm_apply]

universe u
variable {G : Type u} [Group G]
variable (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
variable [IsElementaryAbelian 2 (WK K L T z v)]

/-- The canonical component quotient in the actor to which B.5 is applied. -/
def offenderComponentSection :=
  MovedSection.ofNormal ((offenderRepresentation K L T z v hL hz).comp
    (componentInOffender K L T z v hL hz).subtype) ⊤

/-- The original K⁺ parametrization identifies the two literal moved quotients.
This equivalence has no model-recognition or irreducibility premise. -/
def offenderSectionEquiv [Finite G] (hW : WK K L T z v ≤ Tv T v)
    (hK : K ∈ Yz L T z v) (hn : Tv T v ≤ normalizer (K : Set G)) :
    ActionEquiv (offenderComponentSection K L T z v hL hz).action
      (quotientRepresentation K L T z v hL hz) :=
  reparametrizeMovedSection (componentEquiv K L T z v hL hz hW hK hn)
    (fun _ _ => rfl) (offenderComponentSection K L T z v hL hz)
      (movedSection K L T z v hL hz)

/-- Source-specialized preparation: the classifier acts on the actual offender
subgroup, and the original marked component remains a component inside it. -/
theorem prepared_source [Finite G] {𝒦 : GroupClass.{u}}
    (classification : AdequateClassificationInput.{u,u} 𝒦)
    (hK : K ∈ Yz L T z v) (hn : Tv T v ≤ normalizer (K : Set G))
    (hU : Uv z v ≤ Tv T v) (hlocal : IsSQTK 𝒦 (Gv v))
    (hR : pCore 2 (Gplus K L T z v hL hz) = ⊥)
    {F : BinaryField} (e : plusImage K L T z v hL hz K ≃* Atlas.G2.Model F.Carrier) :
    NontrivialAdequateAlternative (offenderRepresentation K L T z v hL hz) ∧
      Theory.GroupTheory.IsComponent (offenderActor K L T z v hL hz)
        (componentInOffender K L T z v hL hz) ∧
      Nonempty (componentInOffender K L T z v hL hz ≃* Atlas.G2.Model F.Carrier) := by
  have hW := (WK_le_Uv K L T z v hK.1.1).trans hU
  have hSQ : IsSQTK 𝒦 (plusActor K L T v) :=
    (IsSQTK.equiv (subgroupOfEquivOfLe (plusActor_le_Gv K L T v hK.1.1))).mp
      (hlocal.subgroup _)
  exact ⟨classify_nontrivial_offenderActor K L T z v hL hz hW classification hK hn hSQ hR,
    component_isComponent K L T z v hL hz hW hK hn hR,
    ⟨(componentEquiv K L T z v hL hz hW hK hn).trans e⟩⟩

open scoped MatrixGroups

/-- The full adequate B.5 alternatives recognize the literal moved/fixed quotient
as the natural G₂ module. The original W_K need not be irreducible.
The universal classification, U_v containment, SQTK and R₂ inputs are the
earlier-source obligations of `qt-13-06-centralizer-reduction`. -/
theorem naturalMarking_of_source [Finite G] {𝒦 : GroupClass.{u}}
    (classification : AdequateClassificationInput.{u,u} 𝒦)
    (hK : K ∈ Yz L T z v) (hn : Tv T v ≤ normalizer (K : Set G))
    (hU : Uv z v ≤ Tv T v) (hlocal : IsSQTK 𝒦 (Gv v))
    (hR : pCore 2 (Gplus K L T z v hL hz) = ⊥)
    {F : BinaryField} (hF : 1 < F.degree)
    (mark : plusImage K L T z v hL hz K ≃* Atlas.G2.Model F.Carrier) :
    Nonempty (NaturalMarking K L T z v hL hz F) := by
  obtain ⟨e⟩ := source_offender_component_action K L T z v hL hz
    classification hK hn hU hlocal hR mark (modelSeparation_of_degree_gt_one F hF)
  let t := offenderSectionEquiv K L T z v hL hz
    ((WK_le_Uv K L T z v hK.1.1).trans hU) hK hn
  exact ⟨ClassifiedComponent.compose (inverseActionEquiv t) e⟩

/-- The recognized quotient supplies the Sylow-aligned marking and moving
nonshort parabolic required in the G₂ branch of 13.6.19. Only the literal
relative-centralizer two-group premise remains for the independent kernel
argument, in addition to the stated earlier-source inputs. -/
theorem exists_moving_nonshort_parabolic_of_source [Finite G] {𝒦 : GroupClass.{u}}
    (classification : AdequateClassificationInput.{u,u} 𝒦)
    (hK : K ∈ Yz L T z v) (hn : Tv T v ≤ normalizer (K : Set G))
    (hU : Uv z v ≤ Tv T v) (hlocal : IsSQTK 𝒦 (Gv v))
    (hR : pCore 2 (Gplus K L T z v hL hz) = ⊥)
    {F : BinaryField} (hF : 1 < F.degree)
    (mark : plusImage K L T z v hL hz K ≃* Atlas.G2.Model F.Carrier)
    (hk : IsPGroup 2 ((centralizer (WK K L T z v : Set G)).subgroupOf K)) :
    ∃ (e : NaturalMarking K L T z v hL hz F) (i : Fin 2),
      let P := liftedParabolic K L T z v hL hz e.groupEquiv i
      P ≤ Gv v ∧ P ≤ K ∧ Tv T v ⊓ K ≤ P ∧ IsCoatom (P.subgroupOf K) ∧
        ¬ residualIn P ≤ centralizer ({z} : Set G) ∧
        ¬ ChapterC.IsShort (residualIn P) ∧
        Nonempty ((residualIn P ⧸ pCore 2 (residualIn P)) ≃* PSL(2,F.Carrier)) ∧
        Nonempty ((plusImage K L T z v hL hz (residualIn P) ⧸
          pCore 2 (plusImage K L T z v hL hz (residualIn P))) ≃* PSL(2,F.Carrier)) := by
  obtain ⟨e⟩ := naturalMarking_of_source K L T z v hL hz
    classification hK hn hU hlocal hR hF mark
  exact exists_moving_nonshort_parabolic_of_marking hF e hK hn hk


end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.G2.MarkedAction.Recognition
