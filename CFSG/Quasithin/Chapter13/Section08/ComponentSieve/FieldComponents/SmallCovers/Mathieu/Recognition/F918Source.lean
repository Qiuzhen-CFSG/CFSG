module
public import CFSG.Quasithin.Chapter13.Section08.SourceDefs
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Basic
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Mathieu.Recognition.Contracts
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Mathieu.Recognition.F918Source.Inputs
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Mathieu.Recognition.F918Source.Models

/-!
# Constructing the M₂₂ central witness from F.9.18

Starting with the genuine placement setup and source quotient action,
we retain the earlier F.9.18(2–4),(7) outputs explicitly. The complete
case split proves the chosen Irr⁺ space invariant: the faithful action
image in (ii) has generalized Fitting subgroup M₂₂ and hence no FF-module;
the six concrete component models in (iii) have incompatible orders.

The actual K₀*T* actor equals H*. Absence of every finite faithful
FF-module for that actor discharges (7), giving I=[Ũ_H,K*]. The original
quadratic offender passes to the literal central quotient I/C_I(K*),
whose faithful action has the actual M₂₂ generalized Fitting subgroup.
The generic small-quadratic classification contract then recognizes its
code representation. No splitting of I is used.

`centralWitness_of_earlier` completes this conditional deduction. The
parent owns the source theorem and must supply `Earlier`, SQTK, and the
two generic B.4 consequences, then use the central-seed contradiction.
This module does not claim to prove the earlier F.9.18 or B.4 theorems.

Source: Aschbacher–Smith, F.9.18(2–4),(7), pp.325–326, and 13.8.21(2),
p.956 (1 March 2004 manuscript).
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Sporadic.Mathieu
open scoped IsMulCommutative
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Mathieu.Recognition.F918Source
universe u

/-- None of the full list of component models in F.9.18(4iii) is M₂₂. -/
theorem not_splitComponentModel {D : Type u} [Group D] (e : D ≃* M22) :
    ¬ SplitComponentModel D := by
  intro h
  cases h with
  | linearThree F f => exact not_linearThree F (e.symm.trans f)
  | symplecticFour F f => exact not_symplecticFour F (e.symm.trans f)
  | alternatingSix f => exact not_alternating_six (e.symm.trans f)
  | linearFour f => exact not_binary_linear 4 (Or.inl rfl) (e.symm.trans f)
  | linearFive f => exact not_binary_linear 5 (Or.inr rfl) (e.symm.trans f)
  | alternatingSeven f => exact not_alternating_seven (e.symm.trans f)

variable {G : Type u} [Group G] [Finite G]
  {H K L₁ T G₁ M V₃ V₁ : Subgroup G}
  [(V₁.subgroupOf (Source.UH H V₃)).Normal]
  [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]
  (s : Placement.Setup H K L₁ T G₁ M) (d : SourceAction H V₃ V₁)

include s in
omit [Finite G] in
/-- The product hypothesis of F.9.18 holds for the actual earlier L,
using K₀=K and H=KT. -/
theorem source_generation (L : Subgroup G) :
    H = conjugateSpanBy K T ⊔ ((L ⊔ T) ⊓ H) := by
  rw [component_orbit s]
  apply le_antisymm
  · rw [s.eq_component_join_sylow]
    exact sup_le le_sup_left ((le_inf (show T ≤ L ⊔ T from le_sup_right)
      (show T ≤ K ⊔ T from le_sup_right)).trans le_sup_right)
  · exact sup_le s.component_le inf_le_right

include s in
/-- An invariant Irr⁺ member is faithful on the whole source actor.
This is used on the actual Aut_{KT}(I) in alternative (ii). -/
theorem invariant_faithful (I : Subrepresentation d.representation)
    (hI : IsIrrPlus d.representation (Source.starImage H K) I.toSubmodule) :
    Function.Injective I.toRepresentation := by
  apply faithful_of_noncentral s I.toRepresentation
  intro hk
  apply hI.not_le_fixedSpace d.representation
  intro v hv k
  exact congrArg (fun w : I => (w : SourceSpace H V₃ V₁))
    ((actionHom_eq_one_iff I.toRepresentation k).mp (hk k.property) ⟨v, hv⟩)

/-- Derive case (i): (ii) contradicts the no-FF contract on its actual
faithful action image, and every actor in (iii) is excluded by its order. -/
theorem case_i {𝒦 : GroupClass.{u}} (hH : IsSQTK 𝒦 H) (hno : NoFaithfulFF 𝒦)
    (I : Submodule (ZMod 2) (SourceSpace H V₃ V₁))
    (hI : IsIrrPlusWith d.representation (Source.starImage H K) (Source.starImage H T) I)
    (h : FourAlternatives s d I hI) :
    (⊤ : Subgroup (Source.Hstar H)) ≤ subspaceStabilizer d.representation I := by
  cases h with
  | invariant hs => exact hs
  | ff hs hff =>
      let W := stableSubrepresentation s d I hI.invariant hs
      exact (no_ff_image s hH hno I W.toRepresentation
        (invariant_faithful s d W hI.isIrrPlus) hff).elim
  | split a =>
      exact (not_splitComponentModel
        (Placement.starCoordinates H K s.component_le s.component s.model)
        (SplitAction.componentModel d.representation (Source.starImage H K) I a.action)).elim

/-- Assemble the source central witness. The input consists of the genuine
placement, the actual source action, SQTK, complete relevant earlier F.9.18
outputs, and the two generic classification contracts. Invariance is
proved by the full case split. F.9.18(7) receives absence of all faithful
FF-modules for K₀*T*, and the actual offender gives the code recognition
on I/C_I(K). No conclusion-bearing invariant or moved-space premise is used. -/
theorem centralWitness_of_earlier {𝒦 : GroupClass.{u}}
    (hH : IsSQTK 𝒦 H) (hno : NoFaithfulFF 𝒦) (hcode : SmallQuadraticCode 𝒦)
    {L : Subgroup G} (h : Earlier s d L) : Nonempty (CentralWitness s d) := by
  have hs := case_i s d hH hno h.I h.irrPlus h.alternatives
  let I : Subrepresentation d.representation :=
    ⟨h.I, fun g _ hv => (hs (mem_top g) _).2 hv⟩
  refine ⟨⟨I, h.irrPlus.isIrrPlus, ?_, ?_⟩⟩
  · exact (orbitSpan_eq_self d.representation hs).symm.trans
      (h.saturation (no_ff_actor s hH hno))
  · exact central_code s d hH hcode I h.irrPlus.isIrrPlus
      (Source.starImage H h.B) h.elementary h.quadratic h.bound
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Mathieu.Recognition.F918Source
