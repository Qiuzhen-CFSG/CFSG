module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Solvable.Construction.Exceptional.SourceAction.Recovery
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.PreciseMultiplierInputs.Cover

/-!
# The cubic plane from the precise earlier B.5 inputs

A.3.6 supplies the lifted center bound in the genuine B.5.2 cover. The
marked A₆ factor rules out central Fitting. Its order already excludes the
binary derived G₂ model, so the proved B.5.7 module comparison and offender
endgame give the cubic plane without any multiplier-table premise.

Only B.5.1, B.5.2, preparation B.5.5, A.2.1 and A.3.6 remain explicit.
Their producers are qt-b05-quasisimple, qt-b05-quotient-components,
qt-a-02 and qt-a03-sqtk-structure, also required by qt-b05-general-classification.
The following Planes consumer transports this dimension to the original
13.6.10 cubic. No global fixed-space splitting is asserted.
Source: Aschbacher–Smith, B.5.7, p.106; 13.6.10, p.928 (1 March 2004).
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Subnormal.Classification.AdequateSource
open ChapterB ChapterB.QuasisimpleSource ChapterB.SourceInduction
open ChapterB.SourceInduction.HighThreeRank
open CoverCentralizer CoverCentralizer.SourceConstruction
open ComponentReduction ModuleCalculation ModuleCalculation.NaturalCentralizers
open Solvable.Construction.Exceptional
universe u v

/-- Exactly the earlier implications consumed by the cubic-plane proof.
No adequate classifier or local module conclusion is a field. -/
structure EarlierSources (K : GroupClass.{u}) : Prop where
  quasisimple : ProjectiveLine.QuasisimpleClassificationInput.{u,v} K
  cover : CoverInput K
  preparation : PreliminaryActions.Preparation.ComponentInput.{u,v} K
  semisimple : SemisimpleInput K
  components : Chapter1.Section02.A36Input K

/-- Reconstruct the dimension of the specified cubic moved space using the
actual cover and marked A₆ factor, with no complete multiplier-table input. -/
theorem outer_moved_plane {D : Type u} [Group D] [Finite D]
    {W : Type v} [AddCommGroup W] [Module (ZMod 2) W]
    (c : OuterSixThreeShape D) (ρ : Representation (ZMod 2) D W)
    {K : GroupClass.{u}} (earlier : EarlierSources.{u,v} K)
    (hyp : FFHypothesis K ρ) : Module.finrank (ZMod 2) (moved ρ c.second) = 2 := by
  have hL := SourceAction.first_component c
  have hr := SourceAction.first_rank c
  obtain ⟨dc⟩ := PreciseMultiplierInputs.liftedCover_of_preparation ρ earlier.cover
    earlier.preparation earlier.semisimple earlier.components hyp hL hr
  obtain ⟨d⟩ : Nonempty (NoncentralContext K D c.first) := by
    rcases reduction_of_liftedCover hyp hL hr dc with h | h
    · exact (SourceAction.fitting_not_central c h.2).elim
    · exact h
  obtain ⟨A, hA, hm, _, _⟩ := exists_moving_offender ρ hyp hL d
  have hnot : ¬ Nonempty (c.first ≃* commutator (Atlas.G2.Model (ZMod 2))) := by
    rintro ⟨e⟩
    have hc : Nat.card c.first = 360 := by
      rw [Nat.card_congr c.firstEquiv.toEquiv, nat_card_alternatingGroup]
      norm_num
    have hg := (Nat.card_congr e.toEquiv).trans
      Atlas.G2.LieAutomorphismExtensions.card_binaryDerived
    omega
  obtain ⟨r⟩ := NaturalReduction.ModelComparison.reduced_of_no_binaryG2_component
    earlier.quasisimple ρ hyp hL hr d hA hm hnot
  obtain ⟨m⟩ := NaturalReduction.model_of_reduced ρ hyp hL d hm r
  have hf := threeCore_fixes_model ρ ConcreteModels.modelCommutants hL d m
  have e := source_offender_plane ρ hyp hL d hA hm hf m
  obtain ⟨cc⟩ := cubicCentralizers_of_offender_conclusion ρ hyp hL d m e
  have hX : c.second = pCore 3 D := eq_of_le_of_card_ge (SourceAction.second_le_threeCore c) (by
    rw [SourceAction.second_card c, Nat.card_congr cc.threeCoreEquiv.toEquiv]
    exact le_of_eq (Nat.card_zmod 3))
  rw [hX]
  exact e.plane

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Subnormal.Classification.AdequateSource
