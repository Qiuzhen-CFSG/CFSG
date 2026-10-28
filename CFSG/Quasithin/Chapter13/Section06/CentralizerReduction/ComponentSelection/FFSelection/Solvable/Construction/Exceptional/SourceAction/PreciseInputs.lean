module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Solvable.Construction.Exceptional.SourceAction
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.HighThreeRank.ModuleCalculation.NaturalReduction.ModelComparison.BinaryG2Exclusion.TernaryKernel

/-!
# The Chapter 13.6 outer action from five earlier source inputs

The actual prepared SQTK cover and A.3.6 give the lifted component and its
center bound. The original cubic factor excludes the central-Fitting branch.
The proved alternating-eight and binary-G₂ perfect-kernel results then give
the marked natural or augmentation-core six-point module. The established
centralizer and coordinate constructions return the complete original
`Recovered` and `RecoveredAction` records, including their fixed/moved
complement and the common parity-actor coordinates.

The star applications keep the literal `starMk`, its SQTK source, and the
original offender restriction. All five earlier statements remain explicit:
B.5.1, B.5.2, A.2.1, B.5.5 and A.3.6. Their existing producers are
`qt-b05-quasisimple`, `qt-b05-quotient-components`, `qt-a-02` and
`qt-a03-sqtk-structure`; final discharge belongs to the Chapter 13.6 assembly.

Source: Aschbacher--Smith B.5.7, printed p.106, and 13.6.13, printed p.929.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable.Construction.Exceptional.SourceAction
open ChapterB ChapterB.QuasisimpleSource ChapterB.SourceInduction ChapterB.SourceInduction.HighThreeRank
open ModuleCalculation ModuleCalculation.NaturalCentralizers
open CoverCentralizer.SourceConstruction
open CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives
universe u v

/-- The five complete earlier source statements used by this construction. -/
structure PreciseInputs (K : GroupClass.{u}) : Prop where
  quasisimple : ProjectiveLine.QuasisimpleClassificationInput.{u,v} K
  cover : CoverInput K
  semisimple : SemisimpleInput K
  preparation : ComponentReduction.PreliminaryActions.Preparation.ComponentInput.{u,v} K
  structure36 : Chapter1.Section02.A36Input K

variable {G : Type u} [Group G] [Finite G] (c : ChapterB.OuterSixThreeShape G)
variable {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
variable (ρ : Representation (ZMod 2) G V) {K : GroupClass.{u}}

/-- Construct the actual noncentral cover from the five earlier statements. -/
theorem noncentral_context_of_precise_inputs (earlier : PreciseInputs.{u,v} K)
    (hyp : FFHypothesis K ρ) : Nonempty (NoncentralContext K G c.first) := by
  obtain ⟨d⟩ := PreciseMultiplierInputs.liftedCover_of_preparation ρ
    earlier.cover earlier.preparation earlier.semisimple earlier.structure36
    hyp (first_component c) (first_rank c)
  rcases CoverCentralizer.reduction_of_liftedCover
    hyp (first_component c) (first_rank c) d with h | h
  · exact (fitting_not_central c h.2).elim
  · exact h

/-- Recover every original field, retaining the augmentation-core fixed line
and the original component, cubic factor and moving offender. -/
theorem recover_of_precise_inputs (earlier : PreciseInputs.{u,v} K)
    (hyp : FFHypothesis K ρ) :
    Nonempty (Recovered c ρ) := by
  obtain ⟨d⟩ := noncentral_context_of_precise_inputs c ρ earlier hyp
  let : c.first.Normal := d.normal
  have hL := first_component c
  obtain ⟨A, hA, hm, _, _⟩ := exists_moving_offender ρ hyp hL d
  obtain ⟨r⟩ := NaturalReduction.ModelComparison.reduced_of_threeFreePerfectKernels
    earlier.quasisimple
    NaturalReduction.ModelComparison.alternatingEight_threeFreePerfectKernels
    NaturalReduction.ModelComparison.binaryG2_threeFreePerfectKernels
    ρ hyp hL (first_rank c) d hA hm
  obtain ⟨m⟩ := NaturalReduction.model_of_reduced ρ hyp hL d hm r
  have hf := threeCore_fixes_model ρ ConcreteModels.modelCommutants hL d m
  let e := source_offender_plane ρ hyp hL d hA hm hf m
  obtain ⟨cc⟩ := cubicCentralizers_of_offender_conclusion ρ hyp hL d m e
  have hX : c.second = pCore 3 G := eq_of_le_of_card_ge (second_le_threeCore c) (by
    rw [second_card c, Nat.card_congr cc.threeCoreEquiv.toEquiv]
    exact le_of_eq (Nat.card_zmod 3))
  have hdec := threeCore_moved_decomposition ρ hL d hf
  have hs : (c.first ⊔ A) ⊔ c.second = ⊤ ∧
      Disjoint (c.first ⊔ A) c.second ∧ c.first.relIndex (c.first ⊔ A) = 2 := by
    rw [hX, ← cc.component_centralizer]
    rcases e.marking with hn | hc
    · obtain ⟨b⟩ := hn
      exact marked_symmetric_supplement ρ m
        (BinaryPermutation.naturalRepresentation (Fin 6))
        CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.NaturalSix.symmetricAction_injective
        CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.NaturalSix.normalizer_alternatingImage b
    · obtain ⟨b⟩ := hc
      exact marked_symmetric_supplement ρ m
        (BinaryPermutation.coreRepresentation (Fin 6))
        CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.NaturalSix.coreAction_injective
        ConcreteModels.core_six_normalizer b
  refine ⟨{
    offender := A
    best := hA
    model := m
    marking := e.marking
    second_eq := hX
    plane := by rw [hX]; exact e.plane
    component_centralizer := cc.component_centralizer.trans hX.symm
    cubic_centralizer := by rw [hX]; exact cc.threeCore_centralizer
    rank_eq := e.rank_eq
    component_fixedCodim_eq := e.component_fixedCodim_eq
    first_fixed := by rw [hX]; exact hf
    second_fixed := by rw [hX]; exact hdec.2.2
    moved_product := by rw [hX]; exact hdec.1
    disjoint := by rw [hX]; exact hdec.2.1
    cubic_complement := odd_moved_complement ρ c.second (by rw [second_card c]; decide)
    supplement := hs.1
    supplement_disjoint := hs.2.1
    component_index := hs.2.2 }⟩

/-- Both ambient intertwiners use the common recovered parity coordinates. -/
theorem recover_action_of_precise_inputs (earlier : PreciseInputs.{u,v} K)
    (hyp : FFHypothesis K ρ) : Nonempty (RecoveredAction c ρ) := by
  obtain ⟨d⟩ := recover_of_precise_inputs c ρ earlier hyp
  obtain ⟨a⟩ := coordinates c ρ hyp d
  exact ⟨⟨d, a⟩⟩

/-- The source recovery on the literal star quotient and offender action. -/
theorem recover_star_offender_of_precise_inputs (z v : G)
    [IsElementaryAbelian 2 (Uv z v)]
    {K : GroupClass.{u}} (earlier : PreciseInputs.{u,u} K)
    (hlocal : IsSQTK K (Gv v)) (hcore : pCore 2 (Gstar z v) = ⊥)
    (c : ChapterB.OuterSixThreeShape (FFFactors.offenderActor (starRepresentation z v))) :
    Nonempty (OffenderRecovered (D := Gstar z v) (W := Additive (Uv z v))
      (starRepresentation z v) c) := by
  let : Module.Finite (ZMod 2) (Additive (Uv z v)) := Module.Finite.of_finite
  have h := FFFactors.offender_hypothesis (starRepresentation z v)
    (starMk z v) (starMk_surjective z v) hlocal
    (starRepresentation_injective z v) hcore
  have hyp : FFHypothesis K (FFFactors.offenderRepresentation (starRepresentation z v)) := by
    refine ⟨h.finite_module, h.faithful, h.twoCore, h.generated, ?_⟩
    obtain ⟨d⟩ := h.quotient
    let := d.coverGroup
    let := d.coverFinite
    let := d.kernelNormal
    exact ⟨{ Cover := d.Cover, kernel := d.kernel, sqtk := d.sqtk, equiv := d.equiv }⟩
  exact recover_of_precise_inputs c
    (FFFactors.offenderRepresentation (starRepresentation z v)) earlier hyp

/-- The complete recovered star action, with both original ambient
intertwiners and every recovered local field. -/
theorem recover_star_offender_action_of_precise_inputs (z v : G)
    [IsElementaryAbelian 2 (Uv z v)]
    {K : GroupClass.{u}} (earlier : PreciseInputs.{u,u} K)
    (hlocal : IsSQTK K (Gv v)) (hcore : pCore 2 (Gstar z v) = ⊥)
    (c : ChapterB.OuterSixThreeShape (FFFactors.offenderActor (starRepresentation z v))) :
    Nonempty (RecoveredAction c
      (FFFactors.offenderRepresentation (starRepresentation z v))) := by
  obtain ⟨d⟩ := recover_star_offender_of_precise_inputs z v earlier hlocal hcore c
  obtain ⟨a⟩ := coordinates_star_offender z v hlocal hcore c d
  exact ⟨⟨d, a⟩⟩

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable.Construction.Exceptional.SourceAction
