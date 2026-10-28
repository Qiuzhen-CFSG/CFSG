module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.SmallOffender.Recognition.ModelBounds.Suzuki
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.SmallOffender.Recognition.ModelBounds.Orthogonal
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.SmallOffender.Recognition.ModelBounds.ScalarNaturals
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.SmallOffender.Recognition.Completion.QuietRows
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.SmallOffender.Recognition.ModelBounds.FourNaturalCrossed

/-!
# Original small-offender assembly from concrete quiet markings

Every listed marking now supplies its own crossed centralization under the
original source prefix, including the four-natural-copy row. The numerical
and fixed-space exclusions leave the natural SL₃(2) survivor with unchanged
full module and w≥2.

The remaining local obligation is to construct the quiet-row markings; it
stays with qt-d-10-nona5-small-offender. The genuine HalfSylowUniqueAt input
retains qt-d-10-nona5-half-sylow-unique as producer and its final discharge
by qt-d-10-nona5-point-control. This conditional assembly does not claim
unconditional source recognition.
Source: Aschbacher--Smith 10.1.1--2 and 10.2.12, printed pp.741--742,754--755.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SmallOffender.Recognition
open Chapter3.Section02 PointControl.Selection
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G}

/-- The original survivor consumer, retaining only quiet marking selection and the earlier half-Sylow input. -/
theorem nonnormalSmallOffender_of_quiet_marked_rows_and_halfSylow
    (hhalf : PointControl.HalfSylowUniqueAt T)
    (hquiet : ∀ (L : Subgroup G) (D : FundamentalSetup KnownSimple.IsKnownSimple T L) (g : G),
      Configuration T D g →
      Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G) →
      ∃ E : FundamentalSetup KnownSimple.IsKnownSimple T L,
        E.fullModule ≤ D.fullModule ∧
        (BinaryThreeNatural E ∨ RankOneNatural E ∨ NaturalDualRow E ∨
          FourNaturalRow E ∨
          OrthogonalFourMinusRow E ∨ SuzukiNaturalRow E)) :
    SourceNonnormalSmallOffenderAt T := by
  apply nonnormalSmallOffender_of_quiet_models_and_halfSylow hhalf
  intro L D g c hJ
  obtain ⟨E,hE,hrow⟩ := hquiet L D g c hJ
  obtain ⟨he,cE⟩ := c.reselect E hE
  have hNL : normalizer (L : Set G) ≤ E.maximalLocal :=
    PointControl.component_normalizer_le_of_halfSylowUnique E cE.nonnormal
      (hhalf cE.many L E cE.nonnormal cE.notA5)
  rcases hrow with hnatural | hrank | hdual | hfour | horth | hsuzuki
  · obtain ⟨e,⟨mark⟩⟩ := hnatural
    exact ⟨E,hE,Or.inl ⟨⟨ModuleChoice.full_eq_local_of_binaryThreeNatural E cE.nonnormal
      ⟨e,⟨mark⟩⟩,e,mark,fun _ ht htn => binary_three_crossed_of_marking E ⟨e,⟨mark⟩⟩ ht htn⟩⟩⟩
  · exact (no_rank_one_natural_of_small_offender E cE hrank
      (fun _ ht htn => rank_one_crossed_of_marking E hrank ht htn) hNL).elim
  · exact (no_natural_dual_of_small_offender E cE hdual hNL).elim
  · exact (no_four_natural_of_configuration E cE hfour hNL).elim
  · exact (no_orthogonal_of_small_offender E cE horth hNL).elim
  · exact (no_suzuki_natural_of_small_offender E cE hsuzuki hNL).elim

end CFSG.Quasithin.Chapter10.SmallOffender.Recognition
