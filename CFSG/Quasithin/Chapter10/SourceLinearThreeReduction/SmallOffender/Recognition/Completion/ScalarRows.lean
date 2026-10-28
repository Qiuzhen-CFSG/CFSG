module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.SmallOffender.Recognition.ModelBounds.Suzuki
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.SmallOffender.Recognition.ModelBounds.Orthogonal
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.SmallOffender.Recognition.ModelBounds.ScalarNaturals
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.SmallOffender.Recognition.Completion.QuietRows

/-!
# Small-offender assembly from all concrete source rows

The orthogonal and Suzuki markings now provide their full local bounds and
crossed centralization. The two natural markings also supply crossed
centralization directly. Together with the existing natural-plus-dual and
four-copy exclusions, the consumer yields the original natural survivor and
w≥2 on the unchanged full module.

This is conditional assembly. The quiet selector must still construct the
listed markings, including crossed centralization in the four-copy row;
that work remains with qt-d-10-nona5-small-offender. HalfSylowUniqueAt retains
its producer qt-d-10-nona5-half-sylow-unique and ultimate discharge by
qt-d-10-nona5-point-control. No unconditional source theorem is claimed.

Source: Aschbacher--Smith 10.1.1--2 and 10.2.10--12, pp.741--742,753--755.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SmallOffender.Recognition
open Chapter3.Section02 PointControl.Selection
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G}

theorem nonnormalSmallOffender_of_quiet_source_rows_and_halfSylow
    (hhalf : PointControl.HalfSylowUniqueAt T)
    (hquiet : ∀ (L : Subgroup G) (D : FundamentalSetup KnownSimple.IsKnownSimple T L) (g : G),
      Configuration T D g →
      Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G) →
      ∃ E : FundamentalSetup KnownSimple.IsKnownSimple T L,
        E.fullModule ≤ D.fullModule ∧
        (BinaryThreeNatural E ∨ RankOneNatural E ∨ NaturalDualRow E ∨
          (FourNaturalRow E ∧ ∀ t ∈ (T : Subgroup G), t ∉ normalizer (L : Set G) →
            (⁅E.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G)) ∨
          OrthogonalFourMinusRow E ∨ SuzukiNaturalRow E)) :
    SourceNonnormalSmallOffenderAt T := by
  apply nonnormalSmallOffender_of_quiet_models_and_halfSylow hhalf
  intro L D g c hJ
  obtain ⟨E,hE,hrow⟩ := hquiet L D g c hJ
  obtain ⟨he,cE⟩ := c.reselect E hE
  have hNL : normalizer (L : Set G) ≤ E.maximalLocal :=
    PointControl.component_normalizer_le_of_halfSylowUnique E cE.nonnormal
      (hhalf cE.many L E cE.nonnormal cE.notA5)
  rcases hrow with hnatural | hrank | hdual | ⟨hfour,hcross⟩ | horth | hsuzuki
  · obtain ⟨e,⟨mark⟩⟩ := hnatural
    exact ⟨E,hE,Or.inl ⟨⟨ModuleChoice.full_eq_local_of_binaryThreeNatural E cE.nonnormal
      ⟨e,⟨mark⟩⟩,e,mark,fun _ ht htn => binary_three_crossed_of_marking E ⟨e,⟨mark⟩⟩ ht htn⟩⟩⟩
  · exact (no_rank_one_natural_of_small_offender E cE hrank
      (fun _ ht htn => rank_one_crossed_of_marking E hrank ht htn) hNL).elim
  · exact (no_natural_dual_of_small_offender E cE hdual hNL).elim
  · exact (no_four_natural_of_small_offender E cE hfour hcross hNL).elim
  · exact (no_orthogonal_of_small_offender E cE horth hNL).elim
  · exact (no_suzuki_natural_of_small_offender E cE hsuzuki hNL).elim

end CFSG.Quasithin.Chapter10.SmallOffender.Recognition
