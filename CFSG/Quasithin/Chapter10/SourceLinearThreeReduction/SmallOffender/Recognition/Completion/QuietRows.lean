module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.SmallOffender.Recognition.ModelBounds.FourNatural
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.SmallOffender.Recognition.Completion.NaturalDual

/-!
# Small-offender assembly from concrete quiet-row markings

A contained natural three-space supplies full/local equality and the literal
natural geometry. The actual A₅ isomorphism excludes field four in the rank-one
row; the larger fields, natural-plus-dual, and four equal natural copies are
excluded by their full local bounds and uniform fixed-space geometry. The
terminal TI argument then supplies w≥2 on the unchanged full module.

The quiet selector must still produce these markings or the remaining large
rows, together with the source crossed-centralization clause. That work remains
with qt-d-10-nona5-small-offender. HalfSylowUniqueAt retains producer
qt-d-10-nona5-half-sylow-unique and ultimate discharge by
qt-d-10-nona5-point-control. This is a conditional consumer, not a proof of the
unconditional source theorem.

Source: Aschbacher--Smith 10.1.1--2 and 10.2.10--12, pp.741--742,753--755.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SmallOffender.Recognition
open Chapter3.Section02 PointControl.Selection
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G}

theorem nonnormalSmallOffender_of_quiet_markings_and_halfSylow
    (hhalf : PointControl.HalfSylowUniqueAt T)
    (hquiet : ∀ (L : Subgroup G) (D : FundamentalSetup KnownSimple.IsKnownSimple T L) (g : G),
      Configuration T D g →
      Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G) →
      ∃ E : FundamentalSetup KnownSimple.IsKnownSimple T L,
        E.fullModule ≤ D.fullModule ∧
        (∀ t ∈ (T : Subgroup G), t ∉ normalizer (L : Set G) →
          (⁅E.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G)) ∧
        (BinaryThreeNatural E ∨ RankOneNatural E ∨ NaturalDualRow E ∨
          FourNaturalRow E ∨ Nonempty (LargeModuleBounds E))) :
    SourceNonnormalSmallOffenderAt T := by
  apply nonnormalSmallOffender_of_quiet_models_and_halfSylow hhalf
  intro L D g c hJ
  obtain ⟨E,hE,hcross,hrow⟩ := hquiet L D g c hJ
  obtain ⟨he,cE⟩ := c.reselect E hE
  have hNL : normalizer (L : Set G) ≤ E.maximalLocal :=
    PointControl.component_normalizer_le_of_halfSylowUnique E cE.nonnormal
      (hhalf cE.many L E cE.nonnormal cE.notA5)
  rcases hrow with hnatural | hrank | hdual | hfour | hlarge
  · obtain ⟨e,⟨mark⟩⟩ := hnatural
    exact ⟨E,hE,Or.inl ⟨⟨ModuleChoice.full_eq_local_of_binaryThreeNatural E cE.nonnormal
      ⟨e,⟨mark⟩⟩,e,mark,hcross⟩⟩⟩
  · exact (no_rank_one_natural_of_small_offender E cE hrank hcross hNL).elim
  · exact (no_natural_dual_of_small_offender E cE hdual hNL).elim
  · exact (no_four_natural_of_small_offender E cE hfour hcross hNL).elim
  · exact ⟨E,hE,Or.inr hlarge⟩

end CFSG.Quasithin.Chapter10.SmallOffender.Recognition
