module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Quintic.ModuleGeometry.ResidualSigned
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Quintic.SourceComponent.SmallSieve

/-!
# The reduced component catalogue in the original residual branch

The proved signed Sylow normalizer index constructs the original residual
geometry. Extract the escaping component and its actual C.2.7 input, then
apply the full B.5.1 theorem and the small-row exclusions. Every quotient,
radical and first-factor action is the original one. No module, normalizer,
normalization or model-selection callback remains in this residual reduction.

The remaining classical and marked outer models, exchanged module geometry
and final p=3 assembly remain with qt-e-14615-quintic-exclusion. The earlier
14.6.12--14 inputs retain final discharge with qt-e-suitable-odd-normalizer.
The original ExchangedFactorSetup.index is used; no no-index proof is asserted.
Source: Aschbacher--Smith 14.6.15, printed pp.1034--1035.
-/
public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06.OddNormalizer.Quintic.ModuleGeometry
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open ComponentExclusion ChapterC.C27Source
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G]
private def HasRemainingComponent (Mc Kz K1 K2 R : Subgroup G) : Prop :=
    ∃ j : SourceEscapingComponent Mc Kz
        K1 K2 R,
      Input KnownSimple.IsKnownSimple (normalizer (K2 : Set G))
        R (Mc ⊓ normalizer (K2 : Set G)) j.J ∧
      ∃ (_hCJ : starImage j.J R j.J ≤
          offenderSubgroup (starRepresentation j.J R))
        (c : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
          ((starRepresentation j.J R).comp
            (offenderSubgroup (starRepresentation j.J R)).subtype)
          ((starImage j.J R j.J).subgroupOf
            (offenderSubgroup (starRepresentation j.J R)))),
        RemainingQuinticRow c.sectionData.action
          ((starImage j.J R j.J).subgroupOf
            (offenderSubgroup (starRepresentation j.J R)))

variable {T : Sylow 2 G} {M Mc H H0 H1 H2 : Subgroup G}
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H)]
    {a : LocalQuotientAction H (conjugateSpanBy (localModule T M) H) (centralInvolutions T)}
    (s : Context T M Mc H H0 H1 H2 a)
local instance : IsElementaryAbelian 2
    (ChapterF.Section09.Setup.UH
      ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,H⟩) :=
  inferInstanceAs (IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H))

include s in
/-- Construct the literal residual component and reduced moved-section
catalogue from the original source context and K_z=K alone. -/
theorem source_residual_component_remaining_moved_rows
    (hc : residualClosure H Mc = residual H) :
    ∃ j : SourceEscapingComponent Mc (residualClosure H Mc)
        (residual H1) (residual H2) (Mc.pCoreIn 2),
      Input KnownSimple.IsKnownSimple (normalizer (residual H2 : Set G))
        (Mc.pCoreIn 2) (Mc ⊓ normalizer (residual H2 : Set G)) j.J ∧
      ∃ (_hCJ : starImage j.J (Mc.pCoreIn 2) j.J ≤
          offenderSubgroup (starRepresentation j.J (Mc.pCoreIn 2)))
        (c : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
          ((starRepresentation j.J (Mc.pCoreIn 2)).comp
            (offenderSubgroup (starRepresentation j.J (Mc.pCoreIn 2))).subtype)
          ((starImage j.J (Mc.pCoreIn 2) j.J).subgroupOf
            (offenderSubgroup (starRepresentation j.J (Mc.pCoreIn 2))))),
        RemainingQuinticRow c.sectionData.action
          ((starImage j.J (Mc.pCoreIn 2) j.J).subgroupOf
            (offenderSubgroup (starRepresentation j.J (Mc.pCoreIn 2)))) := by
  let d := indexedResidualNormalizerGeometry s hc (source_residual_normalizer_index s hc)
  have he := indexedResidualNormalizerGeometry_factors s hc (source_residual_normalizer_index s hc)
  change d.K1 = residual H1 ∧ d.K2 = residual H2 at he
  change HasRemainingComponent Mc (residualClosure H Mc)
    (residual H1) (residual H2) (Mc.pCoreIn 2)
  rw [←he.1,←he.2]
  let j := Classical.choice (exists_source_escaping_component s d)
  have hi := source_component_input s d j
  have hr := source_component_remaining_moved_rows s d j
  exact ⟨j,hi,hr⟩
end CFSG.Quasithin.Chapter14.Section06.OddNormalizer.Quintic.ModuleGeometry
