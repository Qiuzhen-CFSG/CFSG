module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Quintic.ModuleGeometry.ResidualSigned
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Quintic.SourceComponent.SymplecticExclusion

/-!
# The linear-three and G₂ component remainder in the original residual branch

Apply the intrinsic symplectic parabolic contradiction to the same escaping
component supplied by the signed Sylow normalizer construction. Only the
linear-three and nonbinary G₂ models remain,
with their actual field degrees and all six original B.5.1 clauses.

The classical comparisons, exchanged module geometry, original index premise
and final p=3 assembly remain with qt-e-14615-quintic-exclusion. Earlier
14.6.12--14 discharge stays with qt-e-suitable-odd-normalizer.
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
private def HasLinearG2Component (Mc Kz K1 K2 R : Subgroup G) : Prop :=
    ∃ j : SourceEscapingComponent Mc Kz
        K1 K2 R,
      Input KnownSimple.IsKnownSimple (normalizer (K2 : Set G))
        R (Mc ⊓ normalizer (K2 : Set G)) j.J ∧
      ∃ (_hCJ : starImage j.J R j.J ≤
          offenderSubgroup (starRepresentation j.J R))
        (_c : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
          ((starRepresentation j.J R).comp
            (offenderSubgroup (starRepresentation j.J R)).subtype)
          ((starImage j.J R j.J).subgroupOf
            (offenderSubgroup (starRepresentation j.J R)))),
        LinearG2QuinticRow
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
/-- Construct the literal residual component and remaining classical
catalogue from the original source context and K_z=K alone. -/
theorem source_residual_component_linear_g2_moved_rows
    (hc : residualClosure H Mc = residual H) :
    ∃ j : SourceEscapingComponent Mc (residualClosure H Mc)
        (residual H1) (residual H2) (Mc.pCoreIn 2),
      Input KnownSimple.IsKnownSimple (normalizer (residual H2 : Set G))
        (Mc.pCoreIn 2) (Mc ⊓ normalizer (residual H2 : Set G)) j.J ∧
      ∃ (_hCJ : starImage j.J (Mc.pCoreIn 2) j.J ≤
          offenderSubgroup (starRepresentation j.J (Mc.pCoreIn 2)))
        (_c : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
          ((starRepresentation j.J (Mc.pCoreIn 2)).comp
            (offenderSubgroup (starRepresentation j.J (Mc.pCoreIn 2))).subtype)
          ((starImage j.J (Mc.pCoreIn 2) j.J).subgroupOf
            (offenderSubgroup (starRepresentation j.J (Mc.pCoreIn 2))))),
        LinearG2QuinticRow
          ((starImage j.J (Mc.pCoreIn 2) j.J).subgroupOf
            (offenderSubgroup (starRepresentation j.J (Mc.pCoreIn 2)))) := by
  let d := indexedResidualNormalizerGeometry s hc (source_residual_normalizer_index s hc)
  have he := indexedResidualNormalizerGeometry_factors s hc (source_residual_normalizer_index s hc)
  change d.K1 = residual H1 ∧ d.K2 = residual H2 at he
  change HasLinearG2Component Mc (residualClosure H Mc)
    (residual H1) (residual H2) (Mc.pCoreIn 2)
  rw [←he.1,←he.2]
  let j := Classical.choice (exists_source_escaping_component s d)
  have hi := source_component_input s d j
  have hr := source_component_linear_g2_moved_rows s d j
  exact ⟨j,hi,hr⟩
end CFSG.Quasithin.Chapter14.Section06.OddNormalizer.Quintic.ModuleGeometry
