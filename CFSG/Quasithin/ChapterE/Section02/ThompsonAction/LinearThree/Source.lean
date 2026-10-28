module

public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.LinearThree.Source
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.Basic
public import CFSG.Quasithin.ChapterB.Section06To07.OffenderGeneration
public import CFSG.Quasithin.ChapterB.Section02.OffenderFactorization

/-!
# The original local B.5.1 input in the E.2.3 SL3 exclusion

The original Thompson movement gives an FF action on the literal centralizer
quotient. Its actual offender subgroup contains the two-residual. If the
local action on that offender subgroup satisfies the original reducible
SL3 B.5.1 hypotheses, the proved reconstruction supplies coordinates on the
same moved space with its full ambient action. The two-parabolic obstruction
then excludes this branch.

No module chart or ambient flag preservation is assumed. The full earlier
B.4.2, semisimplicity and A.3.6 implications are retained explicitly, as is the
original local B.5.1 hypothesis awaiting component preparation.

Source: Aschbacher–Smith B.6.9 and E.2.3, printed pp.116 and 216–217
(1 March 2004 manuscript).
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.ChapterE.ThompsonAction
open ChapterB.QuasisimpleSource
universe u
variable {G H : Type u} [Group G] [Finite G] [Group H] [Finite H]

/-- Original E.2.3 quotient application; no assumed natural moved-space chart. -/
theorem not_reducible_three_offender_source
    {K : GroupClass.{u}} (hK : IrreducibleBranch.ContainsSimpleTwoGroups K)
    (hsemisimple : ChapterB.SourceInduction.HighThreeRank.CoverCentralizer.SourceConstruction.SemisimpleInput K)
    (h36 : Chapter1.Section02.A36Input K)
    (earlier : ChapterB.SourceInduction.ProjectiveLine.IrreducibleClassificationInput.{u,u} K)
    (T : Sylow 2 G) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U]
    (q : G →* H) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (U : Set G)) (hcore : pCore 2 H = ⊥)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G)) :
    let ρ := NormalElementaryQuotient.representation U q hq hker
    let Y := offenderSubgroup ρ
    QuasisimpleSourceHypothesis (ρ.comp Y.subtype) K ((pResidual 2 H).subgroupOf Y) →
    ¬ IsIrrPlus (ρ.comp Y.subtype) ((pResidual 2 H).subgroupOf Y)
      (moved (ρ.comp Y.subtype) ((pResidual 2 H).subgroupOf Y)) →
    ∀ (F : BinaryField), (pResidual 2 H ≃* SL(3,F.Carrier)) → False := by
  dsimp only
  intro hs hn F mark
  let ρ := NormalElementaryQuotient.representation U q hq hker
  have hne : q.ker ≠ ⊤ := by
    intro he
    apply hJ
    rw [← hker, he]
    exact le_top
  have hp := (ChapterB.minimalParabolic_reduced_image T hP q hq hcore hne).2
  have hff : IsFFModule ρ := by
    obtain hf | ⟨_,hff,_,_,_⟩ := ChapterB.lemma_B_2_7 U q hq hker T
    · exact (hJ ((elementaryAbelianMaxJ_sylow_le_top T).trans hf.1)).elim
    · exact hff
  have hr := (ChapterB.offender_generation (T.mapSurjective hq) hp ρ hff hcore).1
  exact ChapterB.not_minimalParabolic_of_reducible_three_source_restriction ρ
    hK hsemisimple h36 earlier (T.mapSurjective hq) (pResidual 2 H) (offenderSubgroup ρ)
    hr (pResidual_sup_sylow_eq_top (T.mapSurjective hq)) hs hn F mark hp

/-- The same application on the actual centralizer quotient of the original reduced module. -/
theorem source_not_reducible_three_offender
    {K : GroupClass.{u}} (hK : IrreducibleBranch.ContainsSimpleTwoGroups K)
    (hsemisimple : ChapterB.SourceInduction.HighThreeRank.CoverCentralizer.SourceConstruction.SemisimpleInput K)
    (h36 : Chapter1.Section02.A36Input K)
    (earlier : ChapterB.SourceInduction.ProjectiveLine.IrreducibleClassificationInput.{u,u} K)
    (T : Sylow 2 G) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (U : Subgroup G) (hU : IsPReduced 2 U)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G)) :
    letI := hU.normal
    letI := hU.elementary
    let C := centralizer (U : Set G)
    let q := QuotientGroup.mk' C
    let ρ := NormalElementaryQuotient.representation U q
      (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
    let Y := offenderSubgroup ρ
    QuasisimpleSourceHypothesis (ρ.comp Y.subtype) K
      ((pResidual 2 (G ⧸ C)).subgroupOf Y) →
    ¬ IsIrrPlus (ρ.comp Y.subtype) ((pResidual 2 (G ⧸ C)).subgroupOf Y)
      (moved (ρ.comp Y.subtype) ((pResidual 2 (G ⧸ C)).subgroupOf Y)) →
    ∀ (F : BinaryField), (pResidual 2 (G ⧸ C) ≃* SL(3,F.Carrier)) → False := by
  let := hU.normal
  let := hU.elementary
  exact not_reducible_three_offender_source hK hsemisimple h36 earlier T hP U
    _ (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
    hU.quotient_pCore_eq_bot hJ

end CFSG.Quasithin.ChapterE.ThompsonAction
