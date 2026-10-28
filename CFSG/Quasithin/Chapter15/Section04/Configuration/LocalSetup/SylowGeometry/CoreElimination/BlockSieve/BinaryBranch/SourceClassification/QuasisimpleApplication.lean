module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.BlockSieve.BinaryBranch.SourceClassification.Socle.Fitting
public import Theory.Quasithin.Rank

/-!
# Full quasisimple FF classification on the actual binary source module

The original SQTK hypothesis descends through its normal two-core quotient
and then to the actual offender group. Its generalized Fitting subgroup is
the literal simple binary socle, so all B.5.1 hypotheses hold on the original
module. The corrected universal source implication therefore supplies all
six module conclusions without assuming a local model or a small section.

This is a conditional application of the genuine earlier B.5.1 theorem.
Constructing that universal classifier, and comparing its remaining module
cases with the source Sylow obstruction, are separate mathematical steps.
Source: Aschbacher–Smith, B.5.1, pp.99–103; 15.4.20, printed p.1164.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve.BinaryBranch.SourceClassification
open TwoFactors.FFBranch TwoFactors.FFBranch.ClassificationComparison
universe u
variable {G : Type u} [Group G] [Finite G]
  {d : Source.Geometry G} {i j : Bool} {H U K : Subgroup G}

/-- The genuine SQTK source condition holds on the actual offender actor. -/
theorem sourceGroup_sqtk (h : Input d i j H U K)
    (hH : IsSQTK KnownSimple.IsKnownSimple H) :
    IsSQTK KnownSimple.IsKnownSimple (sourceGroup h) := by
  have hQ : IsSQTK KnownSimple.IsKnownSimple (H ⧸ pCore 2 H) := by
    refine ⟨?_, hH.isKGroup.quotient _⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans
      (hH.stronglyQuasithin p hp ho)
  exact hQ.subgroup _

/-- Every B.5.1 hypothesis is discharged at the literal generalized Fitting subgroup. -/
theorem sourceQuasisimpleHypothesis (h : Input d i j H U K) {n : ℕ}
    (hn : n = 4 ∨ n = 5)
    (e : (H ⧸ pCore 2 H) ≃* MulAut (Matrix.ProjectiveSpecialLinearGroup (Fin n) (ZMod 2)))
    (hH : IsSQTK KnownSimple.IsKnownSimple H) :
    let := h.module_properties.1
    FFAlternatives.QuasisimpleSourceHypothesis (sourceAction h) KnownSimple.IsKnownSimple
      (generalizedFitting (sourceGroup h)) := by
  let := h.module_properties.1
  have hyp := sourceFFHypothesis h hH
  refine ⟨hyp.finite_module, hyp.faithful, sourceFitting_isQuasisimple h hn e,
    (sourceGroup_sqtk h hH).subgroup _, ?_, hyp.twoCore, hyp.generated⟩
  apply (sup_eq_left.mpr ?_).symm
  exact (show center (sourceGroup h) ≤ fittingSubgroup (sourceGroup h) from
    le_sSup ⟨inferInstance, inferInstance⟩).trans (fitting_le_generalizedFitting _)

/-- Apply the corrected full universal B.5.1 implication with no local action assumptions. -/
theorem quasisimple_source_conclusion (h : Input d i j H U K) {n : ℕ}
    (hn : n = 4 ∨ n = 5)
    (e : (H ⧸ pCore 2 H) ≃* MulAut (Matrix.ProjectiveSpecialLinearGroup (Fin n) (ZMod 2)))
    (hH : IsSQTK KnownSimple.IsKnownSimple H)
    (earlier : FFAlternatives.ProjectiveLine.QuasisimpleClassificationInput.{u,u}
      KnownSimple.IsKnownSimple) :
    let := h.module_properties.1
    Nonempty (FFAlternatives.ProjectiveLine.QuasisimpleSourceConclusion (sourceAction h)
      (generalizedFitting (sourceGroup h))) := by
  let := h.module_properties.1
  exact earlier (sourceGroup h) (Additive (moduleClosure (d.Z.subgroupOf H)))
    (sourceAction h) (generalizedFitting (sourceGroup h))
    (sourceQuasisimpleHypothesis h hn e hH)

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve.BinaryBranch.SourceClassification
