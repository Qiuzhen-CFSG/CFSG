module
public import CFSG.Quasithin.Chapter12.Section04.SmallFusion.G2Source.CommutatorGeometry
public import CFSG.Quasithin.Chapter12.Section04.SmallFusion.G2Source.Parameters
public import CFSG.Quasithin.Chapter14.Section03.CaseOneSource.ConjugateInputAt

/-!
# The guarded fixed-space endgame for the binary G₂ Weyl row

The model-independent 12.4.1 conjugator normalizes the original chosen
module in both directions. The completed G₂ 12.4.9 commutator obstruction
rules this out. The numerical parameter input follows from the actual
hyperplane-centralizer bound and the full normalizer's involution geometry.

This source adapter retains the independently produced Sylow-normalizer
inclusion and hyperplane-centralizer theorem. It does not assert either
premise or fixed-space vanishing unconditionally.
Source: Aschbacher--Smith 12.4.1--2 and 12.4.8--9, printed pp.812--816.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion
open Chapter12.Section02
open Chapter12.Section04.SmallFusion
open Chapter12.Section04.SmallFusion.G2Source
open Chapter12.Section04.SLThreeCommutatorSource.ConjugateExistence
open Chapter14.Section03.CaseOneSource
open Chapter13.Section01
open ChapterB.QuasisimpleSource
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G}

 theorem g2_fixed_of_guarded_globalS
    (h13 : Hypothesis1311 T)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (exits : ∀ H : Subgroup G,
      H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) →
      Hypothesis1223 KnownSimple.IsKnownSimple T (localResidual H) →
      Nonempty ((localResidual H ⧸ pCore 2 (localResidual H)) ≃*
        alternatingGroup (Fin 5)) →
      RankOneModule.GenericExit T (localResidual H) ∧
        RankOneModule.SmallExit T (localResidual H))
    (e : ActionEquiv D.quotientAction
      (Atlas.G2.Natural.OrthogonalCover.action (ZMod 2)))
    (hNT : normalizer (T : Set G) ≤ normalizer (L : Set G))
    (hS : fixedSubgroup L V ≠ ⊥ →
      letI := D.elementary; 1 < ChapterE.globalS V) :
    fixedSubgroup L V = ⊥ := by
  let _ := D.elementary
  by_contra hne
  obtain ⟨z, hzOrder, hzGen, hM, hMV, hzOmega, hZ⟩ :=
    exists_fixed_involution_setup h D structural e hne
  obtain ⟨g, hcomm, hbound⟩ :=
    noncommutingConjugate_of_guarded_source_exits h13 h D structural modules hmany
      (by simpa [sylowCenterSeed] using hZ) exits (hS hne)
  have hA : V.map (MulAut.conj g).toMonoidHom ≤ normalizer (V : Set G) :=
    le_normalizer_iff_commutator_le_left.mpr (hbound.trans inf_le_left)
  have hVA : V ≤ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G) := by
    apply le_normalizer_iff_commutator_le_left.mpr
    rw [commutator_comm]
    exact hbound.trans inf_le_right
  exact lemma_12_4_9_of_g2_source h D structural e hne hNT g hA hcomm hVA


/-- The literal guarded G₂ fixed-space exclusion from its two remaining
source inputs. The numerical local minimum is proved internally. -/
theorem g2_fixed_of_guarded_hyperplanes
    (h13 : Hypothesis1311 T)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (exits : ∀ H : Subgroup G,
      H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) →
      Hypothesis1223 KnownSimple.IsKnownSimple T (localResidual H) →
      Nonempty ((localResidual H ⧸ pCore 2 (localResidual H)) ≃*
        alternatingGroup (Fin 5)) →
      RankOneModule.GenericExit T (localResidual H) ∧
        RankOneModule.SmallExit T (localResidual H))
    (e : ActionEquiv D.quotientAction
      (Atlas.G2.Natural.OrthogonalCover.action (ZMod 2)))
    (hNT : normalizer (T : Set G) ≤ normalizer (L : Set G))
    (hyp : fixedSubgroup L V ≠ ⊥ →
      ∀ U ≤ V, ChapterE.subgroupCorank V U = 1 →
        centralizer (U : Set G) ≤ normalizer (V : Set G)) :
    fixedSubgroup L V = ⊥ := by
  apply g2_fixed_of_guarded_globalS h13 h D structural modules hmany exits e hNT
  intro hne
  exact globalS_gt_one_of_hyperplanes h D structural e hne (hyp hne)

end CFSG.Quasithin.Chapter13.Section03.SourceCompletion
