module

public import CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.At.Parameters
public import CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.At.Module
public import CFSG.Quasithin.Chapter14.Section03.CaseOneSource.ConjugateInputAt
public import CFSG.Quasithin.Chapter14.Section03.CaseOneSource.FusionInput.At

/-!
# The guarded L₃ commutator, fusion and naturality application

The actual normalizer action and all three cases of 12.4.8 give globalS > 1.
The guarded 12.4.1 source theorem constructs a literal noncommuting conjugate.
B.4.8 symmetrizes its commutator plane, and 12.4.7 weak closure of the same
fixed involution gives the original contradiction. The marked projection is
then an equivalence on the whole original V, with its original quotient map.
The final application constructs the actual Chapter14 higher-rank hypothesis.

Only earlier Structural1222At, Theorem1222ModulesAt and the generic/small
rank-one source exits remain explicit. The exits retain qt-d-1241-l3-conjugate
and qt-d-1222-rankone-module as producers; qt-d-1332-source and qt-d-1434-source
own final discharge. This is a guarded source implication, not the universal
12.4.2 theorem or the final classification. The preserved universal interfaces
retain their original source obligations. The stronger LocalParameterSource
clause C_H(V_H) ≤ O₂(H) remains unresolved; the actual conjugator uses the proved
Sylow-centralizer bound C_T(V_H) = O₂(H), so that stronger clause is unnecessary
here.

Source: Aschbacher–Smith, 12.4.1, 12.4.8–9 and 12.4.2, pp.812,815–816;
13.3.2(3) and 14.3.4(3), pp.885,990.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section03.CaseOneSource
open Chapter12.Section02 Chapter12.Section04.SmallFusion ChapterE
open Chapter12.Section04.SLThreeCommutatorSource
open Chapter12.Section04.SLThreeCommutatorSource.ConjugateExistence
open Chapter13.Section01
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The original nontrivial symmetric plane; no local geometry premise remains. -/
theorem slThreeCommutator1242_of_source_at
    (h13 : Hypothesis1311 T)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (hmodel : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2)
    (exits : ∀ H : Subgroup G,
      H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) →
      Hypothesis1223 KnownSimple.IsKnownSimple T (localResidual H) →
      Nonempty ((localResidual H ⧸ pCore 2 (localResidual H)) ≃* alternatingGroup (Fin 5)) →
      RankOneModule.GenericExit T (localResidual H) ∧
        RankOneModule.SmallExit T (localResidual H))
    (hne : fixedSubgroup L V ≠ ⊥) :
    ∃ g : G,
      V.map (MulAut.conj g).toMonoidHom ≤ normalizer (V : Set G) ∧
      fixedSubgroup L V ≤ ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ ∧
      (⁅V, V.map (MulAut.conj g).toMonoidHom⁆).map (MulAut.conj g).toMonoidHom =
        ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ ∧
      ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥ := by
  let _ := D.elementary
  obtain ⟨E⟩ := SLThreeSource.At.extension_of_modules h D modules hmodel hne
  obtain ⟨z, _, _, _, _, _, hZ⟩ :=
    At.fixed_involution_setup_of_card_two h D structural (E.fixed_card_eq_two hne)
  have hs := At.globalS_gt_one_of_source h structural E hne
  obtain ⟨g, hg, hbound⟩ := noncommutingConjugate_of_guarded_source_exits
    h13 h D structural modules hmany hZ exits hs
  obtain ⟨k, _, hn, hf, hsym, hcomm, _⟩ :=
    At.symmetric_plane_of_source_conjugate h structural E hne g hg hbound
  exact ⟨k, hn, hf, hsym, hcomm⟩

/-- The same fixed-involution fusion contradiction on the same chosen V. -/
theorem slThreeFixedSpace1242_of_source_at
    (h13 : Hypothesis1311 T)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (hmodel : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2)
    (exits : ∀ H : Subgroup G,
      H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) →
      Hypothesis1223 KnownSimple.IsKnownSimple T (localResidual H) →
      Nonempty ((localResidual H ⧸ pCore 2 (localResidual H)) ≃* alternatingGroup (Fin 5)) →
      RankOneModule.GenericExit T (localResidual H) ∧
        RankOneModule.SmallExit T (localResidual H)) :
    fixedSubgroup L V = ⊥ :=
  slThreeFixedSpace1242_of_source_fusion_at h D hmany structural modules hmodel
    (slThreeCommutator1242_of_source_at h13 h D hmany structural modules hmodel exits)

/-- Natural coordinates on the whole original V, after the fusion contradiction. -/
theorem slThreeNaturalMarking_of_source_at
    (h13 : Hypothesis1311 T)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (hmodel : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2)
    (exits : ∀ H : Subgroup G,
      H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) →
      Hypothesis1223 KnownSimple.IsKnownSimple T (localResidual H) →
      Nonempty ((localResidual H ⧸ pCore 2 (localResidual H)) ≃* alternatingGroup (Fin 5)) →
      RankOneModule.GenericExit T (localResidual H) ∧
        RankOneModule.SmallExit T (localResidual H)) :
    letI := D.elementary
    Nonempty (AmbientNaturalMarking L D.normalizes 3) := by
  obtain ⟨E⟩ := At.extension_of_modules h D modules hmodel
  exact ⟨naturalMarking_of_fixed_eq_bot D E
    (slThreeFixedSpace1242_of_source_at h13 h D hmany structural modules hmodel exits)⟩

/-- The actual Counterexample supplies the ambient guard at the same G,T. -/
theorem slThreeNaturalMarking_of_counterexample_source_at
    (d : Counterexample T L) (hmax : FaithfulMaximalLocal T L)
    (D : ChosenModule T L V)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (hmodel : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2)
    (exits : ∀ H : Subgroup G,
      H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) →
      Hypothesis1223 KnownSimple.IsKnownSimple T (localResidual H) →
      Nonempty ((localResidual H ⧸ pCore 2 (localResidual H)) ≃* alternatingGroup (Fin 5)) →
      RankOneModule.GenericExit T (localResidual H) ∧
        RankOneModule.SmallExit T (localResidual H)) :
    letI := D.elementary
    Nonempty (AmbientNaturalMarking L D.normalizes 3) := by
  have h13 := FaithfulSource.Counterexample.hypothesis1311 d
  exact slThreeNaturalMarking_of_source_at h13
    (h13.hypothesis1223 hmax (quotient_quasisimple hmodel)) D hmany structural modules hmodel exits

/-- Literal 12.8.1/14.3 application, retaining only independent maximality
and the earlier structural, module and rank-one source implications. -/
def higherRankHypothesis_of_guarded_source_at
    (d : Counterexample T L) (hmax : FaithfulMaximalLocal T L)
    (D : ChosenModule T L V)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (hmodel : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2)
    (exits : ∀ H : Subgroup G,
      H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) →
      Hypothesis1223 KnownSimple.IsKnownSimple T (localResidual H) →
      Nonempty ((localResidual H ⧸ pCore 2 (localResidual H)) ≃* alternatingGroup (Fin 5)) →
      RankOneModule.GenericExit T (localResidual H) ∧
        RankOneModule.SmallExit T (localResidual H)) :
    HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3 := by
  letI := D.elementary
  let A := Classical.choice
    (slThreeNaturalMarking_of_counterexample_source_at d hmax D hmany structural modules hmodel exits)
  exact {
    source := (FaithfulSource.Counterexample.hypothesis1311 d).hypothesis1223 hmax
      (quotient_quasisimple hmodel)
    chosen := D
    rank := by decide
    quotient_model := hmodel
    natural := ⟨A.quotientEquiv, A.coordinates, A.equivariant⟩
    no_nextLinear := d.no_linear 4 (Or.inl rfl)
    no_A9 := d.no_alternating_nine
    no_M24 := d.no_sporadic .m24 (by simp) }

end CFSG.Quasithin.Chapter14.Section03.CaseOneSource
