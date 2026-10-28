module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalLocalRightComplete
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalRecognitionPreparation
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalLocal
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobal

/-!
# Complete right-factor selection in the original Chapter 12 setup

All Bender and diagram rows now supply the full normalized right factor,
including the nonprojective field-four linear row. The literal preparation
constructor retains its perfect factor, so the same pair has the genuine
F.1.1 hypotheses, right-Borel action on S, and the two nonsolvable parabolics
with exactly the original factors as solvable residuals.

The independent original uniqueness-over-L implication remains explicit;
its producer is qt-d-1222-rankone-global-uniqueness. The last theorem removes
the local-preparation callback from the existing global assembly. Genuine
Green Book amalgam identification and ambient completion recognition,
including the strict field bound and exceptional rows, remain with this
owner qt-d-1222-rankone-generic-global. The final consumers are
qt-d-1222-rankone-generic and qt-d-1361-source.

Source: Aschbacher–Smith, 5.2.4–6, printed pp.649–651;
the original Chapter 12 application is on p.795 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- The complete right factor in the original chosen-module setup. -/
theorem rankOne_source_rightFactor
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hpar : 1 < ChapterE.generationParameter H)
    (hthree : ¬ ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    {A B : Subgroup G} (c : CartanPair T L H A B)
    (hN : localBorel T L ≤ normalizer (residual H : Set G)) :
    ∃ R : Subgroup G, Global.RightFactor T L H A B R :=
  Global.source_rightFactor (D.rankOne_generic_input_of_many h hmany hn hpsl)
    hH hpar hthree c hN

/-- Construct the normalized pair with its perfect right factor, retaining
only the independent original uniqueness implication. -/
theorem rankOne_global_preparation_perfect_of_uniqueness
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hpar : 1 < ChapterE.generationParameter H)
    (hthree : ¬ ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (hN : localBorel T L ≤ normalizer (residual H : Set G))
    (hunique : ∀ X : Subgroup G, IsMaximalTwoLocal X → L ≤ X →
      X = normalizer (L : Set G)) :
    ∃ A B R : Subgroup G, Global.Preparation T L H A B R ∧ Group.IsPerfect R := by
  have hi := D.rankOne_generic_input_of_many h hmany hn hpsl
  obtain ⟨A,B,c⟩ := D.rankOne_exists_cartanPair h hn hpsl hH hpar
  obtain ⟨R,r,hR⟩ := Global.source_rightFactor_perfect hi hH hpar hthree c hN
  obtain ⟨hleft,hSylow⟩ := D.rankOne_sourceS_intersection_left h hpsl hH
  refine ⟨A,B,R,?_,hR⟩
  refine ⟨c,r.le_residual,r.outside,hunique,hleft,?_,r.quotient,
    r.S_normalizes,r.cartan_normalizes,r.borel,r.characteristic_two hi hH c hleft hN⟩
  intro i
  fin_cases i
  · exact hSylow
  · exact r.sylow

/-- Discharge every local-preparation selection premise under the original
uniqueness-over-L implication. -/
theorem rankOne_global_preparation_of_uniqueness
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hpar : 1 < ChapterE.generationParameter H)
    (hthree : ¬ ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (hN : localBorel T L ≤ normalizer (residual H : Set G))
    (hunique : ∀ X : Subgroup G, IsMaximalTwoLocal X → L ≤ X →
      X = normalizer (L : Set G)) :
    ∃ A B R : Subgroup G, Global.Preparation T L H A B R := by
  obtain ⟨A,B,R,d,_⟩ := D.rankOne_global_preparation_perfect_of_uniqueness
    h hmany hn hpsl hH hpar hthree hN hunique
  exact ⟨A,B,R,d⟩

/-- The actual constructed pair satisfies the source prerequisites for
F.1.12, and both parabolics are nonsolvable with the prescribed residuals. -/
theorem rankOne_global_local_source_of_uniqueness
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hpar : 1 < ChapterE.generationParameter H)
    (hthree : ¬ ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (hN : localBorel T L ≤ normalizer (residual H : Set G))
    (hunique : ∀ X : Subgroup G, IsMaximalTwoLocal X → L ≤ X →
      X = normalizer (L : Set G)) :
    ∃ A B R : Subgroup G, Global.Preparation T L H A B R ∧
      ChapterF.Source.HypothesisF11 ![L,R] (Global.sourceS L H) ∧
      ChapterF.Source.borel R (Global.sourceS L H) ≤ normalizer (Global.sourceS L H : Set G) ∧
      (∀ i : Fin 2, (solvableResidual (ChapterF.Source.parabolic ![L,R] (Global.sourceS L H) i)).map
        (ChapterF.Source.parabolic ![L,R] (Global.sourceS L H) i).subtype = ![L,R] i) ∧
      (∀ i : Fin 2, ¬ Group.IsSolvable (ChapterF.Source.parabolic ![L,R] (Global.sourceS L H) i)) := by
  obtain ⟨A,B,R,d,hR⟩ := D.rankOne_global_preparation_perfect_of_uniqueness
    h hmany hn hpsl hH hpar hthree hN hunique
  have hi := D.rankOne_generic_input_of_many h hmany hn hpsl
  exact ⟨A,B,R,d,d.hypothesisF11 hi hH.1.1.2,d.right_borel_normalizes_sourceS,
    d.parabolic_residuals hi hH.1.1.2 hR,d.parabolics_not_solvable hi hR⟩

/-- Apply the complete preparation to the original global assembly.
Uniqueness and genuine completion recognition still require their source proofs. -/
theorem rankOne_globalExit_of_uniqueness_and_recognition
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hpar : 1 < ChapterE.generationParameter H)
    (hthree : ¬ ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (hN : (normalizer (((T : Subgroup G).subgroupOf L) : Set L)).map L.subtype ≤
      normalizer (residual H : Set G))
    (hunique : ∀ X : Subgroup G, IsMaximalTwoLocal X → L ≤ X →
      X = normalizer (L : Set G))
    (hrecognize : Input KnownSimple.IsKnownSimple T L (RankOneModule.wholeReduced T L) n →
      H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) →
      1 < ChapterE.generationParameter H →
      ¬ ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4 →
      localBorel T L ≤ normalizer (residual H : Set G) →
      ∀ A B R : Subgroup G, Global.Preparation T L H A B R →
      ChapterF.Source.HypothesisF11 ![L,R] (Global.sourceS L H) →
      RankOneModule.GlobalExit G) : RankOneModule.GlobalExit G := by
  apply D.rankOne_globalExit_of_local_sources_of_many h hmany hn hpsl hH hpar hthree hN
    (hrecognize := hrecognize)
  intro _ hH' hpar' hthree' hN'
  exact D.rankOne_global_preparation_of_uniqueness h.toHypothesis1221 hmany hn hpsl
    hH' hpar' hthree' hN' hunique

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
