module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalRecognitionQuotient
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalRecognitionDiagram

/-!
# The diagram quotient exclusions in the original chosen-module setup

The same prepared perfect right factor is nonshort and has an actual
PSL₂(2ᶠ) quotient with f > 1. Thus its quotient is neither a positive
Suzuki model nor SU₃(4). With the exchanged-component core bound, this
leaves the whole residual or a diagram factor outside these four amalgam
rows. The special U₅(4) row remains available in the whole-residual branch.

Original uniqueness remains with qt-d-1222-rankone-global-uniqueness.
The F.1.12 core bound, G₂/triality/unitary-four exclusions and genuine
amalgam and completion recognition remain with this task,
qt-d-1222-rankone-generic-global. Its final consumers are
qt-d-1222-rankone-generic and qt-d-1361-source.

Source: Aschbacher–Smith 5.2.6, printed pp.650–651, and the original
Chapter 12 application, p.795 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- Retain the actual binary quotient and its independent degree when
preparing the source diagram factor; apply both concrete-model exclusions. -/
theorem rankOne_global_preparation_obstructions_of_diagram
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hpar : 1 < ChapterE.generationParameter H)
    (hthree : ¬ ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (hN : localBorel T L ≤ normalizer (residual H : Set G))
    (hunique : ∀ X : Subgroup G, IsMaximalTwoLocal X → L ≤ X →
      X = normalizer (L : Set G))
    (hd : Global.RightDiagramSource T L H) :
    ∃ (A B R : Subgroup G) (f : ℕ), Global.Preparation T L H A B R ∧
      Group.IsPerfect R ∧ 1 < f ∧ ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 (2 ^ f) ∧
      ¬ ChapterC.IsShort R ∧
      (∀ m : ℕ, 0 < m → ¬ Nonempty ((R ⧸ pCore 2 R) ≃* SuzukiMatrixGroup m)) ∧
      ¬ ChapterF.Source.IsSU (R ⧸ pCore 2 R) 3 4 := by
  have hi := D.rankOne_generic_input_of_many h hmany hn hpsl
  obtain ⟨A,B,c⟩ := D.rankOne_exists_cartanPair h hn hpsl hH hpar
  obtain ⟨R,f,r,hp,hf,hlin,hnot,hSuz,hSU⟩ :=
    Global.diagram_source_rightFactor_obstructions hi hH hpar hthree c hN hd
  obtain ⟨hleft,hSylow⟩ := D.rankOne_sourceS_intersection_left h hpsl hH
  refine ⟨A,B,R,f,?_,hp,hf,hlin,hnot,hSuz,hSU⟩
  refine ⟨c,r.le_residual,r.outside,hunique,hleft,?_,r.quotient,
    r.S_normalizes,r.cartan_normalizes,r.borel,r.characteristic_two hi hH c hleft hN⟩
  intro i
  fin_cases i
  · exact hSylow
  · exact r.sylow

/-- After the exchanged-component bound, the prepared pair has either
the whole residual as right factor or the four proved diagram obstructions.
No conclusion about the remaining three diagram rows is assumed. -/
theorem rankOne_global_residual_or_diagram_obstructions_of_core_bound
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hpar : 1 < ChapterE.generationParameter H)
    (hthree : ¬ ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (hN : localBorel T L ≤ normalizer (residual H : Set G))
    (hunique : ∀ X : Subgroup G, IsMaximalTwoLocal X → L ≤ X →
      X = normalizer (L : Set G))
    (hcore : ∀ A B R : Subgroup G, Global.Preparation T L H A B R →
      Group.IsPerfect R →
      (R.pCoreIn 2).relIndex ((R ⊔ Global.sourceS L H).pCoreIn 2) ≤ 2) :
    ∃ A B R : Subgroup G, Global.Preparation T L H A B R ∧ Group.IsPerfect R ∧
      (R = residual H ∨
        (∃ f : ℕ, 1 < f ∧ ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 (2 ^ f)) ∧
        ¬ ChapterC.IsShort R ∧
        (∀ m : ℕ, 0 < m → ¬ Nonempty ((R ⧸ pCore 2 R) ≃* SuzukiMatrixGroup m)) ∧
        ¬ ChapterF.Source.IsSU (R ⧸ pCore 2 R) 3 4) := by
  rcases D.rankOne_global_residual_or_diagram_of_core_bound h hmany hn hpsl
    hH hpar hN hunique hcore with ⟨A,B,d,hp⟩ | hd
  · exact ⟨A,B,residual H,d,hp,Or.inl rfl⟩
  · obtain ⟨A,B,R,f,d,hp,hf,hlin,hnot,hSuz,hSU⟩ :=
      D.rankOne_global_preparation_obstructions_of_diagram
        h hmany hn hpsl hH hpar hthree hN hunique hd
    exact ⟨A,B,R,d,hp,Or.inr ⟨⟨f,hf,hlin⟩,hnot,hSuz,hSU⟩⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
