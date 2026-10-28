module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalRecognitionCatalogue
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalRecognitionRee
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalRecognitionExceptional

/-!
# The whole-residual deduction in the original Chapter12 pair

The source diagram selector constructs a single perfect factor with binary
PSL₂ quotient, nonshortness and the two original core layers. The complete
model comparison excludes every candidate amalgam for that factor. Combining
this with the already proved exchanged-component exclusion identifies the
selected right factor with the entire O²(H). No binary PSL₂ restriction is
imposed on that whole residual, so the special U₅(4) row remains available.

The exhaustive comparison and F.1.12 core bound are explicit source inputs,
not conclusions of this module. Their proofs and ambient completion remain
with qt-d-1222-rankone-generic-global. Original uniqueness retains its independent
producer, and final discharge stays with qt-d-1222-rankone-generic and
qt-d-1361-source. No faithful local triple is treated as global recognition.

Source: Aschbacher–Smith 5.2.6, printed pp.650–651, and its original
Chapter12 application on p.795 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- The complete diagram comparison eliminates that source row, without
using the separate two-core index bound needed for exchanged components. -/
theorem rankOne_global_no_diagram_of_comparisons
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hpar : 1 < ChapterE.generationParameter H)
    (hthree : ¬ ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (hN : localBorel T L ≤ normalizer (residual H : Set G))
    (hunique : ∀ X : Subgroup G, IsMaximalTwoLocal X → L ≤ X →
      X = normalizer (L : Set G))
    (hcomparison : ∀ A B R : Subgroup G, Global.Preparation T L H A B R →
      Group.IsPerfect R → Global.ConcreteAmalgamComparison
        (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H))) :
    ¬ Global.RightDiagramSource T L H := by
  intro hd
  obtain ⟨A,B,R,f,d,hp,_,hlin,hnot,hl,_⟩ :=
    D.rankOne_global_preparation_layers_of_diagram
      h hmany hn hpsl hH hpar hthree hN hunique hd
  exact d.not_diagram_comparison (D.rankOne_generic_input_of_many h hmany hn hpsl)
    hH.1.1.2 hN hp hlin hnot hl (hcomparison A B R d hp)

/-- The local assembly in 5.2.6: the selected factor is the whole O²(H).
The genuine exhaustive comparison, core bound and original uniqueness remain
explicit inputs; all local selection and diagram exclusions are discharged. -/
theorem rankOne_global_residual_preparation_of_comparisons
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hpar : 1 < ChapterE.generationParameter H)
    (hthree : ¬ ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (hN : localBorel T L ≤ normalizer (residual H : Set G))
    (hunique : ∀ X : Subgroup G, IsMaximalTwoLocal X → L ≤ X →
      X = normalizer (L : Set G))
    (hcore : ∀ A B R : Subgroup G, Global.Preparation T L H A B R →
      Group.IsPerfect R →
      (R.pCoreIn 2).relIndex ((R ⊔ Global.sourceS L H).pCoreIn 2) ≤ 2)
    (hcomparison : ∀ A B R : Subgroup G, Global.Preparation T L H A B R →
      Group.IsPerfect R → Global.ConcreteAmalgamComparison
        (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H))) :
    ∃ A B : Subgroup G, Global.Preparation T L H A B (residual H) ∧
      Group.IsPerfect (residual H) := by
  rcases D.rankOne_global_residual_or_diagram_of_core_bound h hmany hn hpsl
    hH hpar hN hunique hcore with hr | hd
  · exact hr
  · exact (D.rankOne_global_no_diagram_of_comparisons h hmany hn hpsl
      hH hpar hthree hN hunique hcomparison hd).elim

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
