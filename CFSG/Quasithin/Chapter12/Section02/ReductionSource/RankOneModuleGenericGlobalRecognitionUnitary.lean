module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalRecognitionUnitaryExtension
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalRecognitionLayers

/-!
# The original diagram factor excludes both unitary-four point endpoints

Apply the concrete Frattini calculation to the same selected factor and
its exact residual-core intersection. The full source parabolic includes
S and the original Cartan. Both the ordinary unitary point parabolic and
its degree-two extension are impossible. All earlier quotient and chief
layer data are retained, and the whole-residual branch, including U₅(4),
remains available.

The exact uniqueness-over-L implication and F.1.12 core bound remain
explicit earlier inputs. Other diagram rows and genuine amalgam/completion
recognition remain with qt-d-1222-rankone-generic-global; final original
source discharge is retained by qt-d-1222-rankone-generic and
qt-d-1361-source.

Source: Aschbacher–Smith, 5.2.6, printed pp.650–651 and the original
chosen-module application on p.795 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
open ChapterF.GreenBook.LieModels.UnitaryFour
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- The selected diagram factor excludes both actual unitary point endpoints,
retaining its earlier quotient and two noncentral layers. -/
theorem rankOne_global_preparation_unitary_point_exclusions_of_diagram
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
      ¬ ChapterC.IsShort R ∧ Global.NoncentralCoreLayer (((residual H).pCoreIn 2).subgroupOf R) ∧
      A ≤ normalizer ((residual H).pCoreIn 2 ⊓ R : Set G) ∧
      (∀ s : NoncentralChiefRefinement.SeriesOn (pCore 2 R), 2 ≤ s.noncentralCount) ∧
      (∀ s : NoncentralChiefRefinement.SeriesOn (pCore 2 (R ⊔ A : Subgroup G)),
        2 ≤ s.noncentralCount) ∧
      (∀ m : ℕ, 0 < m → ¬ Nonempty ((R ⧸ pCore 2 R) ≃* SuzukiMatrixGroup m)) ∧
      ¬ ChapterF.Source.IsSU (R ⧸ pCore 2 R) 3 4 ∧
      (∀ (m : ℕ) (hm : 1 ≤ m),
        ¬ Nonempty ((ChapterF.Source.parabolic ![L,R] (Global.sourceS L H) 1) ≃*
          pointParabolic m hm) ∧
        ¬ Nonempty ((ChapterF.Source.parabolic ![L,R] (Global.sourceS L H) 1) ≃*
          Extension.point m hm)) := by
  obtain ⟨A,B,R,f,d,hp,hf,hlin,hnot,hlayers,hAN,hcount,hcountA,hSuz,hSU⟩ :=
    D.rankOne_global_preparation_layers_of_diagram h hmany hn hpsl hH hpar hthree hN hunique hd
  refine ⟨A,B,R,f,d,hp,hf,hlin,hnot,hlayers,hAN,hcount,hcountA,hSuz,hSU,?_⟩
  intro m hm
  have hTL := (D.rankOne_generic_input_of_many h hmany hn hpsl).sylow_normalizes
  exact ⟨d.not_unitary_point_source_parabolic hTL hN hp hlayers m hm,
    d.not_unitary_extended_point_source_parabolic hTL hN hp hlayers m hm⟩

/-- The original source reduces to the whole residual or a diagram factor
with both unitary point endpoints excluded. The exact earlier F.1.12 core
bound and uniqueness remain explicit. -/
theorem rankOne_global_residual_or_diagram_unitary_point_exclusions_of_core_bound
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
        ¬ ChapterC.IsShort R ∧ Global.NoncentralCoreLayer (((residual H).pCoreIn 2).subgroupOf R) ∧
        A ≤ normalizer ((residual H).pCoreIn 2 ⊓ R : Set G) ∧
        (∀ s : NoncentralChiefRefinement.SeriesOn (pCore 2 R), 2 ≤ s.noncentralCount) ∧
        (∀ s : NoncentralChiefRefinement.SeriesOn (pCore 2 (R ⊔ A : Subgroup G)),
          2 ≤ s.noncentralCount) ∧
        (∀ m : ℕ, 0 < m → ¬ Nonempty ((R ⧸ pCore 2 R) ≃* SuzukiMatrixGroup m)) ∧
        ¬ ChapterF.Source.IsSU (R ⧸ pCore 2 R) 3 4 ∧
        (∀ (m : ℕ) (hm : 1 ≤ m),
          ¬ Nonempty ((ChapterF.Source.parabolic ![L,R] (Global.sourceS L H) 1) ≃*
            pointParabolic m hm) ∧
          ¬ Nonempty ((ChapterF.Source.parabolic ![L,R] (Global.sourceS L H) 1) ≃*
            Extension.point m hm))) := by
  rcases D.rankOne_global_residual_or_diagram_of_core_bound h hmany hn hpsl
    hH hpar hN hunique hcore with ⟨A,B,d,hp⟩ | hd
  · exact ⟨A,B,residual H,d,hp,Or.inl rfl⟩
  · obtain ⟨A,B,R,f,d,hp,hf,hlin,hnot,hlayers,hAN,hcount,hcountA,hSuz,hSU,hU⟩ :=
      D.rankOne_global_preparation_unitary_point_exclusions_of_diagram
        h hmany hn hpsl hH hpar hthree hN hunique hd
    exact ⟨A,B,R,d,hp,Or.inr ⟨⟨f,hf,hlin⟩,hnot,hlayers,hAN,hcount,hcountA,hSuz,hSU,hU⟩⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
