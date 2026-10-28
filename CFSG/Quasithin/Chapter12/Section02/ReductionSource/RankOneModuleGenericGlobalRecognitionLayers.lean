module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalRecognitionLayers
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalRecognitionQuotient

/-!
# The original chosen-module application of the two core layers

The same selected diagram factor R has at least two noncentral chief
factors in its intrinsic two-core. The intervening layer is precisely
R ∩ O₂(O²(H)), and the original left Cartan normalizes it. The count
remains at least two after adjoining that Cartan. The earlier
binary quotient and exclusions are retained on that same factor.

This supplies the local chief-layer argument of 5.2.6. Original uniqueness
and the F.1.12 core bound remain explicit; the whole-residual branch,
including the special U₅(4) row, remains available. The remaining model
comparisons and completion recognition stay with
qt-d-1222-rankone-generic-global, with final source consumers
qt-d-1222-rankone-generic and qt-d-1361-source.

Source: Aschbacher–Smith, printed pp.650–651 and 795
(`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- The source diagram supplies two noncentral two-core layers on the very
same prepared factor, with its binary quotient and four earlier obstructions. -/
theorem rankOne_global_preparation_layers_of_diagram
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
      ¬ ChapterF.Source.IsSU (R ⧸ pCore 2 R) 3 4 := by
  have hi := D.rankOne_generic_input_of_many h hmany hn hpsl
  obtain ⟨A,B,c⟩ := D.rankOne_exists_cartanPair h hn hpsl hH hpar
  obtain ⟨R,f,r,hp,hnot,hf,hlin,hlayers⟩ :=
    Global.diagram_source_rightFactor_two_layers hi hH hpar hthree c hN hd
  obtain ⟨hleft,hSylow⟩ := D.rankOne_sourceS_intersection_left h hpsl hH
  have d : Global.Preparation T L H A B R := by
    refine ⟨c,r.le_residual,r.outside,hunique,hleft,?_,r.quotient,
      r.S_normalizes,r.cartan_normalizes,r.borel,r.characteristic_two hi hH c hleft hN⟩
    intro i
    fin_cases i
    · exact hSylow
    · exact r.sylow
  let := hp
  exact ⟨A,B,R,f,d,hp,hf,hlin,hnot,hlayers,
    d.cartan_normalizes_residual_core_intersection hN,hlayers.two_le_noncentralCount,
    d.cartan_core_two_chief hN hp hlayers,
    fun _ hm => Global.binary_quotient_not_suzuki hlin hm,
    Global.binary_quotient_not_special_unitary hlin (m := 2) (by decide)⟩

/-- The original source reduces to the whole residual or a diagram factor
with two noncentral two-core layers. The F.1.12 bound and uniqueness remain
explicit; no amalgam or ambient recognition is assumed. -/
theorem rankOne_global_residual_or_diagram_layers_of_core_bound
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
        ¬ ChapterF.Source.IsSU (R ⧸ pCore 2 R) 3 4) := by
  rcases D.rankOne_global_residual_or_diagram_of_core_bound h hmany hn hpsl
    hH hpar hN hunique hcore with ⟨A,B,d,hp⟩ | hd
  · exact ⟨A,B,residual H,d,hp,Or.inl rfl⟩
  · obtain ⟨A,B,R,f,d,hp,hf,hlin,hnot,hlayers,hAN,hcount,hcountA,hSuz,hSU⟩ :=
      D.rankOne_global_preparation_layers_of_diagram
        h hmany hn hpsl hH hpar hthree hN hunique hd
    exact ⟨A,B,R,d,hp,Or.inr ⟨⟨f,hf,hlin⟩,hnot,hlayers,hAN,hcount,hcountA,hSuz,hSU⟩⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
