module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalRecognitionUnitaryPlane
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalRecognitionUnitary

/-!
# Both orientations of the unitary amalgams in the original diagram branch

The chosen diagram factor has the original two noncentral core layers.
The ordinary and degree-two point and plane comparisons therefore exclude
all four compatible unitary-four amalgam isomorphisms. The source amalgam
uses the full intersection of its literal parabolics. All earlier quotient,
Cartan and chief-layer data stay attached to the same selected factor.

The whole-residual branch remains, including its special U₅(4) row.
Original uniqueness and the F.1.12 core bound are explicit earlier inputs.
The G₂/triality comparisons and completion recognition remain with
qt-d-1222-rankone-generic-global; final original source discharge remains
with qt-d-1222-rankone-generic and qt-d-1361-source.

Source: Aschbacher–Smith, 5.2.6, printed pp.650–651, and the original
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

/-- Both orientations of both concrete unitary amalgams are excluded on
the same selected diagram factor and its original parabolic inclusion maps. -/
theorem rankOne_global_preparation_unitary_amalgam_exclusions_of_diagram
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
        let α := Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)
        ¬ Nonempty (RankTwoAmalgam.Iso α (amalgam m hm)) ∧
          ¬ Nonempty (RankTwoAmalgam.Iso α (amalgam m hm).reverse) ∧
          ¬ Nonempty (RankTwoAmalgam.Iso α (Extension.amalgam m hm)) ∧
          ¬ Nonempty (RankTwoAmalgam.Iso α (Extension.amalgam m hm).reverse)) := by
  obtain ⟨A,B,R,f,d,hp,hf,hlin,hnot,hlayers,hAN,hcount,hcountA,hSuz,hSU⟩ :=
    D.rankOne_global_preparation_layers_of_diagram h hmany hn hpsl hH hpar hthree hN hunique hd
  refine ⟨A,B,R,f,d,hp,hf,hlin,hnot,hlayers,hAN,hcount,hcountA,hSuz,hSU,?_⟩
  exact d.not_unitary_amalgams
    (D.rankOne_generic_input_of_many h hmany hn hpsl).sylow_normalizes hN hp hlayers

/-- The original source either selects the whole residual, or its selected
diagram factor excludes both orientations of the ordinary and extended U₄
amalgams. The whole-residual U₅(4) possibility is retained. -/
theorem rankOne_global_residual_or_diagram_unitary_amalgam_exclusions_of_core_bound
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
          let α := Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)
          ¬ Nonempty (RankTwoAmalgam.Iso α (amalgam m hm)) ∧
            ¬ Nonempty (RankTwoAmalgam.Iso α (amalgam m hm).reverse) ∧
            ¬ Nonempty (RankTwoAmalgam.Iso α (Extension.amalgam m hm)) ∧
            ¬ Nonempty (RankTwoAmalgam.Iso α (Extension.amalgam m hm).reverse))) := by
  rcases D.rankOne_global_residual_or_diagram_of_core_bound h hmany hn hpsl
    hH hpar hN hunique hcore with ⟨A,B,d,hp⟩ | hd
  · exact ⟨A,B,residual H,d,hp,Or.inl rfl⟩
  · obtain ⟨A,B,R,f,d,hp,hf,hlin,hnot,hlayers,hAN,hcount,hcountA,hSuz,hSU,hU⟩ :=
      D.rankOne_global_preparation_unitary_amalgam_exclusions_of_diagram
        h hmany hn hpsl hH hpar hthree hN hunique hd
    exact ⟨A,B,R,d,hp,Or.inr ⟨⟨f,hf,hlin⟩,hnot,hlayers,hAN,hcount,hcountA,hSuz,hSU,hU⟩⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
