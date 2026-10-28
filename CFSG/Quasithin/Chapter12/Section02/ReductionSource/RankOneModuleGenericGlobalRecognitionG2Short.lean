module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalRecognitionG2Short
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalRecognitionUnitaryPlane

/-!
# Both G₂ orientations in the original diagram branch

The full short G₂ parabolic has the residual-core dichotomy proved by
root coordinates and the Frattini argument. The actual selected diagram
factor, with its two original noncentral layers, cannot be that endpoint.
The other orientation contradicts the original faithful left factor's
noncentral core-center action. Both compatible G₂ orientations are excluded
at every positive binary exponent, including the binary field.
All four earlier unitary exclusions and the exact Cartan/core data are
retained on the same factor and the whole overlap.

The whole-residual branch, including U₅(4), remains available. Triality,
amalgam recognition and ambient completion remain
with qt-d-1222-rankone-generic-global. Original uniqueness and the F.1.12
core bound remain explicit, with final original source discharge retained
by qt-d-1222-rankone-generic and qt-d-1361-source.

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

/-- The same selected factor excludes both G₂ orientations, while retaining
all four unitary exclusions and the original two-core intersection. -/
theorem rankOne_global_preparation_g2_exclusions_of_diagram
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
          ¬ Nonempty (RankTwoAmalgam.Iso α (Extension.amalgam m hm).reverse)) ∧
      (∀ m : ℕ, 0 < m →
        let α := Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)
        ¬ Nonempty (RankTwoAmalgam.Iso α
          (ChapterF.GreenBook.LieModels.G2.amalgam (F := GaloisField 2 m))) ∧
          ¬ Nonempty (RankTwoAmalgam.Iso α
            (ChapterF.GreenBook.LieModels.G2.amalgam (F := GaloisField 2 m)).reverse)) := by
  obtain ⟨A,B,R,f,d,hp,hf,hlin,hnot,hlayers,hAN,hcount,hcountA,hSuz,hSU,hU⟩ :=
    D.rankOne_global_preparation_unitary_amalgam_exclusions_of_diagram
      h hmany hn hpsl hH hpar hthree hN hunique hd
  refine ⟨A,B,R,f,d,hp,hf,hlin,hnot,hlayers,hAN,hcount,hcountA,hSuz,hSU,hU,?_⟩
  intro m _hm
  exact d.not_g2_amalgams
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH.1.1.2 hN hp hlayers

/-- The source selects the whole residual, or a diagram factor excluding
both G₂ orientations and all four unitary comparisons. The whole-residual
U₅(4) row remains, as do the genuine earlier core-bound and uniqueness inputs. -/
theorem rankOne_global_residual_or_diagram_g2_exclusions_of_core_bound
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
            ¬ Nonempty (RankTwoAmalgam.Iso α (Extension.amalgam m hm).reverse)) ∧
        (∀ m : ℕ, 0 < m →
          let α := Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)
          ¬ Nonempty (RankTwoAmalgam.Iso α
            (ChapterF.GreenBook.LieModels.G2.amalgam (F := GaloisField 2 m))) ∧
            ¬ Nonempty (RankTwoAmalgam.Iso α
              (ChapterF.GreenBook.LieModels.G2.amalgam (F := GaloisField 2 m)).reverse))) := by
  rcases D.rankOne_global_residual_or_diagram_of_core_bound h hmany hn hpsl
    hH hpar hN hunique hcore with ⟨A,B,d,hp⟩ | hd
  · exact ⟨A,B,residual H,d,hp,Or.inl rfl⟩
  · obtain ⟨A,B,R,f,d,hp,hf,hlin,hnot,hlayers,hAN,hcount,hcountA,hSuz,hSU,hU,hG2⟩ :=
      D.rankOne_global_preparation_g2_exclusions_of_diagram
        h hmany hn hpsl hH hpar hthree hN hunique hd
    exact ⟨A,B,R,d,hp,Or.inr ⟨⟨f,hf,hlin⟩,hnot,hlayers,hAN,hcount,hcountA,hSuz,hSU,hU,hG2⟩⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
