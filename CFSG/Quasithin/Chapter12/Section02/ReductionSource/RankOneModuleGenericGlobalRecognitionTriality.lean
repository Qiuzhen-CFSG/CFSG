module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalRecognitionTriality
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalRecognitionG2Short

/-!
# Triality comparisons in the original generic branch

Both triality orientations are excluded for the selected diagram factor.
The arms factor centralizes its core center, contradicting the original
faithful left factor in one orientation. In the other orientation, the
literal right factor is the arms solvable residual. Its quotient PSL₂(q³)
forces every noncentral binary chief factor to have dimension at least
6n, while its two-core has order 2^(9n). This contradicts the two original
noncentral layers. The binary field is also excluded directly by solvability
of the central parabolic.

The same selected factor retains all earlier G₂ and unitary comparisons,
the original S = O₂(N_G(L) ∩ H), and the whole overlap with its odd Cartans.
The whole-residual branch, including U₅(4), remains. For an actual triality
amalgam in that branch, the final application identifies its field with the
original exponent and transports both local factors and their core orders.

Genuine amalgam recognition and ambient completion remain with
qt-d-1222-rankone-generic-global. The original uniqueness implication and
F.1.12 core bound remain explicit, with final source discharge retained by
qt-d-1222-rankone-generic and qt-d-1361-source.

Source: Aschbacher–Smith, 5.2.6, pp.650–651, E.2.13(4), p.225,
F.1.12(I)(4), pp.262–264, and the original application on p.795
(`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
open ChapterF.GreenBook.LieModels.UnitaryFour
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- The same selected factor excludes both triality orientations, retaining
all earlier G₂ and unitary exclusions and the original two-core intersection. -/
theorem rankOne_global_preparation_triality_exclusions_of_diagram
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
            (ChapterF.GreenBook.LieModels.G2.amalgam (F := GaloisField 2 m)).reverse)) ∧
      (∀ (m : ℕ) (hm : 0 < m),
        let α := Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)
        let β := ChapterF.GreenBook.LieModels.Triality.amalgam
          (_root_.Triality.Standard.binaryParameters m hm)
        ¬ Nonempty (RankTwoAmalgam.Iso α β) ∧
          ¬ Nonempty (RankTwoAmalgam.Iso α β.reverse)) := by
  obtain ⟨A,B,R,f,d,hp,hf,hlin,hnot,hlayers,hAN,hcount,hcountA,hSuz,hSU,hU,hG2⟩ :=
    D.rankOne_global_preparation_g2_exclusions_of_diagram
      h hmany hn hpsl hH hpar hthree hN hunique hd
  refine ⟨A,B,R,f,d,hp,hf,hlin,hnot,hlayers,hAN,hcount,hcountA,hSuz,hSU,hU,hG2,?_⟩
  intro m hm
  exact d.not_triality_amalgams
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH.1.1.2 hp hlayers m hm

/-- The source selects the whole residual, or a diagram factor excluding
all triality, G₂ and unitary comparisons. The whole-residual
U₅(4) row remains, as do the genuine earlier core-bound and uniqueness inputs. -/
theorem rankOne_global_residual_or_diagram_triality_exclusions_of_core_bound
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
              (ChapterF.GreenBook.LieModels.G2.amalgam (F := GaloisField 2 m)).reverse)) ∧
        (∀ (m : ℕ) (hm : 0 < m),
          let α := Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)
          let β := ChapterF.GreenBook.LieModels.Triality.amalgam
            (_root_.Triality.Standard.binaryParameters m hm)
          ¬ Nonempty (RankTwoAmalgam.Iso α β) ∧
            ¬ Nonempty (RankTwoAmalgam.Iso α β.reverse))) := by
  rcases D.rankOne_global_residual_or_diagram_of_core_bound h hmany hn hpsl
    hH hpar hN hunique hcore with ⟨A,B,d,hp⟩ | hd
  · exact ⟨A,B,residual H,d,hp,Or.inl rfl⟩
  · obtain ⟨A,B,R,f,d,hp,hf,hlin,hnot,hlayers,hAN,hcount,hcountA,hSuz,hSU,hU,hG2,hTr⟩ :=
      D.rankOne_global_preparation_triality_exclusions_of_diagram
        h hmany hn hpsl hH hpar hthree hN hunique hd
    exact ⟨A,B,R,d,hp,Or.inr ⟨⟨f,hf,hlin⟩,hnot,hlayers,hAN,hcount,hcountA,hSuz,hSU,hU,hG2,hTr⟩⟩

open _root_.Triality.Standard _root_.Triality.Standard.Parabolics in
/-- On the literal prepared Chapter12 pair, a surviving triality isomorphism
has the original exponent and the genuine central/arms local factors. This
application also covers the whole-residual branch; it does not assume the
two-layer diagram obstruction. -/
theorem rankOne_global_triality_local_structure
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B R : Subgroup G} (d : Global.Preparation T L H A B R)
    (hp : Group.IsPerfect R) (m : ℕ) (hm : 0 < m)
    (e : RankTwoAmalgam.Iso (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H))
      (ChapterF.GreenBook.LieModels.Triality.amalgam (binaryParameters m hm)).reverse) :
    m = n ∧ 1 < m ∧
      Nonempty (L ≃* localFactor (binaryParameters m hm) .central) ∧
      Nonempty (R ≃* localFactor (binaryParameters m hm) .arms) ∧
      ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 (2^(3*n)) ∧
      Nat.card (pCore 2 L) = (2^n)^11 ∧
      Nat.card (pCore 2 R) = (2^n)^9 ∧ Nat.card (center (pCore 2 R)) = 2^n :=
  d.triality_local_structure (D.rankOne_generic_input_of_many h hmany hn hpsl)
    hH.1.1.2 hp m hm e

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
