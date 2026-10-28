module
public import CFSG.Quasithin.Chapter14.Section02.LargeSource
public import CFSG.Quasithin.Chapter14.Section02.UnitaryKOne
import all CFSG.Quasithin.ChapterB.Section06To07.Structure

/-!
# The original K₁ source selection in the two Bender branches

Apply the normal and exchanged quotient arguments to the same escaping
component supplied by the large outside-parabolic theorem. In the normal
linear/Suzuki branch K₁ is literally O²(H), with S = T. In the exchanged
branch K₁ is the original component, with its actual index-two normalizer
in T. The marked Borel and original two-core quotients are retained in
both cases. The unitary row retains its actual projective or special
unitary quotient and supplies the rank-one condition in F.1.1. Its
exclusion and the diagram selection remain separate source arguments.

Source: Aschbacher--Smith 14.2.8, printed p.983.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter14.Section02
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06 ChapterE
open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
variable {G : Type*} [Group G] [Finite G]

theorem source_outside_large_kOne
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hn : 1 < generationParameter H) :
    let S := T.subtype hH.1.1.2
    let N := (H ⊓ M).subgroupOf H
    ∃ K : Subgroup H, K.IsCComponent ∧ IsQuasisimple (K ⧸ pCore 2 K) ∧
      K ⊔ (S : Subgroup H) = ⊤ ∧ ¬K.map H.subtype ≤ M ∧
      ∃ f : ℕ, generationParameter H ≤ f ∧ 1 < f ∧
        ((K.Normal ∧ SingleClauses N K (S : Subgroup H) ∧
          ((ExchangedModel N K f ∧ pResidual 2 H = K ∧ sourceKernel N = pCore 2 H ∧
            (S : Subgroup H) ⊓ normalizer (K : Set H) = (S : Subgroup H) ∧
            (K.subgroupOf (K ⊔ (S : Subgroup H))).IsCComponent ∧
            ((2 ≤ f ∧ ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2^f)) ∨
              ∃ m : ℕ, 1 ≤ m ∧ f = 2*m+1 ∧
                Nonempty ((K ⧸ pCore 2 K) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m))) ∨
            (UnitaryModel N K f ∧ pResidual 2 H = K ∧
              (S : Subgroup H) ⊓ normalizer (K : Set H) = (S : Subgroup H) ∧
              (K.subgroupOf (K ⊔ (S : Subgroup H))).IsCComponent ∧
              ChapterF.Source.IsRankOneModel (K ⧸ pCore 2 K)) ∨
            DiagramModel N K (S : Subgroup H) f)) ∨
         (¬K.Normal ∧ ExchangedClauses N K (S : Subgroup H) ∧
          ExchangedModel N K f ∧ (normalizer (K : Set H)).index = 2 ∧
          ((normalizer (K : Set H)).subgroupOf (S : Subgroup H)).index = 2 ∧
          (K.subgroupOf (K ⊔ ((S : Subgroup H) ⊓ normalizer (K : Set H)))).IsCComponent ∧
          ((2 ≤ f ∧ ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2^f)) ∨
            ∃ m : ℕ, 1 ≤ m ∧ f = 2*m+1 ∧
              Nonempty ((K ⧸ pCore 2 K) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)))) := by
  dsimp only
  obtain ⟨K,hK,hq,hgen,hout,f,hf,hf1,hm⟩ :=
    source_outside_large_models hG T hempty hM hu hmany hcard e H hH hn
  refine ⟨K,hK,hq,hgen,hout,f,hf,hf1,?_⟩
  rcases hm with ⟨hnorm,hc,hm⟩ | hm
  · refine Or.inl ⟨hnorm,hc,?_⟩
    rcases hm with (hm | hm) | hm
    · obtain ⟨_,hP,hN,_,_,_⟩ :=
        source_lemma_14_2_2_8_minimal hG T hempty hM hu hmany hcard e H hH
      have hmax : (H ⊓ M).subgroupOf H = ChapterB.minimalParabolicMax (T.subtype hH.1.1.2) hP :=
        ChapterB.minimalParabolicMax_unique _ hP hN (by
          intro x hx
          exact ⟨x.property,hM.1.2 hx⟩)
      have hs : ¬Group.IsSolvable H := by
        intro hs
        let := hs
        exact (Nat.not_le_of_gt hn) generationParameter_le_one_of_solvable
      let := hnorm
      have hmodel : ExchangedModel (ChapterB.minimalParabolicMax (T.subtype hH.1.1.2) hP) K f :=
        hmax ▸ hm
      obtain ⟨hr,hcore,hS,hlocal,hq⟩ :=
        source_normal_rank_one_kOne _ hP hs K hK hq hgen hmodel
      refine Or.inl ⟨hm,hr,?_,hS,hlocal,hq⟩
      rw [hmax]
      exact hcore
    · obtain ⟨_,hP,hN,_,_,_⟩ :=
        source_lemma_14_2_2_8_minimal hG T hempty hM hu hmany hcard e H hH
      have hmax : (H ⊓ M).subgroupOf H = ChapterB.minimalParabolicMax (T.subtype hH.1.1.2) hP :=
        ChapterB.minimalParabolicMax_unique _ hP hN (by
          intro x hx
          exact ⟨x.property,hM.1.2 hx⟩)
      have hs : ¬Group.IsSolvable H := by
        intro hs
        let := hs
        exact (Nat.not_le_of_gt hn) generationParameter_le_one_of_solvable
      let := hnorm
      have hmodel : UnitaryModel (ChapterB.minimalParabolicMax (T.subtype hH.1.1.2) hP) K f :=
        hmax ▸ hm
      exact Or.inr (Or.inl ⟨hm,source_normal_bender_kOne _ hP hs K hK hq hgen (Or.inr hmodel)⟩)
    · exact Or.inr (Or.inr hm)
  · exact Or.inr hm
end CFSG.Quasithin.Chapter14.Section02
