module
public import CFSG.Quasithin.Chapter14.Section02.ComponentPlacement
public import CFSG.Quasithin.Chapter14.Section02.NormalAmalgam
public import CFSG.Quasithin.Chapter14.Section02.OddBorelSource
import all CFSG.Quasithin.ChapterB.Section06To07.Structure

/-!
# The selected original large-parabolic source and its normal amalgam

The large source sieve selects K on the original H carrier. Its unique
containing component Kc lies in Mc, with the actual normalizer inclusion
and the unique maximal overgroup of KcT. Each normal Bender branch now
has an actual F.1.1 rank-one quotient, S = T, the prescribed S₂, and
trivial two-core in the literal generated amalgam. This includes the
retained PSU₃/SU₃ row and does not assume its exclusion. The remaining
diagram and exchanged branches keep their genuine marked models.

Source: Aschbacher--Smith 14.2.8--9 and the normal branch of 14.2.13--15,
printed pp.983--985. The movement/cross-normalizer clauses of F.1.1,
the proper-index branch and the full F.1.12 classification remain open.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter14.Section02
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06 ChapterE
open Chapter1 Chapter1.Section02
open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
variable {G : Type*} [Group G] [Finite G]

theorem source_outside_large_bender_assembly
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hn : 1 < generationParameter H) :
    let TH := T.subtype hH.1.1.2
    let N := (H ⊓ M).subgroupOf H
    let Y := sourceResidual M Mc
    ∃ (K : Subgroup H) (Kc : Subgroup G) (f : ℕ),
      K.IsCComponent ∧ IsQuasisimple (K ⧸ pCore 2 K) ∧
      K ⊔ (TH : Subgroup H) = ⊤ ∧ ¬K.map H.subtype ≤ M ∧
      generationParameter H ≤ f ∧ 1 < f ∧
      Kc ∈ cComponentsIn Mc ∧ K.map H.subtype ≤ Kc ∧
      (∀ D ∈ cComponentsIn Mc, K.map H.subtype ≤ D → D = Kc) ∧
      Mc ⊓ normalizer (K.map H.subtype : Set G) ≤ normalizer (Kc : Set G) ∧
      maximalTwoLocalOvergroups (Kc ⊔ (T : Subgroup G)) = {Mc} ∧
      ((K.Normal ∧ BenderModel N K f ∧ pResidual 2 H = K ∧
        ChapterF.Source.IsRankOneModel (K ⧸ pCore 2 K) ∧
        let K₁ := K.map H.subtype
        let S := (T : Subgroup G) ⊓ normalizer (K₁ : Set G)
        let S₂ := Y.pCoreIn 2 ⊔ ((T : Subgroup G) ⊓ K₁)
        S = (T : Subgroup G) ∧ Y.pCoreIn 2 ≤ S ∧ S₂ ≤ S ∧
          pCore 2 (ChapterF.Source.generated ![K₁,Y ⊔ S₂] S) = ⊥) ∨
       (K.Normal ∧ DiagramModel N K (TH : Subgroup H) f) ∨
       (¬K.Normal ∧ ExchangedClauses N K (TH : Subgroup H) ∧
        ExchangedModel N K f ∧ (normalizer (K : Set H)).index = 2 ∧
        ((normalizer (K : Set H)).subgroupOf (TH : Subgroup H)).index = 2 ∧
        (K.subgroupOf (K ⊔ ((TH : Subgroup H) ⊓ normalizer (K : Set H)))).IsCComponent ∧
        ((2 ≤ f ∧ ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2^f)) ∨
          ∃ m : ℕ, 1 ≤ m ∧ f = 2*m+1 ∧
            Nonempty ((K ⧸ pCore 2 K) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)))) := by
  dsimp only
  obtain ⟨K,hK,hq,hgen,hout,f,hf,hf1,hm⟩ :=
    source_outside_large_models hG T hempty hM hu hmany hcard e H hH hn
  obtain ⟨Kc,hKc,hKC,huniq,hNK,_hmodel,hmax,_hnormal⟩ :=
    source_outside_component_placement hG T hempty hM hu hmany hcard e H hH K hK
  refine ⟨K,Kc,f,hK,hq,hgen,hout,hf,hf1,hKc,hKC,huniq,hNK,hmax,?_⟩
  rcases hm with ⟨hnorm,_hc,hm⟩ | hm
  · rcases hm with hm | hm
    · obtain ⟨_,hP,hN,_,_,_⟩ :=
        source_lemma_14_2_2_8_minimal hG T hempty hM hu hmany hcard e H hH
      have hNmax : (H ⊓ M).subgroupOf H = ChapterB.minimalParabolicMax (T.subtype hH.1.1.2) hP :=
        ChapterB.minimalParabolicMax_unique _ hP hN (by
          intro x hx
          exact ⟨x.property,hM.1.2 hx⟩)
      have hs : ¬Group.IsSolvable H := by
        intro hs
        let := hs
        exact (Nat.not_le_of_gt hn) generationParameter_le_one_of_solvable
      let := hnorm
      have hmodel : BenderModel (ChapterB.minimalParabolicMax (T.subtype hH.1.1.2) hP) K f :=
        hNmax ▸ hm
      obtain ⟨hr,_,_,hqF⟩ := source_normal_bender_kOne _ hP hs K hK hq hgen hmodel
      exact Or.inl ⟨hnorm,hm,hr,hqF,
        source_normal_amalgam_core hG T hempty hM hu hmany hcard e H hH K hgen⟩
    · exact Or.inr (Or.inl ⟨hnorm,hm⟩)
  · exact Or.inr (Or.inr hm)
end CFSG.Quasithin.Chapter14.Section02
