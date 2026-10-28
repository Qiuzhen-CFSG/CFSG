module
public import CFSG.Quasithin.Chapter14.Section02.LargeSource
public import CFSG.Quasithin.Chapter14.Section02.PairedCore

/-!
# Original large selection with the exchanged second parabolic constructed

Apply the new core and movement arguments to the component selected by the
original large-parabolic theorem. Both the marked model and index-two
normalizer come from that selector. Thus the exchanged branch has the
original O₂(M) and O₂(Y) containment, S₂≤S, the moving Y, and its actual
S₃ quotient and Sylow subgroup. No model, component or second-side witness
is an extra input to this source consumer.

The normal branches retain their original Bender or diagram models. Their
full normal Bender amalgam is independently constructed in NormalF11; the
proper-index generated-core theorem remains a subsequent source step.
Source: Aschbacher--Smith 14.2.8 and 14.2.12--14, printed pp.983--984.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter14.Section02
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06 ChapterE
open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
variable {G : Type*} [Group G] [Finite G]

theorem source_outside_large_paired_control
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃*
      Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hn : 1 < generationParameter H) :
    let TH := T.subtype hH.1.1.2
    let N := (H ⊓ M).subgroupOf H
    let Y := sourceResidual M Mc
    let S₂ := Y.pCoreIn 2 ⊔ ((T : Subgroup G) ⊓ (pResidual 2 H).map H.subtype)
    ∃ K : Subgroup H, K.IsCComponent ∧ IsQuasisimple (K ⧸ pCore 2 K) ∧
      K ⊔ (TH : Subgroup H) = ⊤ ∧ ¬K.map H.subtype ≤ M ∧
      ∃ f : ℕ, generationParameter H ≤ f ∧ 1 < f ∧
        ((K.Normal ∧ SingleClauses N K (TH : Subgroup H) ∧
          (BenderModel N K f ∨ DiagramModel N K (TH : Subgroup H) f)) ∨
         (¬K.Normal ∧ ExchangedClauses N K (TH : Subgroup H) ∧ ExchangedModel N K f ∧
          (normalizer (K : Set H)).index = 2 ∧
          ((normalizer (K : Set H)).subgroupOf (TH : Subgroup H)).index = 2 ∧
          (K.subgroupOf (K ⊔ ((TH : Subgroup H) ⊓ normalizer (K : Set H)))).IsCComponent ∧
          ((2 ≤ f ∧ ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2^f)) ∨
            ∃ m : ℕ, 1 ≤ m ∧ f = 2*m+1 ∧
              Nonempty ((K ⧸ pCore 2 K) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)) ∧
          let S := (T : Subgroup G) ⊓ normalizer (K.map H.subtype : Set G)
          M.pCoreIn 2 ≤ S ∧ Y.pCoreIn 2 ≤ S ∧ S₂ ≤ S ∧ Y = ⁅Y,S₂⁆ ∧
            Nonempty (((Y ⊔ S₂ : Subgroup G) ⧸ pCore 2 (Y ⊔ S₂ : Subgroup G)) ≃*
              Equiv.Perm (Fin 3)) ∧
            S ⊓ (Y ⊔ S₂) = S₂ ∧ Chapter1.IsSylowIn 2 S₂ (Y ⊔ S₂))) := by
  dsimp only
  obtain ⟨K,hK,hq,hgen,hout,f,hf,hf1,hcases⟩ :=
    source_outside_large_models hG T hempty hM hu hmany hcard e H hH hn
  refine ⟨K,hK,hq,hgen,hout,f,hf,hf1,?_⟩
  rcases hcases with hnormal | ⟨hnot,hc,hm,hi,hSi,hlocal,hmodel⟩
  · exact Or.inl hnormal
  · exact Or.inr ⟨hnot,hc,hm,hi,hSi,hlocal,hmodel,
      source_paired_second_parabolic hG T hempty hM hu hmany hcard e H hH hn K hK hgen hm hi⟩

end CFSG.Quasithin.Chapter14.Section02
