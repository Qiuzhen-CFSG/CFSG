module
public import CFSG.Quasithin.Chapter14.Section02.LargeBenderSource
public import CFSG.Quasithin.Chapter14.Section02.NormalF11

/-!
# The selected large-parabolic source with a complete normal amalgam

The genuine original large-parabolic selector supplies the component,
its containing component in Mc, the marked normalizer and the actual
model alternatives. Every normal Bender alternative now constructs the
literal corrected F.1.1 hypothesis, together with Y=[Y,S₂] and both
Borel identities. The exchanged and diagram alternatives retain their
existing source data for their separate K₁ and placement arguments.
The full F.1.12 classification is not asserted here.

Source: Aschbacher--Smith 14.2.7--16, printed pp.982--986.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter14.Section02
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06 ChapterE
open Chapter1 Chapter1.Section02
open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
variable {G : Type*} [Group G] [Finite G]

theorem source_outside_large_amalgam_input
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
        ChapterF.Source.HypothesisF11 ![K₁,Y ⊔ S₂] S ∧
          S = (T : Subgroup G) ∧ Y = ⁅Y,S₂⁆ ∧
          ChapterF.Source.borel K₁ S = M ⊓ K₁ ∧
          ChapterF.Source.borel (Y ⊔ S₂) S = S₂) ∨
       (K.Normal ∧ DiagramModel N K (TH : Subgroup H) f) ∨
       (¬K.Normal ∧ ExchangedClauses N K (TH : Subgroup H) ∧
        ExchangedModel N K f ∧ (normalizer (K : Set H)).index = 2 ∧
        ((normalizer (K : Set H)).subgroupOf (TH : Subgroup H)).index = 2 ∧
        (K.subgroupOf (K ⊔ ((TH : Subgroup H) ⊓ normalizer (K : Set H)))).IsCComponent ∧
        ((2 ≤ f ∧ ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2^f)) ∨
          ∃ m : ℕ, 1 ≤ m ∧ f = 2*m+1 ∧
            Nonempty ((K ⧸ pCore 2 K) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)))) := by
  dsimp only
  obtain ⟨K,Kc,f,hK,hq,hgen,hout,hf,hf1,hKc,hKC,huniq,hNK,hmax,hcases⟩ :=
    source_outside_large_bender_assembly hG T hempty hM hu hmany hcard e H hH hn
  refine ⟨K,Kc,f,hK,hq,hgen,hout,hf,hf1,hKc,hKC,huniq,hNK,hmax,?_⟩
  rcases hcases with ⟨hnorm,hm,hres,hqF,_⟩ | hc
  · let := hnorm
    exact Or.inl ⟨hnorm,hm,hres,hqF,
      source_normal_bender_hypothesis_F_1_1 hG T hempty hM hu hmany hcard e H hH K hgen hres hqF⟩
  · exact Or.inr hc
end CFSG.Quasithin.Chapter14.Section02
