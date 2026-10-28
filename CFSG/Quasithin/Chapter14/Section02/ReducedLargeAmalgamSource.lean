module
public import CFSG.Quasithin.Chapter14.Section02.LargeAmalgamSource
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.NormalRankOneReduction
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.NormalUnitarySource

/-!
# The reduced original large-parabolic alternatives

Apply the nonabelian Frattini-orbit bounds to the component selected from the
original §14.2 hypotheses. All normal Suzuki and unitary cases disappear when
the actual closure is nonabelian, and the linear field is four or eight.
The actual component, Borel, Sylow and F.1.1 data remain available to the
recognition consumer. The abelian closure and the separate diagram/exchanged
branches retain their original mathematical content.

Source: Aschbacher–Smith 14.2.8–16, printed pp.983–986.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section02
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06 ChapterE
open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
variable {G : Type*} [Group G] [Finite G]
namespace LocalBinary

theorem source_normal_bender_nonabelian_models
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hnH : 1 < generationParameter H)
    (hne : ¬ IsMulCommutative (conjugateSpanBy (localModule T M) H))
    (K : Subgroup H) (hK : K.IsCComponent) [K.Normal]
    (hqK : IsQuasisimple (K ⧸ pCore 2 K))
    (hgen : K ⊔ (T.subtype hH.1.1.2 : Subgroup H) = ⊤)
    (f : ℕ) (hm : BenderModel ((H ⊓ M).subgroupOf H) K f) :
    (f = 2 ∨ f = 3) ∧
      ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2),
        Nat.card F = 2^f ∧
        ModelBorelPair ((H ⊓ M).subgroupOf H) K (BenderSuzuki.Converse.PBorel F) := by
  rcases hm with hm | hm
  · exact source_normal_rank_one_nonabelian_models hG T hempty hM hu hmany hcard e
      H hH hnH hne K hK hqK hgen f hm
  · exact (source_normal_unitary_false hG T hempty hM hu hmany hcard e
      H hH hnH hne K hK hqK hgen hm).elim

end LocalBinary
open Chapter1 Chapter1.Section02

theorem source_outside_large_reduced_amalgam_input
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
      ((K.Normal ∧ BenderModel N K f ∧
        (IsMulCommutative (conjugateSpanBy (localModule T M) H) ∨
          (f = 2 ∨ f = 3) ∧
            ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2),
              Nat.card F = 2^f ∧ ModelBorelPair N K (BenderSuzuki.Converse.PBorel F)) ∧
        pResidual 2 H = K ∧
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
    source_outside_large_amalgam_input hG T hempty hM hu hmany hcard e H hH hn
  refine ⟨K,Kc,f,hK,hq,hgen,hout,hf,hf1,hKc,hKC,huniq,hNK,hmax,?_⟩
  rcases hcases with ⟨hnorm,hm,hres,hqF,hF⟩ | hc
  · let := hnorm
    refine Or.inl ⟨hnorm,hm,?_,hres,hqF,hF⟩
    by_cases hab : IsMulCommutative (conjugateSpanBy (localModule T M) H)
    · exact Or.inl hab
    · exact Or.inr (LocalBinary.source_normal_bender_nonabelian_models
        hG T hempty hM hu hmany hcard e H hH hn hab K hK hq hgen f hm)
  · exact Or.inr hc

end CFSG.Quasithin.Chapter14.Section02
