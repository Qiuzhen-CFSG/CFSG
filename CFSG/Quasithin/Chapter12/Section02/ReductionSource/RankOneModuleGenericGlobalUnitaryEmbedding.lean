module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryEmbedding
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalUnitaryNatural

/-!
# The containing-carrier sieve for the Chapter12 unitary image

The actual proper quotient image is a centerless natural SL₂ block.
It embeds through the overcomponent quotient's center, retaining its
full two-core, natural action, and the image of the original full Sylow.
The genuine A.3.6 and Theorem C catalogues leave rank-two and six
sporadic carriers; the G₂ family is excluded by its parabolic core order.
All preceding original quotient-image and core-intersection data remain.

The remaining carrier comparisons, (S)L₃ identification and second-parabolic
contradiction are still required. This is not unitary maximality or the
ambient GlobalExit. Source: Aschbacher–Smith 5.2.8, printed pp.652–653,
with A.3.6/A.3.12 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric ChapterF.GreenBook.LieModels.UnitaryFour
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- The actual remaining overcomponent has a quasisimple quotient and
a reduced central-quotient carrier catalogue, with every previous marking retained. -/
theorem rankOne_global_unitary_normalizer_or_embedding_models
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B : Subgroup G} (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H)) (m : ℕ) (hm : 1 ≤ m)
    (he : (Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H)) (amalgam m hm)) ∨
      Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H)) (amalgam m hm).reverse)) ∨
      (Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H)) (Extension.amalgam m hm)) ∨
      Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H)) (Extension.amalgam m hm).reverse))) :
    Chapter5.Section03GreenExtension.SourceLocalConditions
      (Global.normalizerAmalgam L (residual H)) L (residual H) ((T : Subgroup G) ⊓ L) ∨
      ∃ (J : Subgroup G) (hKJ : residual H ≤ J),
        J ∈ Chapter1.LStar G (T : Subgroup G) ∧ residual H < J ∧
        ¬ J ≤ normalizer ((residual H).pCoreIn 2 : Set G) ∧
        ¬ (residual H).pCoreIn 2 ≤ J.pCoreIn 2 ∧
        IsElementaryAbelian 2 (residual H ⊓ J.pCoreIn 2 : Subgroup G) ∧
        Nat.card (residual H ⊓ J.pCoreIn 2 : Subgroup G) = (2^m)^3 ∧
        Nat.card (J.pCoreIn 2) ≤ 2*(2^m)^3 ∧
        IsQuasisimple (J ⧸ pCore 2 J) ∧
        Global.UnitaryEmbedding.RemainingModels
          ((J ⧸ pCore 2 J) ⧸ center (J ⧸ pCore 2 J)) ∧
        (let f := (QuotientGroup.mk' (pCore 2 J)).comp (inclusion hKJ)
         f.ker = (J.pCoreIn 2).subgroupOf (residual H) ∧
           (pCore 2 (residual H)).map f = f.range.pCoreIn 2 ∧
           IsElementaryAbelian 2 (pCore 2 f.range) ∧
           Nat.card (pCore 2 f.range) = (2^m)^2 ∧
           ClassicalGroup.IsPSL (f.range ⧸ pCore 2 f.range) 2 (2^m) ∧
           (m = 2 → ¬ (Nonempty ((J ⧸ pCore 2 J) ≃* Sporadic.Mathieu.M22) ∨
             Chapter1.Section02.LocalModels.IsM22Cover (J ⧸ pCore 2 J) ∨
             Nonempty ((J ⧸ pCore 2 J) ≃* Sporadic.Mathieu.M23))) ∧
           ChapterC.IsL2EvenBlock f.range m ∧
           pCore 2 f.range = ChapterC.blockU f.range ∧ center f.range = ⊥ ∧
           IsSQTK KnownSimple.IsKnownSimple (J ⧸ pCore 2 J) ∧
           (⊤ : Subgroup (J ⧸ pCore 2 J)).IsCComponent ∧ f.range ≠ ⊤ ∧
           ∃ S : Sylow 2 J, (S : Subgroup J) = (T : Subgroup G).subgroupOf J ∧
             (let Sb := S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 J))
              f.range ∈ ChapterA.Section03.localCComponents Sb ∧
                (Sb : Subgroup (J ⧸ pCore 2 J)) ≤ normalizer (f.range : Set _))) := by
  have hi := D.rankOne_generic_input_of_many h hmany hn hpsl
  rcases D.rankOne_global_unitary_normalizer_or_natural_image h hmany hn hpsl
      hH d hp m hm he with hlocal | ⟨J,hKJ,hJ,hlt,hnorm,hnot,hN,hNc,hRc,hf⟩
  · exact .inl hlocal
  · obtain ⟨hq,hmodels⟩ := d.unitary_overcomponent_central_quotient_models
      hi hH hp m hm he hJ.1 hlt hnot
    exact .inr ⟨J,hKJ,hJ,hlt,hnorm,hnot,hN,hNc,hRc,hq,hmodels,hf⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
