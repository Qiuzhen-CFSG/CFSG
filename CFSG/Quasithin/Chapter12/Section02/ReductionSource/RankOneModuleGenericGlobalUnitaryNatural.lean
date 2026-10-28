module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryNatural
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalUnitaryCenter

/-!
# The actual natural quotient in the Chapter12 unitary branch

The literal map K → J/O₂(J) has a centerless natural SL₂ block as image,
with its entire elementary two-core. Its local C-component condition uses
the full image of T ∩ J, and that Sylow normalizes the same image. The
containing quotient is SQTK and a C-component. All preceding core orders,
kernel identities and field-four Mathieu exclusions are retained.

This supplies the natural-block input to the proper-embedding argument.
The (S)L₃ selection, second-parabolic contradiction and final global exit
remain to be proved. Source: Aschbacher–Smith 5.2.8, printed pp.652–653
(`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric ChapterF.GreenBook.LieModels.UnitaryFour
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- The remaining overcomponent has an actual centerless natural quotient
image, with the original full Sylow and all previous core data retained. -/
theorem rankOne_global_unitary_normalizer_or_natural_image
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
  rcases D.rankOne_global_unitary_normalizer_or_proper_core h hmany hn hpsl
      hH d hp m hm he with hlocal | ⟨J,hKJ,hJ,hlt,hnorm,hnot,hN,hNc,hRc,hf⟩
  · exact .inl hlocal
  · obtain ⟨hb,hcore,hcenter⟩ :=
      d.unitary_overcomponent_proper_image_block hi hH hp m hm he hJ.1 hKJ hnot
    obtain ⟨hsq,htop,hproper,S,hS,hlocal,hSnorm⟩ :=
      d.unitary_overcomponent_embedding_context hi hH hp m hm he hJ.1 hlt
    exact .inr ⟨J,hKJ,hJ,hlt,hnorm,hnot,hN,hNc,hRc,
      hf.1,hf.2.1,hf.2.2.1,hf.2.2.2.1,hf.2.2.2.2.1,hf.2.2.2.2.2,
      hb,hcore,hcenter,hsq,htop,hproper,S,hS,hlocal,hSnorm⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
