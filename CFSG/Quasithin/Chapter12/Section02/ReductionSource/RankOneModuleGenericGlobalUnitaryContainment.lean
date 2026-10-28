module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryContainment
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalUnitaryConstituent

/-!
# The field-four containment remainder in the unitary argument

Apply the core-containment analysis to the literal Chapter12 normalizer pair.
A nonnormal overcomponent core containing Q can only occur in the degree-two
unitary extension at m = 2 and original n = 4. Its quotient is in the actual
A.3.14 shortlist, its core has order 2q⁵, and that core equals both O₂(H)
and O₂(KS). Its center lies in Z(Q). The other branch retains the elementary
q³ intersection, q² quotient-image core, and actual Mathieu exclusions.

The containment remainder is explicit: this is not core normality or unitary
maximality. Its exclusion, the proper-intersection embedding selection and
second-parabolic contradiction, the remaining maximality rows, exhaustive
comparison and ambient recognition still belong to the global assembly.
Source: Aschbacher–Smith 5.2.8, printed pp.652–653 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric ChapterF.GreenBook.LieModels.UnitaryFour
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- The original unitary pair has the source local conditions, a precise
field-four extended containment remainder, or the proper q³ intersection. -/
theorem rankOne_global_unitary_normalizer_or_refined_core
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
        (((residual H).pCoreIn 2 ≤ J.pCoreIn 2 ∧ m = 2 ∧ n = 4 ∧
          ChapterA.Section03.SourceEmbeddings.AlternatingFive.Shortlist (J ⧸ pCore 2 J) ∧
          (Nonempty (RankTwoAmalgam.Iso
            (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H)) (Extension.amalgam m hm)) ∨
           Nonempty (RankTwoAmalgam.Iso
            (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H)) (Extension.amalgam m hm).reverse)) ∧
          ((residual H).pCoreIn 2).relIndex (J.pCoreIn 2) = 2 ∧
          Nat.card (J.pCoreIn 2) = 2*(2^m)^5 ∧
          J.pCoreIn 2 = H.pCoreIn 2 ∧
          J.pCoreIn 2 = (residual H ⊔ Global.sourceS L H).pCoreIn 2 ∧
          (center (J.pCoreIn 2)).map (J.pCoreIn 2).subtype ≤
            (center ((residual H).pCoreIn 2)).map ((residual H).pCoreIn 2).subtype) ∨
          (IsElementaryAbelian 2 (residual H ⊓ J.pCoreIn 2 : Subgroup G) ∧
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
                 Nonempty ((J ⧸ pCore 2 J) ≃* Sporadic.Mathieu.M23)))))) := by
  have hi := D.rankOne_generic_input_of_many h hmany hn hpsl
  rcases d.unitary_normalizer_or_nonnormal_core hi hH hp m hm he with hlocal | ⟨J,hJ,hlt,hnorm⟩
  · exact .inl hlocal
  · refine .inr ⟨J,hlt.le,hJ,hlt,hnorm,?_⟩
    by_cases hQR : (residual H).pCoreIn 2 ≤ J.pCoreIn 2
    · obtain ⟨hm2,hn4,hs,hext,hidx,hcard⟩ :=
        d.unitary_nonnormal_containment hi hH hp m hm he hJ.1 hlt hQR hnorm
      obtain ⟨hRH,hRU⟩ :=
        d.unitary_nonnormal_containment_core_eq hi hH hp m hm he hJ.1 hlt hQR hnorm
      exact .inl ⟨hQR,hm2,hn4,hs,hext,hidx,hcard,hRH,hRU,
        d.unitary_contained_overcomponent_center_le hi hH hp m hm he hJ.1 hlt.le hQR⟩
    · obtain ⟨hN,hNc⟩ := d.unitary_overcomponent_proper_intersection hi hH hp m hm he hJ.1 hlt.le hQR
      obtain ⟨hfc,hRc⟩ := d.unitary_overcomponent_proper_quotient_core hi hH hp m hm he hJ.1 hlt.le hQR
      obtain ⟨hk,hmap,hfe,hfq,_⟩ := d.unitary_overcomponent_quotient_image hi hH hp m hm he hJ.1 hlt.le
      exact .inr ⟨hN,hNc,hRc,hk,hmap,hfe,hfc,hfq,fun hm2 =>
        d.unitary_four_proper_quotient_not_mathieu hi hH hp m hm he hJ.1 hlt.le hQR hm2⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
