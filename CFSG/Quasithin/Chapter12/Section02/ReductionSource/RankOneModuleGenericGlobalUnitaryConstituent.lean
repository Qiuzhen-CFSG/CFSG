module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryConstituent
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalUnitaryIntersection

/-!
# Sizes of the remaining unitary overcomponent cores

The literal Chapter12 normalizer pair now either satisfies the source local
conditions, has an overcomponent core containing the original right core, or
has intersection of order q³ and quotient-image core of order q². In the last
case the intersection is elementary and the entire overcomponent core has
order at most 2q³. At q = 4, its faithful Frattini action excludes the
actual M₂₂, triple-cover M₂₂ and M₂₃ quotient alternatives. All maps refer
to the actual inclusion in J/O₂(J).

These are the natural-constituent and numerical bounds in the nonnormal
unitary paragraph of 5.2.8, printed pp.652–653 (`refs/quasithin.pdf`).
The containment exclusion, embedding selection and second-parabolic
contradiction remain with the global assembly; this is not a maximality or
ambient recognition theorem.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric ChapterF.GreenBook.LieModels.UnitaryFour
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- Apply the exact intersection and quotient-image sizes to every remaining
unitary overcomponent of the literal Chapter12 pair. -/
theorem rankOne_global_unitary_normalizer_or_small_core
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
        ((residual H).pCoreIn 2 ≤ J.pCoreIn 2 ∨
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
    · exact .inl hQR
    · obtain ⟨hN,hNc⟩ := d.unitary_overcomponent_proper_intersection hi hH hp m hm he hJ.1 hlt.le hQR
      obtain ⟨hfc,hRc⟩ := d.unitary_overcomponent_proper_quotient_core hi hH hp m hm he hJ.1 hlt.le hQR
      obtain ⟨hk,hmap,hfe,hfq,_⟩ := d.unitary_overcomponent_quotient_image hi hH hp m hm he hJ.1 hlt.le
      exact .inr ⟨hN,hNc,hRc,hk,hmap,hfe,hfc,hfq,fun hm2 =>
        d.unitary_four_proper_quotient_not_mathieu hi hH hp m hm he hJ.1 hlt.le hQR hm2⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
