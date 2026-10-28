module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryCenter
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalUnitaryContainment

/-!
# Removing unitary core containment from the Chapter12 alternative

For the literal Chapter12 normalizer pair, the remaining maximal unitary
overcomponent has Q not contained in its two-core. The center calculation
and earlier 1.2.7 uniqueness argument eliminate the entire containment
branch, including the degree-two field-four extension. The surviving branch
retains the actual elementary q³ intersection, q² quotient-image core,
PSL₂ quotient and Mathieu exclusions, with their original quotient map.

The proper-intersection embedding selection and second-parabolic argument,
other maximality rows, exhaustive comparison and ambient recognition remain
with the global assembly. Source: Aschbacher–Smith 5.2.8, printed pp.652–653
(`refs/quasithin.pdf`), using the earlier 1.2.7 normalizer uniqueness theorem.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric ChapterF.GreenBook.LieModels.UnitaryFour
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- The contained-core alternative is impossible; only the actual proper
intersection branch remains before unitary maximality. -/
theorem rankOne_global_unitary_normalizer_or_proper_core
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
             Nonempty ((J ⧸ pCore 2 J) ≃* Sporadic.Mathieu.M23)))) := by
  have hi := D.rankOne_generic_input_of_many h hmany hn hpsl
  rcases D.rankOne_global_unitary_normalizer_or_refined_core h hmany hn hpsl
      hH d hp m hm he with hlocal | ⟨J,hKJ,hJ,hlt,hnorm,hcore⟩
  · exact .inl hlocal
  · have hnot := d.unitary_nonnormal_core_not_le hi hH hp m hm he hJ hKJ hnorm
    rcases hcore with hc | hc
    · exact (hnot hc.1).elim
    · exact .inr ⟨J,hKJ,hJ,hlt,hnorm,hnot,hc⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
