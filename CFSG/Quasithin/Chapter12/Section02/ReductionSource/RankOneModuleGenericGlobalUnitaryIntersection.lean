module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryIntersection
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalUnitaryFour

/-!
# The unitary overcomponent intersection in the literal Chapter12 pair

For the actual K = O²(H), put Q = O₂(K), R = O₂(J). Every remaining
maximal overcomponent has noncentral K ∩ R, with [K ∩ R,Q] = Z(Q),
Z(Q) ≤ R and |R : K ∩ R| ≤ 2. The actual inclusion into J/O₂(J) kills
precisely R ∩ K; its image has elementary two-core and the original
PSL₂(2^m) quotient. Both unitary orientations and the degree-two extension
use the same original source S and whole overlap.

This refines the remaining nonnormal-core alternative; it does not yet
exclude it. The natural-constituent calculation, embedding selection and
second-parabolic contradiction in 5.2.8 remain with the global assembly,
as do the outstanding comparison and ambient recognition obligations.
Source: Aschbacher–Smith 5.2.8, printed pp.652–653, and Chapter12, p.795
(`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric ChapterF.GreenBook.LieModels.UnitaryFour
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- Apply the noncentral intersection and literal quotient-image calculation
to the remaining maximal overcomponent in the original Chapter12 setup. -/
theorem rankOne_global_unitary_normalizer_or_core_intersection
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
        (let Q := (residual H).pCoreIn 2
         let R := J.pCoreIn 2
         let Z := (center Q).map Q.subtype
         R ≤ Global.sourceS L H ∧ residual H ⊓ R ≤ Q ∧
           ¬ residual H ⊓ R ≤ centralizer (residual H : Set G) ∧
           ⁅residual H ⊓ R,Q⁆ = Z ∧ Z ≤ residual H ⊓ R ∧
           (residual H ⊓ R).relIndex R ≤ 2) ∧
        (let f := (QuotientGroup.mk' (pCore 2 J)).comp (inclusion hKJ)
         f.ker = (J.pCoreIn 2).subgroupOf (residual H) ∧
           (pCore 2 (residual H)).map f = f.range.pCoreIn 2 ∧
           IsElementaryAbelian 2 (pCore 2 f.range) ∧
           ClassicalGroup.IsPSL (f.range ⧸ pCore 2 f.range) 2 (2^m) ∧
           (pCore 2 f.range = ⊥ ↔ (residual H).pCoreIn 2 ≤ J.pCoreIn 2)) := by
  have hi := D.rankOne_generic_input_of_many h hmany hn hpsl
  rcases d.unitary_normalizer_or_nonnormal_core hi hH hp m hm he with hlocal | ⟨J,hJ,hlt,hnorm⟩
  · exact .inl hlocal
  · exact .inr ⟨J,hlt.le,hJ,hlt,hnorm,
      d.unitary_overcomponent_core_intersection hi hH hp m hm he hJ.1 hlt.le,
      d.unitary_overcomponent_quotient_image hi hH hp m hm he hJ.1 hlt.le⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
