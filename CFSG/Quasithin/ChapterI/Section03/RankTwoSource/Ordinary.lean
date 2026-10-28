module
public import CFSG.Quasithin.ChapterI.Section03.RankTwoSource.Structure
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.NoncentralFitting.TwoRank
public import Theory.GroupTheory.RankOneSylowExtension
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.NonnormalOrdinary

/-!
# Ordinary components in the two involution-pumpup branches

An injected simple rank-two subgroup survives the solvable two-core kernel.
A.3.6 forces the containing quotient C-component to be quasisimple. For a
nonnormal two-component, normality descends and the proved pre-ordinary
A.3.8 step applies instead. The two-core of a two-component is central, so
both conclusions lift along the actual perfect central cover.

Source: Aschbacher–Smith I.3.2, printed p.414, and the initial ordinary
component deduction in 2.5.19, printed p.561.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterI.RankTwoSource
/-- A simple rank-two subgroup survives the two-core quotient and forces an
actual two-component to be ordinary. -/
theorem twoComponent_quasisimple_of_simple_rank_two
    {G K:Type*} [Group G] [Finite G] [Group K] [Finite K]
    [IsSimpleGroup K] [Group.IsPerfect K] {κ:GroupClass}
    (hG:IsSQTK κ G) {L:Subgroup G} (hL:L.IsTwoComponent)
    (f:K→*L) (hf:Function.Injective f) (hr:2≤primeRank 2 K) :
    IsQuasisimple L := by
  let : Group.IsNilpotent (pCore 2 L):=pCore_isNilpotent
  let : Group.IsNilpotent (pCore 2 G):=pCore_isNilpotent
  let q:=QuotientGroup.mk' (pCore 2 G)
  let C:=L.map q
  let e:(L⧸pCore 2 L)≃*C:=cComponentTwoCoreQuotientEquiv hL.1
  let j:=e.toMonoidHom.comp ((QuotientGroup.mk' (pCore 2 L)).comp f)
  have hj:Function.Injective j:=e.injective.comp
    (Subgroup.RankOneSylowExtension.simple_quotient_injective
      (Group.IsPerfect.not_isSolvable K) f hf (pCore 2 L))
  have hrC:2≤primeRank 2 C:=hr.trans (Theory.GroupTheory.primeRank_le_of_injective 2 j hj)
  let : IsQuasisimple C:=
    ChapterA.Section03.NoncentralFitting.quasisimple_of_two_le_two_rank
      (ChapterI.RankTwoSource.sqtk_twoCore_quotient hG)
      (pCore_quotient_pCore_eq_bot 2) (hL.1.map_quotient (pCore 2 G)) hrC
  let : IsQuasisimple (L⧸pCore 2 L):=IsQuasisimple.of_mulEquiv e.symm
  let c:PerfectCentralCovering.Cover L (L⧸pCore 2 L):={
    toMonoidHom:=QuotientGroup.mk' (pCore 2 L)
    surjective:=QuotientGroup.mk'_surjective _
    isPerfect:=hL.1.perfect
    ker_le_center:=by
      rw [QuotientGroup.ker_mk']
      exact ChapterI.RankTwoSource.twoComponent_twoCore_central hL }
  exact c.isQuasisimple
/-- The nonnormal two-component branch of I.3.2 is ordinary in an SQTK group.
Nonnormality descends through the actual two-core quotient. -/
theorem twoComponent_quasisimple_of_not_normal {G:Type*} [Group G] [Finite G]
    {κ:GroupClass} (hG:IsSQTK κ G) {L:Subgroup G}
    (hL:L.IsTwoComponent) (hn:¬L.Normal) : IsQuasisimple L := by
  let : Group.IsNilpotent (pCore 2 G):=pCore_isNilpotent
  let q:=QuotientGroup.mk' (pCore 2 G)
  let C:=L.map q
  have hc:C.IsCComponent:=hL.1.map_quotient (pCore 2 G)
  have hnc:¬C.Normal := fun hh=>hn (cComponent_normal_of_quotient_normal hL.1 _ hh)
  let : IsQuasisimple C:=ChapterA.Section03.NonnormalOrdinary.quasisimple_of_not_normal
    (sqtk_twoCore_quotient hG) (pCore_quotient_pCore_eq_bot 2) C hc hnc
  let e:(L⧸pCore 2 L)≃*C:=cComponentTwoCoreQuotientEquiv hL.1
  let : IsQuasisimple (L⧸pCore 2 L):=IsQuasisimple.of_mulEquiv e.symm
  let c:PerfectCentralCovering.Cover L (L⧸pCore 2 L):={
    toMonoidHom:=QuotientGroup.mk' (pCore 2 L)
    surjective:=QuotientGroup.mk'_surjective _
    isPerfect:=hL.1.perfect
    ker_le_center:=by
      rw [QuotientGroup.ker_mk']
      exact twoComponent_twoCore_central hL }
  exact c.isQuasisimple
end CFSG.Quasithin.ChapterI.RankTwoSource
