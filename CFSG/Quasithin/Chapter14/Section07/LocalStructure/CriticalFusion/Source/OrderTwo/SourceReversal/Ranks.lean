module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.OrderTwo.SourceReversal.Geometry

/-!
# Reverse rank selection from the same marked quotient orders

The two central point markings transport their actual normalizers and
two-cores. Mapping relative indices with the same conjugator exchanges
(U∩Qα : U) and the order of Uα in H/O₂(H). Thus the source equality of
these ranks gives the reverse rank comparison and its positivity. The
actual placement theorem supplies EarlierImages for the constructed path.
This proves EarlierSymmetry rather than assuming a reversed witness.

Source: Aschbacher–Smith F.9.17 and14.7.39, pp.324 and1060.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.SourceReversal
open Chapter12.Section08
universe u
variable {G:Type u} [Group G] [Finite G] {T:Sylow 2 G} {L V:Subgroup G}
 {F:InvariantFlag T V 3} {W:Type u} [AddCommGroup W] [Module (ZMod 2) W]

omit [Finite G] in
private theorem conjugate_normalizer (A:Subgroup G) (g:G) :
    conjugate (normalizer (A:Set G)) g=normalizer (conjugate A g:Set G) :=
  map_equiv_normalizer_eq A (MulAut.conj g⁻¹)

namespace Geometry
variable {c:CriticalPath (L:=L) F} (r:Geometry c)

omit [Finite G] in
theorem base_H : conjugate F.H r.conjugator=conjugate F.H c.conjugator := by
  change conjugate (normalizer (F.Vi 1:Set G)) r.conjugator=
    conjugate (normalizer (F.Vi 1:Set G)) c.conjugator
  rw [conjugate_normalizer,conjugate_normalizer,r.base_point]
  rfl

omit [Finite G] in
theorem tip_H : conjugate (conjugate F.H r.path.conjugator) r.conjugator=F.H := by
  change conjugate (conjugate (normalizer (F.Vi 1:Set G)) r.path.conjugator) r.conjugator=F.H
  rw [conjugate_normalizer,conjugate_normalizer]
  change normalizer (conjugate r.path.Zα r.conjugator:Set G)=F.H
  rw [r.tip_point]
  rfl

omit [Finite G] in
theorem base_core : conjugate (F.H.pCoreIn 2) r.conjugator=c.Qα := by
  change (F.H.pCoreIn 2).map (MulAut.conj r.conjugator⁻¹).toMonoidHom=c.Qα
  rw [map_pCoreIn_of_injective 2 _ _ (MulAut.conj r.conjugator⁻¹).injective]
  change (conjugate F.H r.conjugator).pCoreIn 2=c.Qα
  rw [r.base_H]
  rfl

omit [Finite G] in
theorem tip_core : conjugate r.path.Qα r.conjugator=F.H.pCoreIn 2 := by
  change ((conjugate F.H r.path.conjugator).pCoreIn 2).map
    (MulAut.conj r.conjugator⁻¹).toMonoidHom=F.H.pCoreIn 2
  rw [map_pCoreIn_of_injective 2 _ _ (MulAut.conj r.conjugator⁻¹).injective]
  change (conjugate (conjugate F.H r.path.conjugator) r.conjugator).pCoreIn 2=F.H.pCoreIn 2
  rw [r.tip_H]

omit [Finite G] in
/-- The reverse denominator is the original starred actor, with both kernels
 transported through the original central points. -/
theorem reverse_index (earlier:c.EarlierImages) :
    (F.U⊓r.path.Qα).relIndex F.U=Nat.card (star F c.Uα) := by
  have ht:=relIndex_map_map_of_injective
    (f:=(MulAut.conj r.conjugator⁻¹).toMonoidHom) (F.U⊓r.path.Qα) F.U
    (MulAut.conj r.conjugator⁻¹).injective
  change (conjugate (F.U⊓r.path.Qα) r.conjugator).relIndex
    (conjugate F.U r.conjugator)=(F.U⊓r.path.Qα).relIndex F.U at ht
  rw [conjugate_inf,r.base_U,r.tip_core,inf_comm,
    CriticalIntersections.core_intersection_index_eq_star_card _ (c.Uα_le_H earlier)] at ht
  exact ht.symm

omit [Finite G] in
/-- The reverse starred actor is the original denominator. -/
theorem reverse_star (earlier:r.path.EarlierImages) :
    Nat.card (star F r.path.Uα)=(F.U⊓c.Qα).relIndex F.U := by
  have ht:=relIndex_map_map_of_injective
    (f:=(MulAut.conj r.conjugator⁻¹).toMonoidHom) (F.H.pCoreIn 2⊓r.path.Uα) r.path.Uα
    (MulAut.conj r.conjugator⁻¹).injective
  change (conjugate (F.H.pCoreIn 2⊓r.path.Uα) r.conjugator).relIndex
    (conjugate r.path.Uα r.conjugator)=(F.H.pCoreIn 2⊓r.path.Uα).relIndex r.path.Uα at ht
  rw [conjugate_inf,r.base_core,r.tip_U,inf_comm,
    CriticalIntersections.core_intersection_index_eq_star_card _ (r.path.Uα_le_H earlier)] at ht
  exact ht.symm
end Geometry

theorem source_reversal (d:Data T L V F W)
    (structural:Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (c:CriticalPath (L:=L) F) (earlier:c.EarlierImages) (selection:c.RankSelection)
    (hr:Nat.log 2 ((F.U⊓c.Qα).relIndex F.U)=Nat.log 2 (Nat.card (star F c.Uα))) :
    Nonempty c.Reversal := by
  obtain ⟨r⟩:=exists_geometry d structural c earlier selection
  have he:=d.source_earlierImages structural r.path earlier.image_eq earlier.sylow
  have hs:r.path.RankSelection := {
    positive:=by
      rw [r.reverse_index earlier]
      exact lt_of_lt_of_le selection.positive selection.comparison
    comparison:=by
      rw [r.reverse_index earlier,r.reverse_star he]
      exact hr.symm.le }
  exact ⟨⟨r.path,r.conjugator,r.conjugator_mem,r.base_U,r.tip_U,r.base_point,r.tip_point,he,hs⟩⟩

/-- The original14.7.39/F.9.17 implication, with every geometric and reverse
 rank-selection field proved. -/
theorem earlierSymmetry (d:Data T L V F W)
    (structural:Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u}) :
    d.EarlierSymmetry := by
  intro c hc hs hr
  exact source_reversal d structural c hc hs.toRankSelection hr
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.SourceReversal
