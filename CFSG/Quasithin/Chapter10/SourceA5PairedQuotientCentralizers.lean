module
public import CFSG.Quasithin.Chapter10.SourceA5OriginalPairedAxes
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.PairResidualCentralizers

/-!
# The original block centralizer in the paired quotient

Locate the original block image on the marked alternating axis and then
compute its centralizer inside the same offender subgroup. It is the
opposite full symmetric-five factor. In particular the image of the
actual block centralizer in the product preimage lies in that factor.

Source: Aschbacher–Smith 10.2.1, pp.742–743. Surjectivity of the original
block centralizer onto this factor is a distinct lifting assertion.
-/

public section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterC ChapterE.ThompsonAction
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

@[expose] def SourceOriginalPairedCentralizers : Prop :=
  let H := localJoin T L
  let S := T.subtype (show (T : Subgroup G) ≤ H from le_sup_right)
  let U := D.moduleSubgroup.subgroupOf H
  letI := (source_parabolic_module_reduced D).normal
  letI := (source_parabolic_module_reduced D).elementary
  let C := centralizer (U : Set H)
  let q := QuotientGroup.mk' C
  let α := NormalElementaryQuotient.representation U q
      (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
  let Y := offenderSubgroup α
  letI := offenderSubgroup_normal α
  let A := L.subgroupOf H
  ∃ d : ChapterB.SourceInduction.SourceTwoFactorCase (α.comp Y.subtype),
    ∃ _c : d.MarkedProduct (BinaryPermutation.naturalRepresentation (Fin 5)),
      (∃ t : S.mapSurjective (QuotientGroup.mk'_surjective C),
        d.first.map (MulAut.conjNormal (t : H ⧸ C)).toMonoidHom = d.second ∧
        d.second.map (MulAut.conjNormal (t : H ⧸ C)).toMonoidHom = d.first) ∧
      Y.comap q ≤ normalizer (A : Set H) ∧
      ((A.map q = (factorResidual q Y d.first).map q ∧
        Y ⊓ centralizer (A.map q : Set (H ⧸ C)) = d.second.map Y.subtype ∧
        (Y.comap q ⊓ centralizer (A : Set H)).map q ≤ d.second.map Y.subtype) ∨
       (A.map q = (factorResidual q Y d.second).map q ∧
        Y ⊓ centralizer (A.map q : Set (H ⧸ C)) = d.first.map Y.subtype ∧
        (Y.comap q ⊓ centralizer (A : Set H)).map q ≤ d.first.map Y.subtype))

theorem source_a5_original_paired_centralizers
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hout : ¬ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ D.maximalLocal) :
    SourceOriginalPairedCentralizers D := by
  let H := localJoin T L
  let U := D.moduleSubgroup.subgroupOf H
  let := (source_parabolic_module_reduced D).normal
  let := (source_parabolic_module_reduced D).elementary
  let C := centralizer (U : Set H)
  let q := QuotientGroup.mk' C
  have hq := QuotientGroup.mk'_surjective C
  let α := NormalElementaryQuotient.representation U q hq (QuotientGroup.ker_mk' C)
  let Y := offenderSubgroup α
  let := offenderSubgroup_normal α
  let A := L.subgroupOf H
  have hmap : (Y.comap q ⊓ centralizer (A : Set H)).map q ≤
      Y ⊓ centralizer (A.map q : Set (H ⧸ C)) :=
    le_inf ((map_mono inf_le_left).trans (map_comap_le q Y))
      ((map_mono inf_le_right).trans (map_centralizer_le_centralizer_image _ q))
  obtain ⟨d,c,hex,hnorm,haxes⟩ := source_a5_original_paired_axes D e hn hout
  refine ⟨d,c,hex,hnorm,?_⟩
  rcases haxes with h | h
  · have he : Y ⊓ centralizer (A.map q : Set (H ⧸ C)) = d.second.map Y.subtype := by
      rw [h]
      exact paired_symmetric_first_residual_centralizer α q hq d c
    exact Or.inl ⟨h,he,hmap.trans_eq he⟩
  · have he : Y ⊓ centralizer (A.map q : Set (H ⧸ C)) = d.first.map Y.subtype := by
      rw [h]
      exact paired_symmetric_second_residual_centralizer α q hq d c
    exact Or.inr ⟨h,he,hmap.trans_eq he⟩

end CFSG.Quasithin.Chapter10
