module
public import CFSG.Quasithin.Chapter10.SourceA5ZeroMarkedPair
public import CFSG.Quasithin.Chapter10.SourceA5OriginalPairedAxes

public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterC ChapterE.ThompsonAction
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

set_option backward.isDefEq.respectTransparency false in
theorem source_a5_zero_centralizer_marked_pair_exchange
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hout : ¬ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ D.maximalLocal)
    (hz : omegaOneCenterAmbient (T : Subgroup G) ⊓
      centralizer (localOrbit T L : Set G) = ⊥) :
    ∃ t : localJoin T L, (t : G) ∈ (T : Subgroup G) ∧
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
      let A := L.subgroupOf H
      ∃ d : ChapterB.SourceInduction.SourceTwoFactorCase (α.comp Y.subtype),
        ∃ c : d.MarkedProduct (BinaryPermutation.naturalRepresentation (Fin 5)),
          (c.action.groupEquiv.symm.toMonoidHom.comp
              c.action.groupEquiv.toMonoidHom = MonoidHom.id Y) ∧
          (letI := offenderSubgroup_normal α
           (∃ u : S.mapSurjective (QuotientGroup.mk'_surjective C),
             d.first.map (MulAut.conjNormal (u : H ⧸ C)).toMonoidHom = d.second ∧
             d.second.map (MulAut.conjNormal (u : H ⧸ C)).toMonoidHom = d.first)) ∧
          Y.comap q ≤ normalizer (A : Set H) ∧
          ((A.map q = (factorResidual q Y d.first).map q ∧
            (A.map (MulAut.conj t).toMonoidHom).map q =
              (factorResidual q Y d.second).map q) ∨
           (A.map q = (factorResidual q Y d.second).map q ∧
            (A.map (MulAut.conj t).toMonoidHom).map q =
              (factorResidual q Y d.first).map q)) := by
  let H := localJoin T L
  let S := T.subtype (show (T : Subgroup G) ≤ H from le_sup_right)
  let A := L.subgroupOf H
  let hU := source_parabolic_module_reduced D
  let := hU.normal
  let := hU.elementary
  let U := D.moduleSubgroup.subgroupOf H
  let C := centralizer (U : Set H)
  let q := QuotientGroup.mk' C
  let α := NormalElementaryQuotient.representation U q
    (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
  let Y := offenderSubgroup α
  let := offenderSubgroup_normal α
  obtain ⟨t,ht,hne,hb,hab,hpair,hsplit,hkA,hkB⟩ :=
    source_a5_zero_centralizer_pair_centralizers D e hn hout hz
  obtain ⟨d,c,hex,hnorm,him⟩ := source_a5_original_paired_axes D e hn hout
  have hop := paired_symmetric_commuting_conjugate_opposite
    U hU q (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
    d c A t hb (by simpa [A] using him)
  exact ⟨t,ht,d,c,by ext y; simp,hex,hnorm,hop⟩

end CFSG.Quasithin.Chapter10
