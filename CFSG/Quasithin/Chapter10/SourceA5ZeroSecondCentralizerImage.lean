module

public import CFSG.Quasithin.Chapter10.SourceA5ZeroMarkedPair
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.PairCentralizerImagesConjugate

/-!
# Both actual zero-center centralizer images

The original block and its chosen Sylow conjugate have the two opposite
full symmetric-five centralizer images under one marked quotient. The
first exact image comes from the cocycle correction, and the second from
conjugating that equality. The core split and both kernel identities are
retained for the direct-product assembly.

Source: Aschbacher–Smith 10.2.1, pp.742–743.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterC ChapterE.ThompsonAction
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

set_option backward.isDefEq.respectTransparency false in
theorem source_a5_zero_centralizer_marked_pair_both_axes
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hout : ¬ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ D.maximalLocal)
    (hz : omegaOneCenterAmbient (T : Subgroup G) ⊓
      centralizer (localOrbit T L : Set G) = ⊥) :
    let H := localJoin T L
    let U := D.moduleSubgroup.subgroupOf H
    letI := (source_parabolic_module_reduced D).normal
    letI := (source_parabolic_module_reduced D).elementary
    let C := centralizer (U : Set H)
    let q := QuotientGroup.mk' C
    let α := NormalElementaryQuotient.representation U q
      (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
    let Y := offenderSubgroup α
    letI := offenderSubgroup_normal α
    ∃ t : H, (t : G) ∈ (T : Subgroup G) ∧
      let A := L.subgroupOf H
      let B := A.map (MulAut.conj t).toMonoidHom
      A ≠ B ∧ ⁅A,B⁆ = ⊥ ∧
        (A ⊔ B).map H.subtype = localOrbit T L ∧
        pCore 2 H = (blockU A).map A.subtype ⊔ (blockU B).map B.subtype ∧
        pCore 2 H ⊓ centralizer (B : Set H) = (blockU A).map A.subtype ∧
        pCore 2 H ⊓ centralizer (A : Set H) = (blockU B).map B.subtype ∧
        centralizer ((A ⊔ B : Subgroup H) : Set H) = ⊥ ∧
        ∃ d : ChapterB.SourceInduction.SourceTwoFactorCase (α.comp Y.subtype),
          ∃ c : d.MarkedProduct (BinaryPermutation.naturalRepresentation (Fin 5)),
            (c.action.groupEquiv.symm.toMonoidHom.comp c.action.groupEquiv.toMonoidHom =
              MonoidHom.id Y) ∧
            (∃ s : (T.subtype (show (T : Subgroup G) ≤ H from le_sup_right)).mapSurjective
                (QuotientGroup.mk'_surjective C),
              d.first.map (MulAut.conjNormal (s : H ⧸ C)).toMonoidHom = d.second ∧
              d.second.map (MulAut.conjNormal (s : H ⧸ C)).toMonoidHom = d.first) ∧
            Y.comap q ≤ normalizer (A : Set H) ∧
            (((Y.comap q ⊓ centralizer (A : Set H)).map q = d.second.map Y.subtype ∧
                (Y.comap q ⊓ centralizer (B : Set H)).map q = d.first.map Y.subtype) ∨
             ((Y.comap q ⊓ centralizer (A : Set H)).map q = d.first.map Y.subtype ∧
                (Y.comap q ⊓ centralizer (B : Set H)).map q = d.second.map Y.subtype)) := by
  let H := localJoin T L
  let U := D.moduleSubgroup.subgroupOf H
  let := (source_parabolic_module_reduced D).normal
  let := (source_parabolic_module_reduced D).elementary
  let C := centralizer (U : Set H)
  let q := QuotientGroup.mk' C
  let α := NormalElementaryQuotient.representation U q
    (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
  let Y := offenderSubgroup α
  obtain ⟨t,ht,hne,hcomm,horbit,hsplit,hkA,hkB,hjoint,d,c,hcid,hex,hN,haxes,hop⟩ :=
    source_a5_zero_centralizer_marked_pair_data_axes D e hn hout hz
  exact ⟨t,ht,hne,hcomm,horbit,hsplit,hkA,hkB,hjoint,d,c,hcid,hex,hN,
    paired_symmetric_conjugate_centralizer_images α q
      (QuotientGroup.mk'_surjective C) d c (L.subgroupOf H) t haxes hop⟩

end CFSG.Quasithin.Chapter10
