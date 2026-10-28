module
public import CFSG.Quasithin.Chapter10.SourceA5ZeroCoreBaumann
public import CFSG.Quasithin.Chapter10.SourceA5ZeroCentralizerAxes

/-!
# The original zero-center Baumann subgroup is a marked full preimage

The complete local two-core lies in the Baumann subgroup. Its genuine
paired quotient marking therefore identifies the subgroup itself with the
full preimage of the two prescribed transposition four-groups. The same
marking retains normalization of the original alternating block.
Source: Aschbacher–Smith10.2.1, p.743.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterE.ThompsonAction
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
set_option backward.isDefEq.respectTransparency false

theorem source_a5_zero_baumann_preimage
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hout : ¬ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ D.maximalLocal)
    (hz : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (localOrbit T L : Set G) = ⊥) :
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
    ∃ d : ChapterB.SourceInduction.SourceTwoFactorCase (α.comp Y.subtype),
      ∃ c : d.MarkedProduct (BinaryPermutation.naturalRepresentation (Fin 5)),
        Y.comap q ≤ normalizer (L.subgroupOf H : Set H) ∧
        (∃ t : S.mapSurjective (QuotientGroup.mk'_surjective C),
          d.first.map (MulAut.conjNormal (t : H ⧸ C)).toMonoidHom = d.second ∧
          d.second.map (MulAut.conjNormal (t : H ⧸ C)).toMonoidHom = d.first) ∧
        ∃ a b : Equiv.Perm (Fin 5), ChapterB.baumann (S : Subgroup H) =
          ((((ChapterB.Offenders.D 5).map (MulAut.conj a).toMonoidHom).prod
            ((ChapterB.Offenders.D 5).map (MulAut.conj b).toMonoidHom)).map
              (Y.subtype.comp c.action.groupEquiv.symm.toMonoidHom)).comap q := by
  let H := localJoin T L
  let S := T.subtype (show (T : Subgroup G) ≤ H from le_sup_right)
  let U := D.moduleSubgroup.subgroupOf H
  have hU := source_parabolic_module_reduced D
  let := hU.normal
  let := hU.elementary
  let C := centralizer (U : Set H)
  let q := QuotientGroup.mk' C
  have hq := QuotientGroup.mk'_surjective C
  have hk : q.ker = centralizer (U : Set H) := QuotientGroup.ker_mk' C
  have hcore : q.ker = pCore 2 H := hk.trans
    (source_a5_zero_centralizer_paired_action D e hn hout hz).2
  obtain ⟨d,c,hex,hN,_⟩ := source_a5_zero_original_centralizer_axes D e hn hout hz
  obtain ⟨_,a,b,hab⟩ := paired_thompson_baumann_of_symmetric_model S
    (source_a5_minimal_parabolic D e hn) U hU (source_local_thompson_not_centralizes D hout)
    q hq hk d c hex
  refine ⟨d,c,hN,hex,a,b,?_⟩
  rw [←hab,comap_map_eq_self (hcore ▸ source_a5_zero_core_le_baumann D e hn hout hz)]
end CFSG.Quasithin.Chapter10
