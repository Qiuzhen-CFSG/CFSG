module

public import CFSG.Quasithin.Chapter10.SourceA5OriginalPairedOpposite
public import CFSG.Quasithin.Chapter10.SourceA5ZeroCentralizerCore
public import CFSG.Quasithin.Chapter10.SourceA5ZeroCentralizerAxes
public import CFSG.Quasithin.ChapterC.Section01.BlockCohomology.AlternatingFivePairCentralizers

/-!
# One witness for the zero-center paired A₅ geometry

The core construction and the marked quotient construction must use the same
Sylow conjugator.  This extension packages that common witness: the literal
core split, both centralizer kernels, the joint-centralizer vanishing, and the
opposite marked quotient axes are all obtained from the conjugator selected by
the original zero-center core theorem.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterC ChapterE.ThompsonAction
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

set_option backward.isDefEq.respectTransparency false in
theorem source_a5_zero_centralizer_marked_pair
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hout : ¬ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ D.maximalLocal)
    (hz : omegaOneCenterAmbient (T : Subgroup G) ⊓
      centralizer (localOrbit T L : Set G) = ⊥) :
    ∃ t : localJoin T L, (t : G) ∈ (T : Subgroup G) ∧
      let A := L.subgroupOf (localJoin T L)
      let B := A.map (MulAut.conj t).toMonoidHom
      A ≠ B ∧ ⁅A,B⁆ = ⊥ ∧
        (A ⊔ B).map (localJoin T L).subtype = localOrbit T L ∧
        pCore 2 (localJoin T L) = (blockU A).map A.subtype ⊔ (blockU B).map B.subtype ∧
        pCore 2 (localJoin T L) ⊓ centralizer (B : Set (localJoin T L)) =
          (blockU A).map A.subtype ∧
        pCore 2 (localJoin T L) ⊓ centralizer (A : Set (localJoin T L)) =
          (blockU B).map B.subtype ∧
        centralizer ((A ⊔ B : Subgroup (localJoin T L)) : Set (localJoin T L)) = ⊥ ∧
        SourceOriginalPairedOpposite D t := by
  let H := localJoin T L
  let A := L.subgroupOf H
  have hLH : L ≤ H := (le_componentOrbit L T).trans le_sup_left
  obtain ⟨ha,haa,_⟩ := source_a5_original_block_of_baumann_not_controlled D e hn hout
  obtain ⟨t,ht,hne,hb,hab,hpair,hsplit,hE⟩ :=
    source_a5_zero_centralizer_pair_core D e hn hout hz
  let B := A.map (MulAut.conj t).toMonoidHom
  have hqA : IsQuasisimple (A ⧸ pCore 2 A) := by
    let := D.quasisimple
    exact IsQuasisimple.of_mulEquiv
      (QuotientGroup.congr _ _ (subgroupOfEquivOfLe hLH).symm
        (pCore_map_iso 2 (subgroupOfEquivOfLe hLH).symm))
  have hc : ⁅A,B⁆ = ⊥ := ha.commutator_eq_bot_of_quasisimple_quotient hb hqA hne
  have hu : D.moduleSubgroup.subgroupOf H = pCore 2 H := by
    apply Subgroup.map_injective H.subtype_injective
    rw [map_subgroupOf_eq_of_le (D.module_le_core.trans (pCoreIn_le 2 H))]
    exact source_a5_zero_centralizer_module_eq_core D e hn hout hz
  have hself : centralizer (pCore 2 H : Set H) ≤ pCore 2 H := by
    rw [←hu]
    exact (source_a5_zero_centralizer_local_module_centralizer D e hn hout hz).le
  obtain ⟨hfirst,hsecond⟩ := alternatingFive_pair_core_centralizers A B haa hab hc hsplit
  have hjoint := alternatingFive_pair_centralizer_eq_bot A B haa hab hc hsplit hself
  have hmark := source_a5_original_paired_opposite D e hn hout t hc
  exact ⟨t,ht,hne,hc,hpair,hsplit,hfirst,hsecond,hjoint,hmark⟩

/- The same package, retaining the marked quotient witness and its exchange
   element.  This is the form needed by the Baumann preimage calculation. -/
set_option backward.isDefEq.respectTransparency false in
theorem source_a5_zero_centralizer_marked_pair_data
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
            ((A.map q = (factorResidual q Y d.first).map q ∧
                B.map q = (factorResidual q Y d.second).map q) ∨
             (A.map q = (factorResidual q Y d.second).map q ∧
                B.map q = (factorResidual q Y d.first).map q)) := by
  let H := localJoin T L
  let U := D.moduleSubgroup.subgroupOf H
  have hU := source_parabolic_module_reduced D
  let := hU.normal
  let := hU.elementary
  let C := centralizer (U : Set H)
  let q := QuotientGroup.mk' C
  have hq := QuotientGroup.mk'_surjective C
  have hk : q.ker = centralizer (U : Set H) := QuotientGroup.ker_mk' C
  let α := NormalElementaryQuotient.representation U q hq hk
  let Y := offenderSubgroup α
  let A := L.subgroupOf H
  obtain ⟨ha,haa,_⟩ := source_a5_original_block_of_baumann_not_controlled D e hn hout
  obtain ⟨d,c,hex,hN,haxes⟩ := source_a5_original_paired_axes D e hn hout
  obtain ⟨t,ht,hne,hb,hab,hpair,hsplit,hE⟩ :=
    source_a5_zero_centralizer_pair_core D e hn hout hz
  have hLH : L ≤ H := (le_componentOrbit L T).trans le_sup_left
  have hqA : IsQuasisimple (A ⧸ pCore 2 A) := by
    let := D.quasisimple
    exact IsQuasisimple.of_mulEquiv
      (QuotientGroup.congr _ _ (subgroupOfEquivOfLe hLH).symm
        (pCore_map_iso 2 (subgroupOfEquivOfLe hLH).symm))
  let B := A.map (MulAut.conj t).toMonoidHom
  have hc : ⁅A,B⁆ = ⊥ :=
    ha.commutator_eq_bot_of_quasisimple_quotient hb hqA hne
  have hu : U = pCore 2 H := by
    apply Subgroup.map_injective H.subtype_injective
    rw [map_subgroupOf_eq_of_le (D.module_le_core.trans (pCoreIn_le 2 H))]
    exact source_a5_zero_centralizer_module_eq_core D e hn hout hz
  have hself : centralizer (pCore 2 H : Set H) ≤ pCore 2 H := by
    rw [←hu]
    exact (source_a5_zero_centralizer_local_module_centralizer D e hn hout hz).le
  obtain ⟨hfirst,hsecond⟩ := alternatingFive_pair_core_centralizers A B haa hab hc hsplit
  have hjoint := alternatingFive_pair_centralizer_eq_bot A B
    haa hab hc hsplit hself
  have hop := paired_symmetric_commuting_conjugate_opposite U hU q hq
    hk d c A t hc haxes
  exact ⟨t,ht,hne,hc,hpair,hsplit,hfirst,hsecond,hjoint,
    d,c,by ext y; simp,hex,hN,hop⟩

/- The exact-axis variant keeps the corrected centralizer image from the
   source axis theorem together with the common core and quotient witness. -/
set_option backward.isDefEq.respectTransparency false in
theorem source_a5_zero_centralizer_marked_pair_data_axes
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
            ((A.map q = (factorResidual q Y d.first).map q ∧
                (Y.comap q ⊓ centralizer (A : Set H)).map q = d.second.map Y.subtype) ∨
             (A.map q = (factorResidual q Y d.second).map q ∧
                (Y.comap q ⊓ centralizer (A : Set H)).map q = d.first.map Y.subtype)) ∧
            ((A.map q = (factorResidual q Y d.first).map q ∧
                B.map q = (factorResidual q Y d.second).map q) ∨
             (A.map q = (factorResidual q Y d.second).map q ∧
                B.map q = (factorResidual q Y d.first).map q)) := by
  let H := localJoin T L
  let U := D.moduleSubgroup.subgroupOf H
  have hU := source_parabolic_module_reduced D
  let := hU.normal
  let := hU.elementary
  let C := centralizer (U : Set H)
  let q := QuotientGroup.mk' C
  have hq := QuotientGroup.mk'_surjective C
  have hk : q.ker = centralizer (U : Set H) := QuotientGroup.ker_mk' C
  let α := NormalElementaryQuotient.representation U q hq hk
  let Y := offenderSubgroup α
  let A := L.subgroupOf H
  obtain ⟨ha,haa,_⟩ := source_a5_original_block_of_baumann_not_controlled D e hn hout
  obtain ⟨d,c,hex,hN,haxes⟩ := source_a5_zero_original_centralizer_axes D e hn hout hz
  obtain ⟨t,ht,hne,hb,hab,hpair,hsplit,hE⟩ :=
    source_a5_zero_centralizer_pair_core D e hn hout hz
  have hLH : L ≤ H := (le_componentOrbit L T).trans le_sup_left
  have hqA : IsQuasisimple (A ⧸ pCore 2 A) := by
    let := D.quasisimple
    exact IsQuasisimple.of_mulEquiv
      (QuotientGroup.congr _ _ (subgroupOfEquivOfLe hLH).symm
        (pCore_map_iso 2 (subgroupOfEquivOfLe hLH).symm))
  let B := A.map (MulAut.conj t).toMonoidHom
  have hc : ⁅A,B⁆ = ⊥ :=
    ha.commutator_eq_bot_of_quasisimple_quotient hb hqA hne
  have hu : U = pCore 2 H := by
    apply Subgroup.map_injective H.subtype_injective
    rw [map_subgroupOf_eq_of_le (D.module_le_core.trans (pCoreIn_le 2 H))]
    exact source_a5_zero_centralizer_module_eq_core D e hn hout hz
  have hself : centralizer (pCore 2 H : Set H) ≤ pCore 2 H := by
    rw [←hu]
    exact (source_a5_zero_centralizer_local_module_centralizer D e hn hout hz).le
  obtain ⟨hfirst,hsecond⟩ := alternatingFive_pair_core_centralizers A B haa hab hc hsplit
  have hjoint := alternatingFive_pair_centralizer_eq_bot A B haa hab hc hsplit hself
  have him : A.map q = (factorResidual q Y d.first).map q ∨
      A.map q = (factorResidual q Y d.second).map q :=
    haxes.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)
  have hop := paired_symmetric_commuting_conjugate_opposite U hU q hq
    hk d c A t hc him
  exact ⟨t,ht,hne,hc,hpair,hsplit,hfirst,hsecond,hjoint,
    d,c,by ext y; simp,hex,hN,haxes,hop⟩

end CFSG.Quasithin.Chapter10
