module
public import CFSG.Quasithin.Chapter10.SourceA5ZeroCentralizerAxes
public import CFSG.Quasithin.Chapter10.SourceA5OriginalPairedOpposite
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.PairedFiveNaturalKernels
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.PairedFiveFactorRecognition
public import CFSG.Quasithin.Chapter10.SourceA5ZeroCoreBaumann
public import Theory.GroupTheory.RestrictedImageSection

/-!
# The actual original Baumann centralizer is a dihedral square

In the zero-center branch the Baumann subgroup is the full preimage of
its marked pair of transposition four-groups. The opposite original block
layer is exactly the natural kernel of the factor centralizer's S₅ map.
Its already proved faithful natural-kernel section makes the actual Baumann
intersection the preimage of the appropriate four-group. Recognition gives
two dihedral factors of order eight, with all source premises discharged.

This concerns C_Baum(T)(L), not the full Sylow subgroup of 2⁴:S₅.
Source: Aschbacher–Smith10.2.1,p.743.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterC ChapterE.ThompsonAction
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
set_option backward.isDefEq.respectTransparency false

theorem source_a5_zero_baumann_factor_dihedral_square
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hout : ¬ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ D.maximalLocal)
    (hz : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (localOrbit T L : Set G) = ⊥) :
    let H := localJoin T L
    let S := T.subtype (show (T : Subgroup G) ≤ H from le_sup_right)
    Nonempty ((ChapterB.baumann (S : Subgroup H) ⊓ centralizer
      (L.subgroupOf H : Set H) : Subgroup H) ≃* DihedralGroup 4 × DihedralGroup 4) := by
  let H := localJoin T L
  let S := T.subtype (show (T : Subgroup G) ≤ H from le_sup_right)
  let R := ChapterB.baumann (S : Subgroup H)
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
  let P := Y.comap q ⊓ centralizer (A : Set H)
  obtain ⟨d,c,hex,hN,haxis⟩ := source_a5_zero_original_centralizer_axes D e hn hout hz
  obtain ⟨_,a,b,hab⟩ := paired_thompson_baumann_of_symmetric_model S
    (source_a5_minimal_parabolic D e hn) U hU (source_local_thompson_not_centralizes D hout)
    q hq hk d c hex
  have hcore : q.ker = pCore 2 H := hk.trans
    (source_a5_zero_centralizer_paired_action D e hn hout hz).2
  have hR : R = ((((ChapterB.Offenders.D 5).map (MulAut.conj a).toMonoidHom).prod
      ((ChapterB.Offenders.D 5).map (MulAut.conj b).toMonoidHom)).map
        (Y.subtype.comp c.action.groupEquiv.symm.toMonoidHom)).comap q := by
    rw [←hab,comap_map_eq_self (hcore ▸ source_a5_zero_core_le_baumann D e hn hout hz)]
  have hRY : R ≤ Y.comap q := by
    rw [hR]
    apply comap_mono
    rintro _ ⟨v,_,rfl⟩
    exact (c.action.groupEquiv.symm v).property
  have hRP : R ⊓ P = R ⊓ centralizer (A : Set H) := by
    apply le_antisymm
    · exact le_inf inf_le_left (inf_le_right.trans inf_le_right)
    · exact le_inf inf_le_left (le_inf (inf_le_left.trans hRY) inf_le_right)
  obtain ⟨t,ht,hne,hcomm,horbit,hsplit,hkA,hkB,hjoint⟩ :=
    source_a5_zero_centralizer_pair_centralizers D e hn hout hz
  let B := A.map (MulAut.conj t).toMonoidHom
  have hblockB : IsBlock B :=
    (source_a5_original_block_of_baumann_not_controlled D e hn hout).1.map_equiv (MulAut.conj t)
  have hu : U = pCore 2 H := by
    apply Subgroup.map_injective H.subtype_injective
    rw [map_subgroupOf_eq_of_le (D.module_le_core.trans (pCoreIn_le 2 H))]
    exact source_a5_zero_centralizer_module_eq_core D e hn hout hz
  have hku : q.ker = U := hk.trans
    (source_a5_zero_centralizer_local_module_centralizer D e hn hout hz)
  have hK : q.ker ⊓ P = ⁅U,B⁆ := by
    change q.ker ⊓ (Y.comap q ⊓ centralizer (A : Set H)) = _
    rw [←inf_assoc,inf_eq_left.mpr (ker_le_comap q Y),hku,hu,hblockB.ambient_core_commutator]
    exact hkB
  have him : A.map q = (factorResidual q Y d.first).map q ∨
      A.map q = (factorResidual q Y d.second).map q :=
    haxis.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)
  have hop := paired_symmetric_commuting_conjugate_opposite U hU q hq hk d c A t hcomm him
  have hm (F : Subgroup H) (he : B.map q = F.map q) : (⁅U,B⁆ : Subgroup H) = ⁅U,F⁆ := by
    have he' : NormalElementaryQuotient.commutatorSpace U B =
        NormalElementaryQuotient.commutatorSpace U F := by
      rw [NormalElementaryQuotient.commutatorSpace_eq U q hq hk,
        NormalElementaryQuotient.commutatorSpace_eq U q hq hk,he]
    apply le_antisymm
    · intro x hx
      have hv : Additive.ofMul (⟨x,(commutator_le_left U B) hx⟩ : U) ∈
          NormalElementaryQuotient.commutatorSpace U B := hx
      rw [he'] at hv
      exact hv
    · intro x hx
      have hv : Additive.ofMul (⟨x,(commutator_le_left U F) hx⟩ : U) ∈
          NormalElementaryQuotient.commutatorSpace U F := hx
      rw [←he'] at hv
      exact hv
  rcases hop with ⟨ha,hb⟩ | ⟨ha,hb⟩
  · have hP : P.map q = d.second.map Y.subtype := by
      rcases haxis with h | h
      · exact h.2
      · have hc := paired_symmetric_first_residual_centralizer α q hq d c
        have hc' := paired_symmetric_second_residual_centralizer α q hq d c
        rw [←ha] at hc
        rw [←h.1] at hc'
        exact h.2.trans (hc'.symm.trans hc)
    obtain ⟨f,hf,hfk,hfc,ek,he,σ,hσ⟩ := paired_second_axis_natural_quotient U q hq hk d c P hP (hK.trans (hm _ hb))
    have hp : P.map q = ((⊥ : Subgroup (Equiv.Perm (Fin 5))).prod ⊤).map
        (Y.subtype.comp c.action.groupEquiv.symm.toMonoidHom) := by rw [hP,←c.second_eq,map_map]
    have hd := marked_second_baumann_factor q Y c.action.groupEquiv P R a b hp hR f hf hfc ek he
    rw [hRP] at hd
    exact hd
  · have hP : P.map q = d.first.map Y.subtype := by
      rcases haxis with h | h
      · have hc := paired_symmetric_first_residual_centralizer α q hq d c
        have hc' := paired_symmetric_second_residual_centralizer α q hq d c
        rw [←h.1] at hc
        rw [←ha] at hc'
        exact h.2.trans (hc.symm.trans hc')
      · exact h.2
    obtain ⟨f,hf,hfk,hfc,ek,he,σ,hσ⟩ := paired_first_axis_natural_quotient U q hq hk d c P hP (hK.trans (hm _ hb))
    have hp : P.map q = ((⊤ : Subgroup (Equiv.Perm (Fin 5))).prod ⊥).map
        (Y.subtype.comp c.action.groupEquiv.symm.toMonoidHom) := by rw [hP,←c.first_eq,map_map]
    have hd := marked_first_baumann_factor q Y c.action.groupEquiv P R a b hp hR f hf hfc ek he
    rw [hRP] at hd
    exact hd
end CFSG.Quasithin.Chapter10
