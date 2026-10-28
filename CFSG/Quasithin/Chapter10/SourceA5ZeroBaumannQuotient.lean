module

public import CFSG.Quasithin.Chapter10.SourceA5ZeroMarkedPair
public import CFSG.Quasithin.Chapter10.SourceA5ZeroCoreBaumann
public import Theory.GroupTheory.QuotientPairDirectProduct

/-!
# The Baumann quotient restricted to the marked pair

The ambient quotient is restricted to the actual Baumann subgroup before its
two coordinate images are assembled.  This records the common quotient map
and its exact kernel; subsequent factor calculations can therefore use the
literal marked product without changing ambient types.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterC ChapterE.ThompsonAction
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false in
theorem source_a5_zero_baumann_quotient
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hout : ¬ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ D.maximalLocal)
    (hz : omegaOneCenterAmbient (T : Subgroup G) ⊓
      centralizer (localOrbit T L : Set G) = ⊥) :
    let H := localJoin T L
    let S := T.subtype (show (T : Subgroup G) ≤ H from le_sup_right)
    let U := D.moduleSubgroup.subgroupOf H
    let _ := (source_parabolic_module_reduced D).normal
    let _ := (source_parabolic_module_reduced D).elementary
    let C := centralizer (U : Set H)
    let q := QuotientGroup.mk' C
    let α := NormalElementaryQuotient.representation U q
      (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
    let Y := offenderSubgroup α
    let _ := offenderSubgroup_normal α
    let R := ChapterB.baumann (S : Subgroup H)
    ∃ d : ChapterB.SourceInduction.SourceTwoFactorCase (α.comp Y.subtype),
      ∃ c : d.MarkedProduct (BinaryPermutation.naturalRepresentation (Fin 5)),
      (c.action.groupEquiv.symm.toMonoidHom.comp
        c.action.groupEquiv.toMonoidHom = MonoidHom.id Y) ∧
      ∃ qR : R →* (Equiv.Perm (Fin 5) × Equiv.Perm (Fin 5)),
        qR.ker = q.ker.subgroupOf R := by
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
  let α := NormalElementaryQuotient.representation U q hq hk
  let Y := offenderSubgroup α
  let _ := offenderSubgroup_normal α
  let R := ChapterB.baumann (S : Subgroup H)
  obtain ⟨t,ht,hne,hcomm,horbit,hsplit,hkA,hkB,hjoint,d,c,hc_id,hex,hN,hop⟩ :=
    source_a5_zero_centralizer_marked_pair_data D e hn hout hz
  obtain ⟨_,a,b,hab⟩ := paired_thompson_baumann_of_symmetric_model S
    (source_a5_minimal_parabolic D e hn) U hU
    (source_local_thompson_not_centralizes D hout) q hq hk d c hex
  let F := ((((ChapterB.Offenders.D 5).map (MulAut.conj a).toMonoidHom).prod
      ((ChapterB.Offenders.D 5).map (MulAut.conj b).toMonoidHom)).map
        (Y.subtype.comp c.action.groupEquiv.symm.toMonoidHom))
  have hcore : q.ker = pCore 2 H := hk.trans
    (source_a5_zero_centralizer_paired_action D e hn hout hz).2
  have hR : R = F.comap q := by
    rw [show F = R.map q from hab.symm]
    simpa [R] using (comap_map_eq_self
      (hcore ▸ source_a5_zero_core_le_baumann D e hn hout hz)).symm
  have hRY : R ≤ Y.comap q := by
    rw [hR]
    exact comap_mono (by
      rintro _ ⟨v,hv,rfl⟩
      exact (c.action.groupEquiv.symm v).property)
  let qR : R →* (Equiv.Perm (Fin 5) × Equiv.Perm (Fin 5)) :=
    c.action.groupEquiv.toMonoidHom.comp
      ((q.comp R.subtype).codRestrict Y (fun r => hRY r.property))
  have hker : qR.ker = q.ker.subgroupOf R := by
    ext r
    change c.action.groupEquiv
        ((q.comp R.subtype).codRestrict Y (fun r => hRY r.property) r) = 1 ↔
      q (r : H) = 1
    constructor
    · intro h
      have hz : ((q.comp R.subtype).codRestrict Y (fun r => hRY r.property) r) = 1 := by
        apply c.action.groupEquiv.injective
        simpa using h
      exact congrArg Y.subtype hz
    · intro h
      have hz : ((q.comp R.subtype).codRestrict Y (fun r => hRY r.property) r) = 1 := by
        apply Subtype.ext
        simpa using h
      rw [hz]
      exact c.action.groupEquiv.map_one
  exact ⟨d,c,by ext y; simp,qR,hker⟩

end CFSG.Quasithin.Chapter10
