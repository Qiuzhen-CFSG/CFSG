module
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.Basic
/-!
# Irreducibility from a marked block module

Surjective coordinates send intermediate normal subgroups of U(L) to
invariant subgroups of the model. The actual fixed subgroup is precisely
the coordinate kernel, so model irreducibility is the source normal-subgroup
interval, including its strict lower endpoint.

Source: Aschbacher–Smith C.1.7, printed p.123.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC
variable {L A V : Type*} [Group L] [Group A] [Group V] [Nontrivial V]

theorem BlockModuleModel.irreducible (ρ:A→*MulAut V) (m:BlockModuleModel L ρ)
    (hi:∀W:Subgroup V,(∀a v,v∈W→ρ a v∈W)→W=⊥∨W=⊤) : BlockModuleIrreducible L := by
  let U:=blockU L
  let Z:=blockFixed L
  let q:U→*V:=m.moduleIso.toMonoidHom.comp (QuotientGroup.mk' Z)
  have hq:Function.Surjective q:=m.moduleIso.surjective.comp (QuotientGroup.mk'_surjective Z)
  have hk:q.ker=Z := by
    ext u
    change m.moduleIso (QuotientGroup.mk' Z u)=1 ↔ u∈Z
    rw [←m.moduleIso.map_one,m.moduleIso.injective.eq_iff]
    exact QuotientGroup.eq_one_iff u
  have hZne:Z≠⊤ := by
    intro hz
    obtain ⟨v,hv⟩:=exists_ne (1:V)
    obtain ⟨u,rfl⟩:=hq v
    exact hv (MonoidHom.mem_ker.mp (by rw [hk,hz];trivial))
  refine ⟨lt_of_le_of_ne inf_le_left ?_,?_⟩
  · intro hh
    apply hZne
    apply top_unique
    intro u _
    exact ((show U≤U⊓center L from hh.ge) u.property).2
  · intro N hN hlow hhigh
    let := hN
    let J:=N.subgroupOf U
    have hZJ:Z≤J:=fun u hu=>hlow ⟨u.property,hu⟩
    have hinv:∀a v,v∈J.map q→ρ a v∈J.map q := by
      intro a v hv
      obtain ⟨u,hu,rfl⟩:=hv
      obtain ⟨l,hl⟩:=m.quotientIso.surjective a
      obtain ⟨g,rfl⟩:=QuotientGroup.mk'_surjective (pCore 2 L) l
      refine ⟨blockConjugate L g u,?_,?_⟩
      · exact hN.conj_mem u hu g
      · exact (m.intertwining g u).trans (by rw [hl];rfl)
    have hpull:(J.map q).comap q=J := by rw [comap_map_eq,hk,sup_eq_left.mpr hZJ]
    rcases hi (J.map q) hinv with hb|ht
    · left
      have hJ:J=Z:=by rw [hb,MonoidHom.comap_bot,hk] at hpull;exact hpull.symm
      have hh:=congrArg (map U.subtype) hJ
      rw [map_subgroupOf_eq_of_le hhigh,blockFixed_map] at hh
      exact hh
    · right
      have hJ:J=⊤:=by rw [ht,comap_top] at hpull;exact hpull.symm
      have hh:=congrArg (map U.subtype) hJ
      change (N.subgroupOf U).map U.subtype=(⊤:Subgroup U).map U.subtype at hh
      rw [map_subgroupOf_eq_of_le (show N≤U from hhigh),←MonoidHom.range_eq_map,range_subtype] at hh
      exact hh
end CFSG.Quasithin.ChapterC
