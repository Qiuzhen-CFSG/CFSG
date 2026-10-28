module
public import Stellmacher.SectionTen.TenOneSmallMiddleCoreCenter
public import Stellmacher.SectionTen.TenOneSmallSolvableCentralizer
public import Stellmacher.SectionNine.AmbientEdgeSylow

/-!
# Excluding the terminal-center class inside a noncentral middle core

In the small Section Ten case, a point of the middle two-core outside its
center cannot be ambient-conjugate to the terminal-center point if its
full ambient centralizer lies in the mapped middle stabilizer. Conjugacy
is stated for the literal mapped terminal line and the cyclic subgroup of
the chosen embedded point, without replacing the embedding or ambient group.

The terminal edge supplies a full Sylow two-subgroup of H centralized by
the terminal center. An alleged conjugacy puts the conjugate Sylow in the
chosen point's full centralizer. The assumed containment puts this Sylow
in the mapped middle stabilizer, so it contains that stabilizer's normal
two-core. Injectivity then shows that the point centralizes the original
middle core, whose full center is exactly Zmiddle, a contradiction.

Source: Stellmacher (10.1)(a3)(11), printed p.62, the first Wstar case.
The hypothesis only needs membership in the middle core; the source's
Wstar points satisfy it. Source (10) supplies the centralizer containment
under the final solvability contradiction.
-/

namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine Subgroup
universe u
variable {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
  {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
  {embedding : G →* H} {T A B : Subgroup G}

public theorem ten_one_small_point_not_conjugate_terminal_center
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hsmall : Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep)=8)
    (hmodel : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.firstStep)
      (QAt ctx.Γ ctx.criticalPath.firstStep) SL2Two)
    (a : G) (haQ : a∈QAt ctx.Γ middle) (haZ : a∉ZAt ctx.Γ middle)
    (hC : centralizer ({embedding a}:Set H)≤(GAt ctx.Γ middle).map embedding) :
    ¬∃ actor:H, ((ZAt ctx.Γ ctx.criticalPath.a').map embedding).map
      (MulAut.conj actor).toMonoidHom = zpowers (embedding a) := by
  rintro ⟨actor,hactor⟩
  let M := GAt ctx.Γ middle
  let MH := M.map embedding
  let Q := QAt ctx.Γ middle
  let QH := Q.map embedding
  let C := centralizer ({embedding a}:Set H)
  let Zt := (ZAt ctx.Γ ctx.criticalPath.a').map embedding
  have hadj := (sectionTenOpeningGeometry ctx middle hpath).2.2.1
  obtain ⟨PS,hPS⟩ := ambient_edge_stabilizer_is_sylow_two ctx.toAmbientSectionNineContext
    (by rw [ctx.critical_length]; decide) middle ctx.criticalPath.a' hadj
  have hPZ : (PS:Subgroup H)≤centralizer (Zt:Set H) := by
    rw [hPS]
    obtain ⟨mover,_,hmove⟩ := lemma_seven_five_endpoint_alignment
      ctx.sectionSeven ctx.Γ ctx.criticalPath ctx.commutator_eq
    have hh := nine_next_center_centralizes_stabilizer ctx.toLocalContext.toSectionNineLocalContext
      ctx.criticalPath.a' ⟨mover,hmove⟩
    exact (map_mono (inf_le_right.trans hh)).trans (map_centralizer_le_centralizer_image _ _)
  let conjugate : Sylow 2 H := actor • PS
  have hconjC : (conjugate:Subgroup H)≤C := by
    have hh := (map_mono (f:=(MulAut.conj actor).toMonoidHom) hPZ).trans
      (map_centralizer_le_centralizer_image _ _)
    change ((PS:Subgroup H).map (MulAut.conj actor).toMonoidHom)≤
      centralizer (Zt.map (MulAut.conj actor).toMonoidHom:Set H) at hh
    change Zt.map (MulAut.conj actor).toMonoidHom=zpowers (embedding a) at hactor
    rw [hactor,zpowers_eq_closure,centralizer_closure] at hh
    exact hh
  have hconjM : (conjugate:Subgroup H)≤MH := hconjC.trans hC
  let PM : Sylow 2 MH := conjugate.subtype hconjM
  let e : M ≃* MH := M.equivMapOfInjective embedding ctx.embedding_injective
  have hcomp : MH.subtype.comp e.toMonoidHom=embedding.comp M.subtype := rfl
  have hQcore : QH=(pCore 2 MH).map MH.subtype := by
    have hh := congrArg (fun K : Subgroup MH => K.map MH.subtype) (pCore_map_iso 2 e)
    rw [map_map,hcomp,←map_map] at hh
    have hlocal : (pCore 2 M).map M.subtype=Q := (ctx.Γ.twoCoreAt_def middle).symm
    rw [hlocal] at hh
    exact hh
  have hQconj : QH≤(conjugate:Subgroup H) := by
    have hh := map_mono (f:=MH.subtype)
      ((pCore_isPGroup (p:=2) (G:=MH)).le_sylow_of_normal PM)
    rw [←hQcore] at hh
    change QH≤((conjugate:Subgroup H).subgroupOf MH).map MH.subtype at hh
    rw [map_subgroupOf_eq_of_le hconjM] at hh
    exact hh
  have haCenter : (⟨a,haQ⟩:Q)∈center Q := by
    rw [mem_center_iff]
    intro q
    apply Subtype.ext
    apply ctx.embedding_injective
    have hh := mem_centralizer_singleton_iff.mp
      (hconjC (hQconj (mem_map_of_mem embedding q.property)))
    simpa only [Subgroup.coe_mul,map_mul] using hh
  have haAmbient : a∈CenterAmbient Q := mem_map_of_mem Q.subtype haCenter
  rw [show CenterAmbient Q=ZAt ctx.Γ middle from ten_one_small_middle_core_center
    ctx middle hpath hsmall hmodel] at haAmbient
  exact haZ haAmbient

end Stellmacher.SectionTen