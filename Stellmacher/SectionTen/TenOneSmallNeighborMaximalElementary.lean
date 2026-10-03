module
public import Stellmacher.SectionTen.TenOneSmallElementaryEscapeBound
public import Stellmacher.SectionTen.TenOneSmallNeighborhoodCard

/-!
# Maximal elementary neighbor modules in the small middle core

In the actual small Section Ten case, every neighbor module is a maximal
elementary abelian subgroup of the middle two-core. The theorem retains
any supplied neighbor and any actual ambient elementary extension X.

Local transitivity gives the neighbor module order eight. Such a module
cannot lie in the middle normal subgroup Wstar: all its conjugate neighbor
modules would then lie there, so their order-thirty-two generated
neighborhood would lie in a subgroup of order eight or sixteen. Every
elementary extension of the neighbor module therefore escapes Wstar.
The proved escaping-elementary-subgroup bound limits its order to eight,
forcing equality with the neighbor module.

Source: Stellmacher (10.1)(a3), printed p.61, the maximal elementary
terminal-module assertion in the uniqueness paragraph preceding (7).
This explicit native consequence is also used in the terminal-core
centralizer calculation of source (11), with no maximality assumption
added to that later proof.
-/

namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine Subgroup
universe u
variable {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
  {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
  {embedding : G →* H} {T A B : Subgroup G}

public theorem ten_one_small_neighbor_module_maximal_elementary
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hsmall : Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep)=8)
    (hmodel : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.firstStep)
      (QAt ctx.Γ ctx.criticalPath.firstStep) SL2Two)
    (neighbor : ctx.Γ.Vertex) (hadj : ctx.Γ.adjacent middle neighbor)
    (X : Subgroup G) [IsElementaryAbelian 2 X]
    (hVX : VAt ctx.Γ neighbor≤X) (hXQ : X≤QAt ctx.Γ middle) :
    X=VAt ctx.Γ neighbor := by
  let Q := QAt ctx.Γ middle
  let M := GAt ctx.Γ middle
  let W0 := NeighborhoodQIntersection ctx.Γ (Neighborhood ctx.Γ middle) ⊓
    GeneratedNeighborhoodV ctx.Γ middle
  let Wstar := Q ⊓ centralizer (W0:Set G)
  have hp := ten_one_small_centralizer_elementary ctx middle hpath hsmall hmodel
  have hMW : M≤normalizer (Wstar:Set G) := hp.1
  have hVcard : Nat.card (VAt ctx.Γ neighbor)=8 := by
    obtain ⟨_,hfirst,_,_⟩ := sectionTenOpeningGeometry ctx middle hpath
    obtain ⟨actor,hactor⟩ := (lemma_seven_one ctx.sectionSeven ctx.Γ).local_transitivity middle
      ((mem_neighborhood_iff_adjacent ctx.Γ).mpr hfirst)
      ((mem_neighborhood_iff_adjacent ctx.Γ).mpr hadj)
    change Nat.card (v ctx.Γ neighbor)=8
    rw [←hactor,v_act,card_map_of_injective (MulAut.conj (actor:G)⁻¹).injective]
    exact hsmall
  have hnot : ¬ VAt ctx.Γ neighbor≤Wstar := by
    intro hVW
    have hwhole : GeneratedNeighborhoodV ctx.Γ middle≤Wstar := by
      apply sSup_le
      rintro K ⟨vertex,hvertex,rfl⟩
      obtain ⟨actor,hactor⟩ := (lemma_seven_one ctx.sectionSeven ctx.Γ).local_transitivity middle
        ((mem_neighborhood_iff_adjacent ctx.Γ).mpr hadj) hvertex
      have hWmap : Wstar.map (MulAut.conj (actor:G)⁻¹).toMonoidHom=Wstar :=
        mem_normalizer_iff_map_conj_eq.mp (hMW (M.inv_mem actor.property))
      have hmap := map_mono (f:=(MulAut.conj (actor:G)⁻¹).toMonoidHom) hVW
      rw [hWmap] at hmap
      change v ctx.Γ vertex≤Wstar
      rw [←hactor,v_act]
      exact hmap
    have hc := card_le_of_le hwhole
    rw [ten_one_small_neighborhood_card ctx middle hpath hsmall] at hc
    have hs := hp.2.2.1
    change Nat.card Wstar=8 ∨ Nat.card Wstar=16 at hs
    omega
  let XQ := X.subgroupOf Q
  let _ : IsElementaryAbelian 2 XQ := IsElementaryAbelian.subgroupOf hXQ
  have hescape : ¬ XQ≤Wstar.subgroupOf Q := by
    intro hh
    apply hnot
    intro x hx
    exact hh (show (⟨x,hXQ (hVX hx)⟩:Q)∈XQ from hVX hx)
  have hbound := ten_one_small_elementary_escape_card_bound ctx middle hpath hsmall hmodel
    XQ hescape
  change Nat.card XQ≤8 at hbound
  rw [Nat.card_congr (subgroupOfEquivOfLe hXQ).toEquiv] at hbound
  exact (eq_of_le_of_card_ge hVX (by rw [hVcard]; exact hbound)).symm

end Stellmacher.SectionTen