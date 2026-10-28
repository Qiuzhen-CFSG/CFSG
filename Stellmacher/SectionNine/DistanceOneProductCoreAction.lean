module

public import Stellmacher.SectionNine.DistanceOneFirstCoreQuotient
public import Theory.GroupTheory.WreathQuotientSylowControl
public import Theory.GroupTheory.NormalizedSupCard


/-!
# Noncentral terminal-core action on the extracted product

After the initial core equals its center, a subgroup V of order32 in the
terminal core, meeting the initial center in order8, is not centralized by
that core modulo the initial center. The terminal core order64 and the
faithful initial quotient are explicit. No full local conclusion is assumed.

Otherwise the actual wreath image of the terminal core centralizes V's image
of order4 inside the actual Sylow D8. Its centralizer lies in that same image,
so pulling back gives Q_d contained in V joined with Z_a. The normalized-product
cardinality formula gives this join order64, hence equality. This contradicts
the critical pair's Z_a not contained in Q_d.

This is the small maximal-subgroup reduction following Stellmacher(9.1),
relation(11), Journal of Algebra190 (1997), p.48. In particular a maximal V1
with [V1,Q_d]=Z_d cannot equal V once the source center containment is supplied.
The actual (1.3) action packet provides its remaining order alternatives.
-/

namespace Stellmacher.SectionNine
open Stellmacher.Later Stellmacher.SectionsFiveToSeven

public theorem distance_one_product_core_commutator_not_le_initial_center
    {G : Type*} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B) (hb : ctx.criticalPath.length=1)
    (hfaith : DistanceOneFaithfulConclusion ctx)
    (hcore : QAt ctx.Γ ctx.criticalPath.a=ZAt ctx.Γ ctx.criticalPath.a)
    (V : Subgroup G) (hVQ : V≤QAt ctx.Γ ctx.criticalPath.a')
    (hVcard : Nat.card V=32)
    (hQcard : Nat.card (QAt ctx.Γ ctx.criticalPath.a')=64)
    (hIcard : Nat.card (V ⊓ ZAt ctx.Γ ctx.criticalPath.a : Subgroup G)=8) :
    ¬ ⁅QAt ctx.Γ ctx.criticalPath.a',V⁆ ≤ ZAt ctx.Γ ctx.criticalPath.a := by
  let first := GAt ctx.Γ ctx.criticalPath.a
  let Za := ZAt ctx.Γ ctx.criticalPath.a
  let Q := QAt ctx.Γ ctx.criticalPath.a'
  have hend : ctx.criticalPath.a'=ctx.criticalPath.firstStep := by
    rw [← ctx.criticalPath.path_end,← ctx.criticalPath.path_first]
    congr 1
    exact Fin.ext hb
  have hQT : Q≤T := by
    change QAt ctx.Γ ctx.criticalPath.a'≤T
    rw [hend]
    exact (SevenSix.local_cores_le_edge_sylow ctx.sectionSeven ctx.Γ ctx.criticalPath).2
  have hVT : V≤T := hVQ.trans hQT
  have hZaT : Za≤T := by
    change ZAt ctx.Γ ctx.criticalPath.a≤T
    rw [← hcore]
    exact (SevenSix.local_cores_le_edge_sylow ctx.sectionSeven ctx.Γ ctx.criticalPath).1
  obtain ⟨hTfirst,P,hP⟩ := (SevenSix.edge_sylow_data ctx.sectionSeven ctx.Γ ctx.criticalPath).1
  change T≤first at hTfirst
  have hVfirst := hVT.trans hTfirst
  have hQfirst := hQT.trans hTfirst
  have hPnative : (P:Subgroup first)=T.subgroupOf first := by
    apply Subgroup.map_injective first.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le hTfirst]
    exact hP
  obtain ⟨⟨f,hf,hfk⟩,_⟩ := distance_one_first_core_quotient_of_core_eq_center ctx hb hfaith hcore
  have hker : f.ker=Za.subgroupOf first := by rw [hfk,hcore]
  have hindex : 4≤f.ker.relIndex (V.subgroupOf first) := by
    rw [hker,Subgroup.relIndex_subgroupOf hVfirst,← Subgroup.inf_relIndex_left]
    have h := Subgroup.relIndex_mul_relIndex (⊥ : Subgroup G) (V ⊓ Za) V bot_le inf_le_left
    simp only [Subgroup.relIndex_bot_left] at h
    change Nat.card (V ⊓ Za : Subgroup G)=8 at hIcard
    rw [hIcard,hVcard] at h
    omega
  intro hcomm
  have hncomm : ⁅Q.subgroupOf first,V.subgroupOf first⁆≤f.ker := by
    rw [hker]
    apply Subgroup.commutator_le.mpr
    intro q hq v hv
    exact hcomm (Subgroup.commutator_mem_commutator hq hv)
  obtain ⟨hle,_⟩ := wreath_quotient_sylow_control f hf P (Q.subgroupOf first)
    (V.subgroupOf first) (by rw [hPnative]; exact Subgroup.subgroupOf_mono first hQT)
    (by rw [hPnative]; exact Subgroup.subgroupOf_mono first hVT) hindex hncomm
  have hQsup : Q≤V⊔Za := by
    have hmap := Subgroup.map_mono (f:=first.subtype) hle
    rw [Subgroup.map_subgroupOf_eq_of_le hQfirst,Subgroup.map_sup,
      Subgroup.map_subgroupOf_eq_of_le hVfirst,hPnative,hker] at hmap
    apply hmap.trans
    apply sup_le_sup_left
    rintro x ⟨y,hy,rfl⟩
    exact hy.2
  have hn : V≤Subgroup.normalizer (Za : Set G) := by
    apply hVfirst.trans
    exact stabilizer_le_normalizer_z ctx.Γ ctx.criticalPath.a
  have hsupcard : Nat.card (V⊔Za : Subgroup G)=64 := by
    have h := Subgroup.card_mul_eq_card_inf_mul_card_sup_of_normalizes Za V hn
    have hZa : Nat.card Za=16 := hfaith.1
    rw [hZa,hVcard,inf_comm Za V,sup_comm Za V,hIcard] at h
    omega
  have heq : Q=V⊔Za := Subgroup.eq_of_le_of_card_ge hQsup (by rw [hQcard,hsupcard])
  apply ctx.criticalPath.critical.2
  change Za≤Q
  rw [heq]
  exact le_sup_right
end Stellmacher.SectionNine
