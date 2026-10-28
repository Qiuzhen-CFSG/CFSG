module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Noncommuting.PathControl

/-!
# Literal rank-one generation at the source edges

An odd-index normal local actor contains every two-subgroup of its full vertex
stabilizer. In a two-closed full edge, its embedded Sylow is exactly the edge
two-core. The proved rank-one Sylow-overgroup theorem then says that this
Sylow and any escaping two-subgroup generate the local actor. The full Borel
supplement gives the corresponding coset factorization.

These discharge the (5.1) generation steps used twice in (7.3), from the
actual local data supplied by (6.1). The model isomorphisms in that data are
retained, including the small rank-one groups. No Chapter 7 bound is assumed.
Source: DGS, *Groups and Graphs* (1985), pp.104,118--119,127.
-/

public section
open Subgroup
open scoped Pointwise
open Theory.GroupTheory.AmalgamGraph
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Noncommuting
variable {G : Type*} [Group G] {H E : Subgroup G}

/-- Odd relative index and relative normality place every two-subgroup in
this same marked local actor. -/
theorem local_twoGroup_le_star (d : LocalRankOneData H E)
    (hodd : ¬ 2 ∣ d.Pstar.relIndex H)
    (A : Subgroup G) (hp : IsPGroup 2 A) (hAH : A ≤ H) : A ≤ d.Pstar := by
  let := d.finite_P
  let N := d.Pstar.subgroupOf H
  let A' := A.subgroupOf H
  let : N.Normal := d.normal
  have hA' : IsPGroup 2 A' := hp.comap_subtype
  obtain ⟨n,hn⟩ := hA'.exists_card_eq
  have hcop : Nat.Coprime N.index (Nat.card A') := by
    rw [hn]
    exact Nat.prime_two.coprime_pow_of_not_dvd hodd
  have hi : N.relIndex A' = 1 := Nat.eq_one_of_dvd_coprimes hcop
    (N.relIndex_dvd_index_of_normal A') (relIndex_dvd_card N A')
  have hle : A' ≤ N := relIndex_eq_one.mp hi
  intro a ha
  exact hle (show (⟨a,hAH ha⟩ : H) ∈ A' from ha)

/-- The specified rank-one Sylow is the literal two-core of the full edge. -/
theorem local_sylow_eq_edgeCore (d : LocalRankOneData H E)
    (hodd : ¬ 2 ∣ d.Pstar.relIndex H)
    (hclosed : ∃ T : Sylow 2 E, (T : Subgroup E) = pCore 2 E) :
    (d.sylow : Subgroup d.Pstar).map d.Pstar.subtype = E.pCoreIn 2 := by
  let := d.finite_P
  have hEH : E ≤ H := le_sup_right.trans d.supplement.le
  let : Finite E := Finite.of_injective (inclusion hEH) (inclusion_injective _)
  let T := (d.sylow : Subgroup d.Pstar).map d.Pstar.subtype
  have hTE : T ≤ E := by
    intro t ht
    have hm : t ∈ d.Pstar ⊓ normalizer (T : Set G) :=
      ⟨map_subtype_le _ ht,T.le_normalizer ht⟩
    rw [← d.borel_eq] at hm
    exact hm.2
  have hCL : E.pCoreIn 2 ≤ d.Pstar := local_twoGroup_le_star d hodd _
    (isPGroup_pCoreIn 2 E) ((pCoreIn_le 2 E).trans hEH)
  apply le_antisymm (pGroup_le_core_of_core_sylow E T hTE (d.sylow.isPGroup'.map _) hclosed)
  apply le_sylow_image_of_normalizes d.Pstar d.sylow rfl (isPGroup_pCoreIn 2 E) hCL
  intro x hx
  have hm : x ∈ d.Pstar ⊓ E := ⟨hCL hx,pCoreIn_le 2 E hx⟩
  rw [d.borel_eq] at hm
  exact hm.2

/-- The source local generation step follows from the actual rank-one
quotient, its marked Sylow normalizer, and escape from the full edge. -/
theorem local_escaping_twoGroup_generates (d : LocalRankOneData H E)
    (hodd : ¬ 2 ∣ d.Pstar.relIndex H)
    (hclosed : ∃ T : Sylow 2 E, (T : Subgroup E) = pCore 2 E)
    (A : Subgroup G) (hp : IsPGroup 2 A) (hAH : A ≤ H) (hAE : ¬ A ≤ E) :
    A ⊔ E.pCoreIn 2 = d.Pstar := by
  let := d.finite_P
  let : Finite d.Pstar := Finite.of_injective (inclusion d.Pstar_le) (inclusion_injective _)
  rw [← local_sylow_eq_edgeCore d hodd hclosed]
  let T := (d.sylow : Subgroup d.Pstar).map d.Pstar.subtype
  let M := A ⊔ T
  have hAL := local_twoGroup_le_star d hodd A hp hAH
  have hML : M ≤ d.Pstar := sup_le hAL (map_subtype_le _)
  change M = d.Pstar
  by_contra hne
  have hproper : M.subgroupOf d.Pstar < ⊤ := by
    apply lt_top_iff_ne_top.mpr
    intro he
    apply hne
    have hh := congrArg (Subgroup.map d.Pstar.subtype) he
    simpa only [map_subgroupOf_eq_of_le hML,← MonoidHom.range_eq_map,range_subtype] using hh
  have hTM : (d.sylow : Subgroup d.Pstar) ≤ M.subgroupOf d.Pstar := by
    intro t ht
    exact (show T ≤ M from le_sup_right) (mem_map_of_mem d.Pstar.subtype ht)
  have hMN := (rankOneSylowFacts_of_rankOneQuotient d.quotient d.sylow).unique_maximal
    _ hTM hproper
  rw [← source_star_borel d] at hMN
  apply hAE
  intro a ha
  exact hMN (show (⟨a,hAL ha⟩ : d.Pstar) ∈ M.subgroupOf d.Pstar from
    (show A ≤ M from le_sup_left) ha)

/-- The original full edge supplement gives the factorization used by the
faithful common-normal obstruction. -/
theorem local_star_factor (d : LocalRankOneData H E) (a : G) (ha : a ∈ H) :
    ∃ l ∈ d.Pstar, ∃ t ∈ E, a = l*t := by
  have hm : a ∈ (d.Pstar : Set G) * (E : Set G) := by
    rw [← source_star_product d]
    exact ha
  obtain ⟨l,hl,t,ht,he⟩ := hm
  exact ⟨l,hl,t,ht,he.symm⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.Noncommuting
