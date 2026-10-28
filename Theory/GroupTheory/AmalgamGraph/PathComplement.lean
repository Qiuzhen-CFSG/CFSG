module
public import Theory.GroupTheory.AmalgamGraph.PathSupplement
public import Mathlib.GroupTheory.SchurZassenhaus
/-!
# Complements inside a Sylow supplement

If H supplements the normal Sylow p-subgroup of a finite edge group E,
then H contains a p-prime complement to that Sylow subgroup in E. Apply
Schur--Zassenhaus to H intersect O_p(E), whose index divides the p-prime
index of O_p(E), then transport the complement through the literal subgroup
inclusions. This supplies the choice K inside the path fixer used after
the path supplement in DGS 6.8.

Source: Delgado--Goldschmidt--Stellmacher, *Groups and Graphs* (1985),
Part II, 6.7--6.8, p.123.
-/

public section
open Subgroup
open scoped Pointwise
namespace Subgroup
variable {G : Type*} [Group G]
private theorem complement_le_supplement [Finite G] (prime : ℕ) [Fact prime.Prime]
    (H : Subgroup G) (hs : ∃ T : Sylow prime G, (T : Subgroup G) = pCore prime G)
    (hgen : H ⊔ pCore prime G = ⊤) :
    ∃ K : Subgroup G, K ≤ H ∧ Disjoint K (pCore prime G) ∧
      K ⊔ pCore prime G = ⊤ ∧ Nat.Coprime prime (Nat.card K) := by
  obtain ⟨T,hT⟩ := hs
  let N := (pCore prime G).subgroupOf H
  have hp : IsPGroup prime N := pCore_isPGroup.comap_subtype
  obtain ⟨n,hn⟩ := hp.exists_card_eq
  have hi : ¬ prime ∣ N.index := by
    intro hd
    apply T.not_dvd_index
    rw [hT]
    exact hd.trans (relIndex_dvd_index_of_normal (pCore prime G) H)
  have hcop : Nat.Coprime (Nat.card N) N.index := by
    rw [hn]
    exact ((Nat.Prime.coprime_iff_not_dvd (Fact.out : prime.Prime)).mpr hi).pow_left n
  obtain ⟨D,hD⟩ := exists_left_complement'_of_coprime hcop
  let K := D.map H.subtype
  have hKH : K ≤ H := map_subtype_le _
  have hdis : Disjoint K (pCore prime G) := by
    apply disjoint_iff.mpr
    apply le_antisymm _ bot_le
    intro x hx
    obtain ⟨d,hd,rfl⟩ := hx.1
    have hdN : d ∈ N := hx.2
    have hd1 : d = 1 := (disjoint_iff.mp hD.disjoint).le ⟨hd,hdN⟩
    exact congrArg Subtype.val hd1
  have hcover : K ⊔ (pCore prime G ⊓ H) = H := by
    have hm := congrArg (map H.subtype) hD.sup_eq_top
    simpa only [N, K, map_sup, subgroupOf_map_subtype, ← MonoidHom.range_eq_map, range_subtype] using hm
  have htop : K ⊔ pCore prime G = ⊤ := by
    apply top_unique
    rw [← hgen, ← hcover]
    exact sup_le (sup_le le_sup_left (inf_le_left.trans le_sup_right)) le_sup_right
  have hcomp : K.IsComplement' (pCore prime G) := by
    apply isComplement'_of_disjoint_and_mul_eq_univ hdis
    rw [← coe_mul_of_left_le_normalizer_right K (pCore prime G) le_normalizer_of_normal, htop]
    rfl
  have hcard : Nat.card K = (pCore prime G).index := hcomp.index_eq_card.symm
  refine ⟨K,hKH,hdis,htop,?_⟩
  rw [hcard, ←hT]
  exact (Nat.Prime.coprime_iff_not_dvd (Fact.out : prime.Prime)).mpr T.not_dvd_index

/-- A subgroup supplementing a normal Sylow contains a complement to it. -/
theorem exists_complement_le_of_core_supplement (prime : ℕ) [Fact prime.Prime]
    (E H : Subgroup G) [Finite E] (hHE : H ≤ E)
    (hs : ∃ T : Sylow prime E, (T : Subgroup E) = pCore prime E)
    (hgen : H ⊔ E.pCoreIn prime = E) :
    ∃ K : Subgroup G, K ≤ H ∧ Disjoint K (E.pCoreIn prime) ∧
      K ⊔ E.pCoreIn prime = E ∧ Nat.Coprime prime (Nat.card K) := by
  have hi : H.subgroupOf E ⊔ pCore prime E = ⊤ := by
    apply (map_injective E.subtype_injective)
    rw [map_sup, map_subgroupOf_eq_of_le hHE,
      ← MonoidHom.range_eq_map, E.range_subtype]
    exact hgen
  obtain ⟨D,hDH,hd,hg,hcard⟩ := complement_le_supplement prime (H.subgroupOf E) hs hi
  refine ⟨D.map E.subtype, ?_, disjoint_map E.subtype_injective hd, ?_, ?_⟩
  · exact (map_mono hDH).trans_eq (map_subgroupOf_eq_of_le hHE)
  · have hm := congrArg (map E.subtype) hg
    simpa only [pCoreIn, map_sup, ← MonoidHom.range_eq_map, range_subtype] using hm
  · rwa [card_map_of_injective E.subtype_injective]
end Subgroup
