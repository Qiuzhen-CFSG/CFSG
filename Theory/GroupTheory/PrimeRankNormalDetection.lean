module

public import Theory.GroupTheory.RankTwoDisjointAction
public import Theory.GroupTheory.PrimeRankInvolutionLift
public import Theory.GroupTheory.QuasithinBasic

/-!
# Detecting rank one from a normal subgroup

In a finite group of p-rank at most two, a subgroup whose elementary
p-subgroups all miss a normal subgroup of order divisible by p has rank
at most one. Otherwise an elementary plane acts on that disjoint normal
subgroup and produces an elementary subgroup of order p³ by fixed-point
counting.

This is the rank argument used for the literal quotient centralizer in
Aschbacher–Smith, *The Classification of Quasithin Groups*,
Lemma 12.8.13(8), combined manuscript of 1 March 2004, printed p.856.
-/

open Subgroup

namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

public theorem primeRank_le_one_of_disjoint_normal
    {p : ℕ} [Fact p.Prime] (hr : primeRank p G ≤ 2) (I C : Subgroup G) [I.Normal]
    (hdiv : p ∣ Nat.card I)
    (hdis : ∀ E : Subgroup G, E ≤ C → IsElementaryAbelian p E → Disjoint E I) :
    primeRank p C ≤ 1 := by
  by_contra hn
  have hrc : primeRank p C = 2 := by
    have hu := (Theory.GroupTheory.primeRank_le_of_injective p C.subtype C.subtype_injective).trans hr
    omega
  obtain ⟨E, hE, hc⟩ := exists_elementaryAbelian_card_primeRank (G := C) (p := p)
  let := hE
  let P := E.map C.subtype
  let : IsElementaryAbelian p P := IsElementaryAbelian.map_subtype
  have hP : Nat.card P = p ^ 2 := by rw [card_map_of_injective C.subtype_injective, hc, hrc]
  have hnI : P ≤ normalizer (I : Set G) := by rw [I.normalizer_eq_top]; exact le_top
  have hcop := coprime_card_of_normalized_disjoint_plane hr P I hP hnI
    (hdis P (map_subtype_le E) inferInstance)
  exact (((Fact.out : p.Prime).coprime_iff_not_dvd).mp hcop) hdiv
end Subgroup
