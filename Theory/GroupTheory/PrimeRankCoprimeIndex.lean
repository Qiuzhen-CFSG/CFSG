module
public import Theory.GroupTheory.PrimeRankSylow
/-!
# Prime rank at an index prime to the given prime

A Sylow subgroup of a subgroup of index prime to p maps to an ambient Sylow
subgroup. Prime rank is detected on these same Sylow groups, so the subgroup
and ambient group have equal p-rank. No normality is required.

The source consumer is the exceptional-model degree calculation in
Aschbacher--Smith 4.3.16, printed p.618: a binary rank-one section of degree
three would force cubic rank one in the full quotient.
-/

public section
open Subgroup Theory.GroupTheory
namespace Subgroup
variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
/-- A subgroup of index prime to p has the ambient p-rank. -/
theorem primeRank_eq_of_not_dvd_index (B : Subgroup G) (hi : ¬ p ∣ B.index) :
    primeRank p B = primeRank p G := by
  let P : Sylow p B := default
  have hindex : ¬ p ∣ ((P : Subgroup B).map B.subtype).index := by
    rw [index_map_of_injective _ B.subtype_injective, range_subtype]
    exact (Fact.out : p.Prime).not_dvd_mul P.not_dvd_index hi
  let Q : Sylow p G := (P.isPGroup'.map B.subtype).toSylow hindex
  rw [P.primeRank_eq, Q.primeRank_eq]
  exact primeRank_equiv p ((P : Subgroup B).equivMapOfInjective B.subtype B.subtype_injective)
end Subgroup
