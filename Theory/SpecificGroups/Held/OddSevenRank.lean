module
public import Theory.SpecificGroups.Held.OddCubeCandidates.Cardinality
public import Theory.GroupTheory.OddPrimeRankOneSylow

/-!
# Seven-rank of the actual Held carrier

The certified nonabelian subgroup of order 343 lies in a Sylow seven-subgroup.
If Held had seven-rank at most one, that Sylow subgroup would be cyclic, which
would make the certified subgroup commutative. No full group order or simplicity
assertion is required. Source: GLS3 Table 5.3p and the ATLAS words retained in
`OddCubeCandidates`; used in Aschbacher--Smith 4.3.16, printed p.618.
-/

public section
open Subgroup
namespace Held

/-- A nonabelian subgroup of order 7³ forces seven-rank at least two. -/
theorem seven_rank_ge_two : 2 ≤ primeRank 7 He := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  have hp : IsPGroup 7 OddCubeCandidates.seven :=
    IsPGroup.of_card (n := 3) (by simpa using OddCubeCandidates.card_seven)
  obtain ⟨P,hP⟩ := hp.exists_le_sylow
  by_contra! hr
  let : IsCyclic P := P.isCyclic_of_odd_of_primeRank_le_one (by decide) (by omega)
  let : IsCyclic OddCubeCandidates.seven := Subgroup.isCyclic_of_le hP
  exact OddCubeCandidates.seven_not_commutative inferInstance
end Held

