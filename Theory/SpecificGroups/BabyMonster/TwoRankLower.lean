module

public import Theory.SpecificGroups.BabyMonster.AlternatingNine
public import Theory.SpecificGroups.Alternating.TwoRankSieve
public import Theory.GroupTheory.QuasithinBasic

/-!
# The Baby Monster presentation has two-rank at least three when finite and nontrivial

The checked A₉ chain embedding contains an elementary eight. Finiteness and
nontriviality are supplied by the finite-simple catalogue guard; no additional
recognition or order assertion for the presentation is needed.
Source: Breuer–Magaard–Wilson (2019), §3.1; Aschbacher–Smith A.2.12, p.36.
-/

namespace BabyMonster
/-- The actual chain embedding witnesses the rank obstruction for this carrier. -/
public theorem three_le_twoRank [Finite Carrier] [Nontrivial Carrier] :
    3 ≤ primeRank 2 Carrier :=
  (alternatingGroup.TwoRankSieve.three_le_primeRank (by decide : 8 ≤ 9)).trans
    (Theory.GroupTheory.primeRank_le_of_injective 2
      alternatingNineHom alternatingNineHom_injective)
end BabyMonster
