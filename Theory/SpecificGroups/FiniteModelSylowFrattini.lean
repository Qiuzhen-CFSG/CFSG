module
public import Theory.GroupTheory.SylowFrattiniBounds
public import Theory.SpecificGroups.Janko3.Model.OuterSimpleSections
public import Theory.SpecificGroups.McLaughlin.Multiplier.ModelComparison.Source

/-!
# Sylow Frattini bounds for the actual J₃ and McL models

Sylow conjugacy transports the five-generator J₃ certificate to any Sylow
subgroup and any equivalent carrier. For McL, its proved permutation-to-Leech
comparison and certified order bound the entire Sylow subgroup by 128.
These are intrinsic finite-model inputs for Aschbacher--Smith 4.4.10, p.621;
no assertion of full outer automorphism solvability is made.
-/

public section
open Subgroup
namespace Theory.SpecificGroups.FiniteModelSylowFrattini
open Theory.GroupTheory.SylowFrattiniBounds
variable {G : Type*} [Group G] [Finite G]

/-- Every actual J₃ Sylow Frattini quotient has at most 32 elements. -/
theorem j3_card_le_thirtytwo (e : G ≃* Sporadic.Janko3.Model) (P : Sylow 2 G) :
    Nat.card (P ⧸ frattini P) ≤ 32 := by
  let Q := P.mapSurjective (f := e.toMonoidHom) e.surjective
  let a : P ≃* Q := e.subgroupMap (P : Subgroup G)
  rw [card_congr a, card_congr (Q.equiv Sporadic.Janko3.TwoLocal.sourceSylow)]
  exact Sporadic.Janko3.TwoLocal.sourceSylow_frattini_card_le

/-- Every actual McL Sylow Frattini quotient has at most 128 elements. -/
theorem mcl_card_le_128 (e : G ≃* Sporadic.LeechRelated.McL.Carrier) (P : Sylow 2 G) :
    Nat.card (P ⧸ frattini P) ≤ 128 := by
  apply card_le_of_order_not_dvd (n := 7) P
  rw [Nat.card_congr e.toEquiv,
    Nat.card_congr McLaughlin.Multiplier.permutationModelEquiv.toEquiv,
    Atlas.Sporadic.McLaughlin.card]
  norm_num [Atlas.Sporadic.McLaughlin.order]

end Theory.SpecificGroups.FiniteModelSylowFrattini
