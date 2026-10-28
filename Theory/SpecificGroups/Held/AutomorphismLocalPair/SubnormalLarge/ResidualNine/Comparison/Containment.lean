module

public import Theory.SpecificGroups.Held.AutomorphismLocalPair.SubnormalLarge.ResidualNine.Definitions
public import Theory.SpecificGroups.Held.AutomorphismLocalPair.LiteralLocal.Action
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.CandidateOrders.Factors.Pair00

/-!
# Containment of the conjugated pure Held pair in the full seed normalizer

For each of the six literal pair generators, its conjugate by the inverse of the
published word permutes the seed subgroup: every conjugated seed generator is an
explicit short word in the twelve seed generators. The faithful four-point base
checks these 72 identities. Finite subgroup containment gives normalization.

Source: ATLAS HeG1-p2058B0 and the literal pair words; GLS3 Table 5.3p and
Aschbacher--Smith, printed p.526. GAP proposes words; the Lean kernel checks them.
-/

public section
namespace Held.AutomorphismLocalPair.ResidualNine.Comparison
open Subgroup LiteralLocal
open LocalPairs.PairCoverage.LocalActions
open LocalPairs.PairCoverage.LocalActions.Exhaustion
open LocalPairs.PairCoverage.LocalActions.Exhaustion.CandidateOrderCertificate.Factors

private def conjugatorPerm : Equiv.Perm Vertex :=
  ([(true, -2), (false, 1), (true, 2), (false, 1), (true, -1), (false, 1),
    (true, -1), (false, 1), (true, 1), (false, 1), (true, -1)].map
    (fun t : Bool × ℤ => (if t.1 then Local0.localTable else atlasA) ^ t.2)).prod

private theorem conjugatorPerm_eq : conjugatorPerm = representation pairConjugator :=
  (Pair00.map_local_word _).symm

private def actor (i : Fin 6) : He :=
  pairConjugator⁻¹ * Pair00.generator i * pairConjugator
private def actorPerm (i : Fin 6) : Equiv.Perm Vertex :=
  conjugatorPerm⁻¹ * Pair00.generatorTable i * conjugatorPerm

private theorem actorPerm_eq (i : Fin 6) : actorPerm i = representation (actor i) := by
  simp only [actorPerm, actor, conjugatorPerm_eq, Pair00.generatorTable_eq, map_mul, map_inv]

private def conjugateWord : Fin 6 → Fin 12 → List (Fin 12)
  | 0, 0 => [0]
  | 0, 1 => [1, 3]
  | 0, 2 => [1, 2, 3, 4]
  | 0, 3 => [1, 4, 5]
  | 0, 4 => [6, 4, 6]
  | 0, 5 => [2, 3]
  | 0, 6 => [9]
  | 0, 7 => [10]
  | 0, 8 => [5, 6, 8]
  | 0, 9 => [6, 9]
  | 0, 10 => [7, 10]
  | 0, 11 => [2, 3]
  | 1, 0 => [0, 4, 5]
  | 1, 1 => [0, 2, 6, 7]
  | 1, 2 => [1, 3, 4]
  | 1, 3 => [3, 5]
  | 1, 4 => [0, 3]
  | 1, 5 => [3]
  | 1, 6 => [6]
  | 1, 7 => [1, 7, 1]
  | 1, 8 => [1, 9, 4]
  | 1, 9 => [9]
  | 1, 10 => [5, 10]
  | 1, 11 => [3]
  | 2, 0 => [0, 4, 5]
  | 2, 1 => [1, 2, 3]
  | 2, 2 => [2, 5]
  | 2, 3 => [3, 5]
  | 2, 4 => [4]
  | 2, 5 => [5]
  | 2, 6 => [6]
  | 2, 7 => [1, 7, 1]
  | 2, 8 => [8]
  | 2, 9 => [9]
  | 2, 10 => [5, 10]
  | 2, 11 => [5]
  | 3, 0 => [0, 4, 5]
  | 3, 1 => [3, 4]
  | 3, 2 => [1, 2, 3, 4]
  | 3, 3 => [2, 6, 7]
  | 3, 4 => [6, 4, 6]
  | 3, 5 => [2, 3]
  | 3, 6 => [6]
  | 3, 7 => [1, 7, 1]
  | 3, 8 => [5, 6, 9]
  | 3, 9 => [6, 9]
  | 3, 10 => [2, 7, 9]
  | 3, 11 => [2, 3]
  | 4, 0 => [0]
  | 4, 1 => [1]
  | 4, 2 => [2]
  | 4, 3 => [3]
  | 4, 4 => [4]
  | 4, 5 => [5]
  | 4, 6 => [7]
  | 4, 7 => [6]
  | 4, 8 => [2, 9]
  | 4, 9 => [10]
  | 4, 10 => [9]
  | 4, 11 => [5]
  | 5, 0 => [0, 3]
  | 5, 1 => [1, 5]
  | 5, 2 => [2]
  | 5, 3 => [3]
  | 5, 4 => [4, 5]
  | 5, 5 => [5]
  | 5, 6 => [6]
  | 5, 7 => [7]
  | 5, 8 => [8]
  | 5, 9 => [9]
  | 5, 10 => [10]
  | 5, 11 => [5]

set_option maxRecDepth 16384 in
private theorem conjugation_check : ∀ i : Fin 6, ∀ j : Fin 12, ∀ v : Fin 4,
    (actorPerm i * seedPerm j * (actorPerm i)⁻¹) ⟨v.val, by omega⟩ =
      seedPermWord (conjugateWord i j) ⟨v.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem conjugation (i : Fin 6) (j : Fin 12) :
    actor i * seedGen j * (actor i)⁻¹ = seedWord (conjugateWord i j) := by
  apply eq_of_four_point_images
  simp only [map_mul, map_inv]
  rw [← actorPerm_eq, ← seedPerm_eq, ← seedPermWord_eq]
  exact conjugation_check i j

private theorem actor_normalizes (i : Fin 6) : actor i ∈ representativeLargeLocal := by
  apply mem_normalizer_fintype
  apply seed_le_of_generators (representativeLargeSeed.comap (MulAut.conj (actor i)).toMonoidHom)
  intro j
  change actor i * seedGen j * (actor i)⁻¹ ∈ representativeLargeSeed
  rw [conjugation]
  exact seedWord_mem _

private theorem generator_mem_comap (i : Fin 6) :
    Pair00.generator i ∈ representativeLargeLocal.comap
      (MulAut.conj pairConjugator⁻¹).toMonoidHom := by
  change pairConjugator⁻¹ * Pair00.generator i * (pairConjugator⁻¹)⁻¹ ∈
    representativeLargeLocal
  rw [inv_inv]
  exact actor_normalizes i

/-- Every element of the literal pair, conjugated by the inverse word, normalizes
both seeds' join. The assertion is containment in the full ambient normalizer. -/
theorem candidate_map_inverse_le :
    (candidateProduct false 0).map (MulAut.conj pairConjugator⁻¹).toMonoidHom ≤
      representativeLargeLocal := by
  rw [map_le_iff_le_comap]
  apply sup_le
  · apply (closure_le _).mpr
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact generator_mem_comap 0
    · exact generator_mem_comap 1
  · apply (closure_le _).mpr
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact generator_mem_comap 2
    · exact generator_mem_comap 3
    · exact generator_mem_comap 4
    · exact generator_mem_comap 5

end Held.AutomorphismLocalPair.ResidualNine.Comparison
