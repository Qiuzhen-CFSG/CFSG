module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.GeneratorPair
public import Theory.GroupTheory.WordSubgroup
public import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.Tactic.FinCases

/-!
# Faithfulness of the J₂ permutation-normalizer action

Two explicitly evaluated words in the published degree-100 generators have
exactly one common fixed point. An explicit orbit transversal reaches all
100 points. A permutation centralizing the generators therefore fixes that
point and then every point. Consequently conjugation embeds the full
permutation normalizer into the actual automorphism group of the carrier.

The finite equalities are checked by kernel reduction against the lookup
permutations already proved equal to the original ATLAS cycles. No order,
simplicity, or comparison with the separate icosian model is used.

Source: R. A. Wilson et al., ATLAS of Finite Group Representations,
`J2G1-p100B0`; original permutations and provenance are in `AtlasCarriers/source/`.
The transversal and stabilizer words are derived from those permutations.
-/

@[expose] public section

open Theory.GroupTheory
namespace Sporadic.LeechRelated.J2.ExceptionalParabolics
open GeneratorPair
set_option maxRecDepth 20000
set_option maxHeartbeats 800000

private def orbitWords : Fin 100 → List (Fin 2) := ![
  [],
  [1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1],
  [0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1],
  [1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1],
  [0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1],
  [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1],
  [0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1],
  [1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1],
  [1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1],
  [1, 0, 1, 0, 1, 1],
  [0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1],
  [0, 1, 1, 0, 1, 1],
  [0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1],
  [1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1],
  [1, 1, 0, 1, 1, 0, 1, 0, 1],
  [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1],
  [0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1],
  [1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1],
  [1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1],
  [0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1],
  [0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1],
  [1],
  [0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1],
  [0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1],
  [0, 1, 1, 0, 1, 0, 1],
  [0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1],
  [0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1],
  [1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1],
  [0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1],
  [1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1],
  [1, 0, 1, 1, 0, 1, 1],
  [0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1],
  [1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1],
  [1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1],
  [0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1],
  [0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1],
  [1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1],
  [0, 1, 0, 1, 1, 0, 1, 1],
  [1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1],
  [0, 1, 0, 1, 0, 1, 1],
  [0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1],
  [1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1],
  [0, 1, 0, 1, 0, 1, 0, 1, 1],
  [0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1],
  [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1],
  [1, 0, 1],
  [0, 1, 1, 0, 1],
  [1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1],
  [1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1],
  [0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1],
  [0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1],
  [0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1],
  [1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1],
  [1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1],
  [1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1],
  [0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1],
  [1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1],
  [1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1],
  [1, 1, 0, 1, 0, 1, 1, 0, 1, 1],
  [0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1],
  [0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1],
  [0, 1, 0, 1, 1],
  [1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1],
  [1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1],
  [0, 1, 0, 1, 0, 1],
  [0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1],
  [0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1],
  [1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1],
  [0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1],
  [1, 0, 1, 0, 1],
  [0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1],
  [1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1],
  [1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1],
  [0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1],
  [1, 1, 0, 1, 0, 1],
  [0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1],
  [0, 1, 0, 1, 1, 0, 1, 0, 1],
  [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1],
  [0, 1, 1],
  [1, 1],
  [0, 1, 0, 1],
  [1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1],
  [1, 0, 1, 1],
  [0],
  [0, 1],
  [0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1],
  [1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1],
  [1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1],
  [1, 1, 0, 1],
  [1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1],
  [1, 0, 1, 0, 1, 0, 1, 1],
  [1, 0, 1, 0, 1, 1, 0, 1, 0, 1],
  [1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1],
  [1, 0, 1, 0, 1, 1, 0, 1, 1],
  [0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1],
  [1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1],
  [0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1],
  [1, 0, 1, 1, 0, 1, 0, 1],
  [0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1],
  [1, 1, 0, 1, 1]]

private def word (w : List (Fin 2)) : Carrier := evalWord ![a,b] w

private theorem inclusion_word (w : List (Fin 2)) :
    inclusion (word w) = evalWord ![generatorA,generatorB] w := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    change inclusion ((![a,b] : Fin 2 → Carrier) i * word w) = _
    rw [map_mul, ih]
    congr 1
    fin_cases i <;> rfl

private theorem word_apply (w : List (Fin 2)) (i : Fin 100) :
    inclusion (word w) i = evalWord ![tableA,tableB] w i := by
  rw [inclusion_word, generatorA_eq_table, generatorB_eq_table]

/-- An explicit orbit transversal for the published permutation action. -/
theorem action_transitive (i : Fin 100) : ∃ g : Carrier, inclusion g 0 = i := by
  refine ⟨word (orbitWords i), ?_⟩
  rw [word_apply]
  exact (by decide +kernel : ∀ j : Fin 100,
    evalWord ![tableA,tableB] (orbitWords j) 0 = j) i

private def fixWord₁ : List (Fin 2) := [0, 1, 0]
private def fixWord₂ : List (Fin 2) := [1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1]

private theorem fixWord₁_zero : inclusion (word fixWord₁) 0 = 0 := by
  rw [word_apply]
  decide +kernel
private theorem fixWord₂_zero : inclusion (word fixWord₂) 0 = 0 := by
  rw [word_apply]
  decide +kernel

private theorem common_fixed_point (i : Fin 100)
    (h₁ : inclusion (word fixWord₁) i = i)
    (h₂ : inclusion (word fixWord₂) i = i) : i = 0 := by
  rw [word_apply] at h₁ h₂
  exact (by decide +kernel : ∀ j : Fin 100,
    evalWord ![tableA,tableB] fixWord₁ j = j →
    evalWord ![tableA,tableB] fixWord₂ j = j → j = 0) i h₁ h₂

/-- The symmetric-group centralizer of the actual permutation carrier is trivial.
Two stabilizer words fix only zero, and the explicit orbit covers every point. -/
theorem permutation_centralizer_eq_bot :
    Subgroup.centralizer (generated : Set (Equiv.Perm (Fin 100))) = ⊥ := by
  apply eq_bot_iff.mpr
  intro c hc
  have comm (g : Carrier) (i : Fin 100) :
      inclusion g (c i) = c (inclusion g i) :=
    congrArg (fun p : Equiv.Perm (Fin 100) => p i)
      ((Subgroup.mem_centralizer_iff.mp hc) (inclusion g) g.property)
  have hzero : c 0 = 0 := common_fixed_point (c 0)
    (by rw [comm, fixWord₁_zero]) (by rw [comm, fixWord₂_zero])
  change c = 1
  apply Equiv.ext
  intro i
  obtain ⟨g, rfl⟩ := action_transitive i
  change c (inclusion g 0) = inclusion g 0
  rw [← comm, hzero]

/-- Conjugation embeds the full permutation normalizer into the actual automorphism group. -/
theorem normalizer_action_injective : Function.Injective generated.normalizerMonoidHom := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  rw [Subgroup.normalizerMonoidHom_ker, permutation_centralizer_eq_bot]
  simp

end Sporadic.LeechRelated.J2.ExceptionalParabolics
