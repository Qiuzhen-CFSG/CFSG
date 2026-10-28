module

public import Theory.Representation.Mathieu.M22James.Uniqueness.Reduction
import Mathlib.Tactic.FinCases

/-!
# Explicit words in the actual Mathieu point stabilizer

A breadth-first transversal of the certified degree-22 action sends point 1
to each label. Every Schreier edge word therefore belongs to the literal
point stabilizer. These words give a common finite family for the group and
module comparisons. Generation of the stabilizer is a separate obligation;
this file proves the word definitions, their endpoint images and membership.

The generator matrices and permutations come from the ATLAS-derived core
comparison, whose attribution is retained in `LinearModel/source/` in the
J₄ local model. Source context: the SL₃(4) restriction used in James (1973),
Lemma 8.3 and Aschbacher–Smith H.12.1, printed pp.393–394.
-/

@[expose] public section
noncomputable section
namespace Sporadic.Mathieu.M22TripleCover.Uniqueness.PointRestriction.PointModel
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel

/-- The two already certified generators of the full triple cover. -/
def ambientGenerator : Fin 2 → M22TripleCover := ![coreGeneratorA, coreGeneratorB]

/-- Their certified degree-22 permutations. -/
def ambientPermutation : Fin 2 → Equiv.Perm (Fin 22) := ![corePermA, corePermB]

lemma ambientGenerator_action (i : Fin 2) :
    corePermutationAction (ambientGenerator i) = ambientPermutation i := by
  fin_cases i
  · exact corePermutationAction_coreGeneratorA
  · exact corePermutationAction_coreGeneratorB

/-- Words are in Lean's left-action multiplication order. -/
def transversalWords : Fin 22 → List (Fin 2) :=
  ![[0], [], [1,0,0,0,1,0], [0,0,1,0], [0,0,0,0,0,0,0],
    [0,0,1,0,0,0,1,0], [0,0,1,0,0,0,0], [0,1,0], [0,1,0,0,0,0],
    [0,1,0,0,0,1,0], [1,0], [1,0,0,1,0], [0,0,0,1,0], [0,0,0],
    [1,0,0,0,0], [0,1,0,0,1,0], [0,0,0,0], [1], [0,0,0,0,0,0],
    [0,0,1,0,0,1,0], [0,0], [0,0,0,0,0]]

def transversal (i : Fin 22) : M22TripleCover :=
  ((transversalWords i).map ambientGenerator).prod

def transversalPermutation (i : Fin 22) : Equiv.Perm (Fin 22) :=
  ((transversalWords i).map ambientPermutation).prod

lemma transversal_action (i : Fin 22) :
    corePermutationAction (transversal i) = transversalPermutation i := by
  simp [transversal, transversalPermutation, map_list_prod, List.map_map, Function.comp_def, ambientGenerator_action]

set_option maxRecDepth 4000 in
lemma transversal_base (i : Fin 22) : transversalPermutation i 1 = i := by
  revert i
  decide +kernel

lemma transversal_one : transversal 1 = 1 := rfl

/-- The Schreier word T(s·i)⁻¹ s T(i), as an actual member of the fixed-point subgroup. -/
def schreierGenerator (i : Fin 22) (j : Fin 2) : pointStabilizer :=
  ⟨(transversal (ambientPermutation j i))⁻¹ * ambientGenerator j * transversal i, by
    rw [mem_pointStabilizer, map_mul, map_mul, map_inv, ambientGenerator_action,
      transversal_action, transversal_action]
    change (transversalPermutation (ambientPermutation j i))⁻¹
      (ambientPermutation j (transversalPermutation i 1)) = 1
    rw [transversal_base]
    apply (transversalPermutation (ambientPermutation j i)).injective
    change (transversalPermutation (ambientPermutation j i))
      ((transversalPermutation (ambientPermutation j i)).symm (ambientPermutation j i)) =
      transversalPermutation (ambientPermutation j i) 1
    rw [Equiv.apply_symm_apply, transversal_base]⟩

/-- The finite family whose generation is needed by both concrete comparisons. -/
def schreierGenerators : Set pointStabilizer :=
  Set.range (fun ij : Fin 22 × Fin 2 => schreierGenerator ij.1 ij.2)

end Sporadic.Mathieu.M22TripleCover.Uniqueness.PointRestriction.PointModel
