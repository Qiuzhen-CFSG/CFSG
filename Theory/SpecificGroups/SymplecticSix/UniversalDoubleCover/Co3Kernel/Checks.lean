module

public import Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover.Co3Kernel.SwitchB
public import Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover.Co3Kernel.SwitchC
public import Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover.Co3Kernel.SwitchD
import Mathlib.Tactic.FinCases

/-!
# Two-graph rigidity certificates for the Co₃ kernel

The signatures have precisely the fibers {x,b²x}. For each moved letter, a
specified bridge distinguishes both its pair and the bridge's pair from vertex
0. These finite checks give the two-step rigidity argument in `Co3Kernel`.
The switching identities certify invariance under the actual three generators.

Source motivation: GLS3 Table 5.3j; certificate and permutation provenance are
recorded in `source/README.md`. Every computation uses `decide +kernel`.
-/

public section
namespace Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover.Co3Kernel
open Sporadic.LeechRelated.Co3.CentralizerSection

set_option maxRecDepth 20000
set_option Elab.async false

theorem adjacent_anchor : ∀ x, adjacent 4 x = false := by
  apply Tables.allFin
  decide +kernel

theorem triangle_anchor (x y : Fin 276) : triangle 4 x y = adjacent x y := by
  simp only [triangle, adjacent_anchor, Bool.false_xor]

theorem signature_spec : ∀ (x : Fin 276) (i : Fin 36),
    (signature x).getLsbD i.val = adjacent (Tables.fixedPoint i) x := by
  apply allFin₂
  decide +kernel

theorem signature_fibers : ∀ x y, signature x = signature y →
    y = x ∨ y = Tables.tableZ x := by
  apply allFin₂
  decide +kernel

theorem bridge_separates : ∀ x, Tables.tableZ x ≠ x →
    adjacent 0 (bridge x) ≠ adjacent 0 (Tables.tableZ (bridge x)) ∧
      adjacent (bridge x) x ≠ adjacent (bridge x) (Tables.tableZ x) := by
  apply Tables.allFin
  decide +kernel

theorem generator_switch (i : Fin 3) (x y : Fin 276) :
    adjacent (Tables.generatorTable i x) (Tables.generatorTable i y) =
      ((adjacent x y ^^ adjacent (Tables.generatorTable i 4) (Tables.generatorTable i x)) ^^
        adjacent (Tables.generatorTable i 4) (Tables.generatorTable i y)) := by
  fin_cases i
  · exact switchB x y
  · exact switchC x y
  · exact switchD x y

end Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover.Co3Kernel
