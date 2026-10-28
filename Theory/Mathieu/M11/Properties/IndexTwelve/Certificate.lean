module

public import Theory.Mathieu.M11.Generators
public import Mathlib.Algebra.Group.Pointwise.Finset.Scalar

/-!
# A small block-orbit certificate for an M11 subgroup

The eleven displayed five-subsets are preserved by `AB` and the involution
`(0, 10)(3, 5)(6, 7)(8, 9)`. Twelve words in the native generators give distinct
translates of this collection. The kernel checks only these small finite
identities; no enumeration of M11 or subgroup-classification oracle is used.
The witness was discovered from the GAP words recorded by the M11 degree-twelve
recognition investigation. All permutations use Lean's left-action convention.
See `IndexTwelve.lean` for the cardinality and normal-generation argument.
-/

open scoped Pointwise

namespace Sporadic.Mathieu.M11IndexTwelveCertificate

@[expose] public section

def sPerm : Equiv.Perm (Fin 11) :=
  Equiv.swap (0 : Fin 11) 10 * Equiv.swap (3 : Fin 11) 5 *
    Equiv.swap (6 : Fin 11) 7 * Equiv.swap (8 : Fin 11) 9

/-- The native word that realizes the additional involution. -/
def involutionWord {G : Type*} [Group G] (a b : G) : G :=
  b⁻¹ * (b⁻¹ * a⁻¹) ^ 2 * (b ^ 2 * a) ^ 2 * (b⁻¹ * a) ^ 2 * b⁻¹

set_option maxRecDepth 4096 in
theorem involutionWord_eq : involutionWord m11GeneratorA m11GeneratorB = sPerm := by
  ext x
  fin_cases x <;> rfl

set_option maxRecDepth 4096 in
theorem normal_generation_word :
    sPerm = (m11GeneratorA * m11GeneratorB) ^ 2 *
      (sPerm⁻¹ * (m11GeneratorA * m11GeneratorB) * sPerm) *
      ((m11GeneratorA * m11GeneratorB) ^ 2)⁻¹ *
      ((sPerm⁻¹ * (m11GeneratorA * m11GeneratorB) * sPerm) ^ 2)⁻¹ *
      (m11GeneratorA * m11GeneratorB) := by
  ext x
  fin_cases x <;> rfl

set_option maxRecDepth 4096 in
theorem complement_word :
    m11GeneratorA * m11GeneratorB⁻¹ * m11GeneratorA *
      m11GeneratorB * m11GeneratorB * m11GeneratorA *
      m11GeneratorB⁻¹ * m11GeneratorA * m11GeneratorB *
      m11GeneratorB * m11GeneratorA * m11GeneratorB⁻¹ *
      m11GeneratorA * m11GeneratorB⁻¹ * m11GeneratorA * m11GeneratorB⁻¹ =
    (m11GeneratorA * m11GeneratorB) * sPerm * (m11GeneratorA * m11GeneratorB)⁻¹ * sPerm*
      (m11GeneratorA * m11GeneratorB) * sPerm⁻¹ * ((m11GeneratorA * m11GeneratorB) ^ 2)⁻¹*
      sPerm⁻¹ * (m11GeneratorA * m11GeneratorB)⁻¹ := by
  ext x
  fin_cases x <;> rfl

def blocks : Finset (Finset (Fin 11)) :=
  {{0, 1, 2, 3, 8}, {0, 1, 4, 7, 9}, {0, 2, 6, 7, 10}, {0, 3, 4, 5, 10},
   {0, 5, 6, 8, 9}, {1, 2, 5, 9, 10}, {1, 3, 5, 6, 7}, {1, 4, 6, 8, 10},
   {2, 3, 4, 6, 9}, {2, 4, 5, 7, 8}, {3, 7, 8, 9, 10}}

theorem c_blocks : (m11GeneratorA * m11GeneratorB) • blocks = blocks := by
  decide +kernel

theorem s_blocks : sPerm • blocks = blocks := by
  decide +kernel

/-- Words representing twelve distinct translates of the block collection. -/
def reps {G : Type*} [Group G] (a b : G) : Fin 12 → G
  | 0 => 1
  | 1 => a
  | 2 => b * a
  | 3 => a * b * a
  | 4 => b * b * a
  | 5 => b * a * b * a
  | 6 => b * b * a * b * a
  | 7 => b * b * b * a * b * a
  | 8 => a * b * b * b * a * b * a
  | 9 => b * a * b * b * b * a * b * a
  | 10 => a * b * a * b * b * b * a * b * a
  | 11 => b * a * b * a * b * b * b * a * b * a

theorem reps_blocks_injective :
    Function.Injective (fun i => reps m11GeneratorA m11GeneratorB i • blocks) := by
  decide +kernel

end
end Sporadic.Mathieu.M11IndexTwelveCertificate
