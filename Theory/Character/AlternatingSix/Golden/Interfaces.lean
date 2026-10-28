module

public import Theory.Character.AlternatingSix.Blocks

/-!
# Inputs to the complementary-character construction for A₆

The principal character and the four rational characters leave two columns of
an irreducible-character basis. `RationalCompletion` asks for those actual
representation characters and the residual second-orthogonality identity; it
prescribes neither their degrees nor any of their values. `GoldenClassGeometry`
records the separate, purely group-theoretic calculation on the actual A₆.

The consumer in `Golden` derives both degree-eight rows, including their
quadratic values and the interchange at the square of a five-element.

Source: Janko, *A characterization of the Mathieu simple groups, I* (1968),
§6, pp.10–11; ordinary character completeness and column orthogonality.
-/

noncomputable section
open scoped BigOperators
namespace Theory.Character.AlternatingSix

/-- The column product contributed by the five known rational characters. -/
@[expose] public def rationalColumn {c : alternatingGroup (Fin 6)} (R : RationalBlock c)
    (x y : alternatingGroup (Fin 6)) : ℂ :=
  1 + ∑ j, R.character j x * star (R.character j y)

/-- The two genuine irreducibles complementary to the five known rows.
No degree or character-table entry is part of this interface. -/
public structure RationalCompletion {c : alternatingGroup (Fin 6)} (R : RationalBlock c) where
  character : Fin 2 → ClassFunction (alternatingGroup (Fin 6))
  irreducible : ∀ j, IsIrreducibleCharacter (character j)
  column : ∀ x y,
    character 0 x * star (character 0 y) + character 1 x * star (character 1 y) =
      (if IsConj x y then (Nat.card (Subgroup.centralizer ({x} : Set _)) : ℂ) else 0) -
        rationalColumn R x y

/-- Only the intrinsic class calculations used by the golden rows.
The class count is used to construct `RationalCompletion`; the remaining
fields determine its values. -/
public structure GoldenClassGeometry : Prop where
  class_count : Nat.card (ConjClasses (alternatingGroup (Fin 6))) = 7
  centralizer_two : ∀ x : alternatingGroup (Fin 6), orderOf x = 2 →
    Nat.card (Subgroup.centralizer ({x} : Set _)) = 8
  centralizer_three : ∀ x : alternatingGroup (Fin 6), orderOf x = 3 →
    Nat.card (Subgroup.centralizer ({x} : Set _)) = 9
  centralizer_four : ∀ x : alternatingGroup (Fin 6), orderOf x = 4 →
    Nat.card (Subgroup.centralizer ({x} : Set _)) = 4
  centralizer_five : ∀ x : alternatingGroup (Fin 6), orderOf x = 5 →
    Nat.card (Subgroup.centralizer ({x} : Set _)) = 5
  five_inverse : ∀ x : alternatingGroup (Fin 6), orderOf x = 5 → IsConj x x⁻¹
  five_square : ∀ x : alternatingGroup (Fin 6), orderOf x = 5 → ¬ IsConj x (x ^ 2)

end Theory.Character.AlternatingSix
