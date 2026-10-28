module

public import Theory.SpecificGroups.MacWilliams.SylowPresentations

/-!+# Quadratic frames for the unitary presentation

A quadratic frame specifies generators for an elementary central quotient and
its center in the coordinates of `unitaryTable`. The quotient coordinates of
the last two generators are trivial; the central coordinates of the first four
are trivial. Squares and polar values are the exact words of the presentation,
so lifting such a frame retains the presentation's commutator convention.

This is the interface between the classification of the square map and group
recognition in the unitary alternative of Janko–Thompson, Math. Z. 113 (1970),
Theorem 1.3(b), p.386, citing MacWilliams, Trans. AMS 150 (1970).
-/

namespace MacWilliamsSylow

/-- Coordinates for a square map and its polar map matching the published
six-generator unitary table, with zero-based indices. -/
public structure UnitaryQuadraticFrame
    {V W : Type*} [Group V] [Group W]
    (square : V → W) (polar : V → V → W) where
  quotientGenerator : Fin 6 → V
  centralGenerator : Fin 6 → W
  quotient_last : ∀ i, 4 ≤ i.val → quotientGenerator i = 1
  central_first : ∀ i, i.val < 4 → centralGenerator i = 1
  quotient_closure : Subgroup.closure (Set.range quotientGenerator) = ⊤
  central_closure : Subgroup.closure (Set.range centralGenerator) = ⊤
  square_eq : ∀ i, square (quotientGenerator i) =
    word centralGenerator (unitaryTable.square i)
  polar_eq : ∀ i j, i < j → polar (quotientGenerator j) (quotientGenerator i) =
    word centralGenerator (unitaryTable.commutator j i)

end MacWilliamsSylow
