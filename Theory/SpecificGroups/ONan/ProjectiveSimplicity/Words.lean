module

public import Theory.SpecificGroups.ONan.MatrixModel

/-!
# Prime-order representative words for the O'Nan matrix group

The straight-line program `ONG1-cycW1` from the ATLAS of Finite Group
Representations is evaluated on the actual projective matrix generators.
Its source labels are 7B, 11A, 12A, 15AB, 16AB, 16CD, 19ABC, 20AB, 28AB,
and 31AB. Appropriate powers, together with the first standard generator,
give eight candidates for prime-order cyclic classes.

These definitions assert neither element orders nor conjugacy coverage.
Those are separate certification obligations for this fixed matrix subgroup.

Source: R. A. Wilson, R. A. Parker, J. N. Bray and the ATLAS contributors,
https://brauer.maths.qmul.ac.uk/Atlas/spor/ON/words/ONG1-cycW1
(accessed 2026-10-03). The source program is preserved alongside this module.
-/

@[expose] public section

namespace ONan.Simplicity

/-- Evaluate the ATLAS cyclic-class program in any group, in its output order. -/
def cyclicWords {G : Type*} [Group G] (a b : G) : Fin 10 → G :=
  let w11 := a * b
  let w19 := w11 * b
  let w20 := w11 * w19
  let w12 := w20 * b
  let aux := w11 * w20
  let w31 := aux * w19
  let w28 := w12 * aux
  let w16ab := aux * w28
  let w16cd := w19 * w16ab
  let w7 := w12 * w16cd
  let w15 := w7 * w28
  ![w7, w11, w12, w15, w16ab, w16cd, w19, w20, w28, w31]

/-- Candidates labelled 2A, 3A, 5A, 7A, 7B, 11A, 19ABC and 31AB.
The labels describe the source, not a proved identification. -/
def primeRepresentative : Fin 8 → Model :=
  let w := cyclicWords generatorA generatorB
  ![generatorA, w 2 ^ 4, w 7 ^ 4, w 8 ^ 4, w 0, w 1, w 6, w 9]

end ONan.Simplicity
