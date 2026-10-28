module

public import Theory.SpecificGroups.Thompson.Model.GeneratorCertificates
public import Mathlib.Data.Fin.VecNotation

/-!
# Proposed prime-order representatives for the Thompson matrix model

These are words in the certified ATLAS generators from the conjugacy-class
table for Th. The entries correspond to 2A, 3A, 3B, 3C, 5A, 7A, 13A, 19A,
and 31A-B. The table relates 31A and 31B by taking a third power, so one
representative meets both cyclic classes. These are definitions only: neither
their asserted orders nor class coverage is imported from the source.

Source: https://brauer.maths.qmul.ac.uk/Atlas/v3/spor/Th/ , conjugacy-class
table, standard-generator words (R. A. Wilson, S. J. Nickerson, J. N. Bray).
-/

@[expose] public section

namespace Thompson.Simplicity

/-- Evaluate a positive word in the two fixed generators. -/
def word (s : String) : Model :=
  (s.toList.map fun c => if c = 'a' then generatorA else if c = 'b' then generatorB else 1).prod

/-- The commutator convention used by the ATLAS word table. -/
def commutatorWord (x y : Model) : Model := x⁻¹ * y⁻¹ * x * y

/-- Nine candidates meeting the prime-order cyclic classes of the published
Thompson group. Coverage for the concrete matrix group is a separate theorem. -/
def primeRepresentative : Fin 9 → Model :=
  ![generatorA,
    generatorB,
    (generatorA * generatorB * generatorA * generatorB * generatorA * generatorB ^ 2) ^ 6,
    commutatorWord generatorA
      (generatorB * generatorA * generatorB * generatorA * generatorB) ^ 2,
    commutatorWord generatorA generatorB ^ 2,
    (generatorA * generatorB) ^ 6 * (generatorA * generatorB ^ 2) ^ 6,
    (generatorA * generatorB) ^ 9 * (generatorA * generatorB ^ 2) ^ 3,
    generatorA * generatorB,
    word "abababababababbabbabababababbababababababababb"]

end Thompson.Simplicity
