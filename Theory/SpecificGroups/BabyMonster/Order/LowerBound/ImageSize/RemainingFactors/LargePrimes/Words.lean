module

public import Theory.SpecificGroups.BabyMonster.Order.LowerBound.ImageSize.RemainingFactors.Assembly

/-!
# Fixed words for the seven larger prime divisors

These are the literal ATLAS candidate words recorded in
`RemainingFactors/source/README.md`, expanded to include their indicated powers.
False denotes `a`, true denotes `b`; products act left to right on row vectors.
No order or orbit assertion is made by this transcription.

Source: ATLAS of Finite Group Representations, Baby Monster class representatives,
https://brauer.maths.qmul.ac.uk/Atlas/v3/spor/B/ .
-/

@[expose] public section

namespace BabyMonster.OrderLowerBound.RemainingFactors.LargePrimes

/-- The candidate `ab` raised to power `5`. -/
def word11 : List Bool :=
  [false, true, false, true, false, true, false, true, false, true]

/-- The candidate `ababababbabababbababb` raised to power `2`. -/
def word13 : List Bool :=
  [false, true, false, true, false, true, false, true, true, false, true, false, true, false, true, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, true, true, false, true, false, true, true]

/-- The candidate `abababbabababbab` raised to power `2`. -/
def word17 : List Bool :=
  [false, true, false, true, false, true, true, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, true, true, false, true]

/-- The candidate `ababababbababbababababbababbabb` raised to power `2`. -/
def word19 : List Bool :=
  [false, true, false, true, false, true, false, true, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, true, false, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, true, false, true, true]

/-- The candidate `abababababbababbabbabb` raised to power `2`. -/
def word23 : List Bool :=
  [false, true, false, true, false, true, false, true, false, true, true, false, true, false, true, true, false, true, true, false, true, true, false, true, false, true, false, true, false, true, false, true, true, false, true, false, true, true, false, true, true, false, true, true]

/-- The candidate `ababababbababb` raised to power `1`. -/
def word31 : List Bool :=
  [false, true, false, true, false, true, false, true, true, false, true, false, true, true]

/-- The candidate `abababbababababbababb` raised to power `1`. -/
def word47 : List Bool :=
  [false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, true]

end BabyMonster.OrderLowerBound.RemainingFactors.LargePrimes
