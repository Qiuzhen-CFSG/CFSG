module

public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.Reduction

/-!
# Marked odd-prime generation for the J₄ Sylow-overgroup argument

Let P be a Sylow two-subgroup of the full centralizer of the original
matrix involution a. Its image in J₄ is already certified to be Sylow.
The contracts below ask that adjoining an odd-prime-order element inverted
by a generates J₄. They concern every such element and every such P,
not just chosen ATLAS words or a subgroup labelled by an extension shape.

Baer–Suzuki turns these generation statements into the required nontrivial
intrinsic two-core, as proved in the parent `CoreExistence` module. The
split is by the nine odd prime divisors of the certified ambient order.
Neither generation statement is asserted here.

Source context: Aschbacher–Smith A.1.2 and the sporadic Sylow-overgroup
step of A.3.12, printed pp.47–48, citing Aschbacher (1986), Memoirs AMS
60, no.343; Kleidman–Wilson (1988), pp.484–510. This is a sufficient
generation route to the cited exhaustion, not an assumed subgroup table.
-/

public section

open Subgroup

namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover

/-- The marked generation assertion for an explicit set of odd primes. -/
@[expose] def CentralOddPrimeGeneration (primes : Finset ℕ) : Prop :=
  ∀ (P : Sylow 2 (centralizer ({Janko4.a} : Set Janko4.Model)))
    (q : ℕ), q ∈ primes → ∀ r : Janko4.Model,
      orderOf r = q → (MulAut.conj Janko4.a) r = r⁻¹ →
      closure (insert r
        ((P : Subgroup (centralizer ({Janko4.a} : Set Janko4.Model))).map
          (centralizer ({Janko4.a} : Set Janko4.Model)).subtype : Set Janko4.Model)) = ⊤

/-- The primes occurring in the two centralizer orders. No generation proof
for these primes is implicit in the centralizer certificates. -/
@[expose] def CentralSmallPrimeGeneration : Prop :=
  CentralOddPrimeGeneration {3, 5, 7, 11}

/-- The remaining odd primes dividing the certified J₄ order. -/
@[expose] def CentralLargePrimeGeneration : Prop :=
  CentralOddPrimeGeneration {23, 29, 31, 37, 43}

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover
