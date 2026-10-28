module

public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.QuadraticSplitting.AxisGeometry.Generation.LeviTransports
public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.QuadraticSplitting.AxisGeometry.Generation

/-!
# Applying full Levi transports to axis generation

The constructed simultaneous conjugators discharge `LeviPairTransports` in
the existing generation proof for B.4.9(1), printed pp.92–93. Identification
of original root groups with parameter lines remains the independent input;
all coordinates, shears and conjugations use the supplied quotient marking.
-/

public section

open Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterB.QuasisimpleSource

namespace CFSG.Quasithin.ChapterB.NaturalExtensions.QuadraticSplitting
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {F : BinaryField} {n : ℕ} {ρ : Representation (ZMod 2) G V}
  {d : DoubleNatural F n ρ}
namespace QuotientCoordinates
variable (m : QuotientCoordinates d) (j : Fin n)

/-- The full Levi discharges the pair-transport premise in axis generation.
Only identification of the original root groups remains an independent input. -/
theorem axisGeneration_of_roots (hr : m.RootLineDescription j)
    (hf : SourceFamily F n) (E : Subgroup G) (hE : IsAxisFour d E)
    (hEQ : E ≤ m.Q j) (hroot : n = 3 → ¬ InRootGroup d E) :
    AxisGeneration d E (m.Q j) :=
  m.axisGeneration_of_levi_and_roots j (m.leviPairTransports j) hr hf E hE hEQ hroot

end QuotientCoordinates
end CFSG.Quasithin.ChapterB.NaturalExtensions.QuadraticSplitting
