module

public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.QuadraticSplitting.AxisGeometry.Generation
public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.QuadraticSplitting.AxisGeometry.Generation.RootLines

/-!
# Discharging the root-line premise of axis generation

The original marked root groups have now been identified with the parameter
lines. Substituting that theorem in the generation and quadraticity arguments
leaves only the independent full-Levi pair transports to be constructed.

Source: Aschbacher–Smith B.4.9(1), printed pp.92–93, combined manuscript
of 1 March 2004. Unconditional generation remains with the full-Levi assembly.
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

/-- The full-Levi transports are the remaining matrix premise of axis generation. -/
theorem axisGeneration_of_levi (ht : m.LeviPairTransports j)
    (hf : SourceFamily F n) (E : Subgroup G) (hE : IsAxisFour d E)
    (hEQ : E ≤ m.Q j) (hroot : n = 3 → ¬ InRootGroup d E) :
    AxisGeneration d E (m.Q j) := by
  have hn : 3 ≤ n := by rcases hf with h | ⟨_, h⟩ <;> omega
  exact m.axisGeneration_of_levi_and_roots j ht (m.rootLineDescription j hn) hf E hE hEQ hroot

/-- The root-line obligation in quadratic propagation is discharged by the original marking. -/
theorem axis_quadratic_of_levi (ht : m.LeviPairTransports j)
    (h : SourceHypotheses d) (E : Subgroup G) (hE : IsAxisFour d E)
    (hEQ : E ≤ m.Q j) (hroot : n = 3 → ¬ InRootGroup d E)
    (hquad : IsQuadratic ρ E) : IsQuadratic ρ (m.Q j) :=
  axis_quadratic d h E (m.Q j) hquad
    (m.axisGeneration_of_levi j ht h.family E hE hEQ hroot)

end QuotientCoordinates
end CFSG.Quasithin.ChapterB.NaturalExtensions.QuadraticSplitting
