module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour.SourceLocal.SixCoordinates
public import CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour.At.EnlargedSwapping

/-!
# Literal six-dimensional coordinates in the remaining swapping case at the original G,T

The elementary product B=A C_G(L) is identified with the binary four-space
and a binary plane. Multiplication retains both ambient factors. Every actor
in the marked parabolic centralizes the second factor, so its image is the
specified parabolic extended by the identity. The corrected cubic rotates
the same common four-group and moves both coordinate factors.

This extension specializes the existing source argument to the actual
`HigherRankHypothesis` and to `Structural1222At` and `Theorem12213At`.
The universal interfaces remain unchanged. Earlier Chapter 12 inputs keep
their original producers; final recognition still requires I.4.5.
Source: Aschbacher–Smith, 14.4.3–5, printed pp.1006–1008.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour.At
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative Pointwise commutatorElement
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section03.CaseOneSource CaseOneGeometry DimensionFour.SplitImage
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G]

variable [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The source local-data constructor has only the concrete finite-action
obstruction left; no ambient normalizer or coordinate callback is assumed. -/
theorem source_localData_or_six_dimensional_swapping
    (d : Counterexample T L) (setup : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hcard : Nat.card F.U = 32) :
    Nonempty (SourceLocalData L F) ∨ SixDimensionalSwappingCase := by
  rcases source_localData_or_enlarged_swapping d setup structural alternatives F hne hZ hcard with
    hd | hs
  · exact Or.inl hd
  · exact Or.inr (sixDimensionalSwappingCase_of_enlarged F hs)

end CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour.At
