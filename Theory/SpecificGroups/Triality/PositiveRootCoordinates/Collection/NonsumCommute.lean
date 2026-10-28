module

public import Theory.SpecificGroups.Triality.PositiveRootCoordinates.Collection.Relations
public import Theory.SpecificGroups.Triality.PositiveRootCoordinates.Collection.NonsumCommute.Geometry
public import Theory.SpecificGroups.Triality.PositiveRootCoordinates.Collection.NonsumCommute.Transport
public import Theory.AlgebraicGroup.RootSystems.TypeD4Irreducible

/-!+# Commutation of positive canonical Geck curves with absent root sum

A finite D4 root calculation realizes each distinct non-sum positive pair as
a common Weyl translate of distinct, oppositely signed simple roots. The
integral Geck operators commute on those simple roots; rational root-space
comparison transfers the identity to the actual canonical operators. Integral
factorial cancellation then gives commutation of their divided powers and hence
of their specialized curves. The argument works for every parameter field,
in particular for every binary parameter, including n = 1.

This proves the complementary local identity required by positive-word
collection. Source: GLS3 2.3.6–7 and §§2.4–2.6
(`refs/KGroup/GLS3/chapter2.tex`).
-/

public section
noncomputable section

open Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction
namespace Triality.Standard.PositiveCoordinates

/-- Distinct positive canonical curves commute whenever their root sum is absent. -/
theorem nonsumCommute_parameters (P : Parameters) : NonsumCommute P := by
  let := typeD4RootPairing_isIrreducible
  intro i j hij hsum a b
  obtain ⟨w, l, r, hlr, hwi, hwj⟩ := NonsumGeometry.common_signed_route i j hij hsum
  have h := rootOperator_commute_of_common_signed_route
    (rootIndex i) (rootIndex j) (rootIndex_positive i) (rootIndex_positive j)
    w l r hlr hwi hwj
  apply Subtype.ext
  exact (rootCurveUnit_commute_of_operator_commute h a b).eq

/-- The non-sum commuting identity for all binary triality parameters. -/
theorem nonsumCommute_binary (n : ℕ) (hn : 0 < n) :
    NonsumCommute (binaryParameters n hn) :=
  nonsumCommute_parameters (binaryParameters n hn)

end Triality.Standard.PositiveCoordinates
