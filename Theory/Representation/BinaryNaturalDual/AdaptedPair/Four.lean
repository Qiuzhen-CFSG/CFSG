module

public import Theory.Representation.BinaryNaturalDual.AdaptedPair.Geometry
public import Theory.Representation.BinaryNaturalDual.AdaptedPair.Four.Coordinates
public import Theory.Representation.BinaryNaturalDual.AdaptedPair.Four.FixedSpaces
public import Theory.Representation.BinaryNaturalDual.AdaptedPair.Four.UpperSylow
public import Theory.Representation.BinaryNaturalDual.AdaptedPair.Four.PointSylow
public import Theory.Representation.BinaryNaturalDual.ModelOrbits.Coordinate

/-!
# Standard four-dimensional adapted-pair geometry

For the nonsingular vector (e₃,e₂*+e₃*), the geometric moving module has a
one-dimensional fixed space under its stabilizer in the actual standard
upper/graph group. It equals the fixed line of that whole standard group.
An explicit inner point stabilizer moves this line. The actual upper/graph
semidirect product has order 128, and its point intersection has order 16.
The inner part of that intersection acts as the full upper group on the
kernel with basis e₁,e₂+e₃,e₄.

`standard_coordinates` combines these calculations into every standard input
of the adapted-pair transport. It discharges the point-Sylow calculation's
normal-form premise using the upper/graph semidirect product, and supplies
inner transitivity from the actual natural-plus-dual action. Its only inputs
are the specified coordinate action, inner index two, and point-stabilizer
order 336. Construction of these model inputs and arbitrary-pair transport
remain with the source-theorem assembly.

Source: the corrected adapted-pair form of Aschbacher–Smith H.9.1(4),
printed p.390, needed by 12.1.1 and 12.1.3.
-/

public section
namespace BinaryNaturalDual.AdaptedPair.Four

/-- The fixed-space equality in the standard adapted-pair contract. -/
theorem moving_fixedVectors_eq_standard (d : CoordinateAction 4) :
    movingSpace vectorFour ⊓ fixedVectors (linearAction d)
      (standardGroup 4 ⊓ pointStabilizer (linearAction d) vectorFour) =
        fixedVectors (linearAction d) (standardGroup 4) := by
  rw [moving_fixedVectors_intersection, fixedVectors_standard]

/-- The actual standard fixed space has binary dimension one. -/
theorem finrank_fixedVectors_standard (d : CoordinateAction 4) :
    Module.finrank (ZMod 2) (fixedVectors (linearAction d) (standardGroup 4)) = 1 := by
  rw [fixedVectors_standard]
  exact finrank_fixedVector_span 4

/-- All standard-coordinate inputs for the corrected adapted-pair transport
in dimension four. The Sylow intersection, outer witness, fixed-line equality,
dimension and inner movement are conclusions of the coordinate calculation.
In particular the point-Sylow normal form is discharged here. -/
theorem standard_coordinates (d : CoordinateAction 4)
    (hindex : (innerGroup 4).index = 2)
    (hcard : Nat.card (pointStabilizer (linearAction d) vectorFour) = 336) :
    ∃ S : Sylow 2 (MulAut (BinaryLinear.OuterCyclic.LinearGroup 4)),
    ∃ P : Sylow 2 (pointStabilizer (linearAction d) vectorFour),
      (S : Subgroup _) = standardGroup 4 ∧
      quadratic vectorFour = 1 ∧
      (∀ v : CoordinateSpace 4, quadratic v = 1 →
        ∃ l ∈ innerGroup 4, linearAction d l v = vectorFour) ∧
      (P : Subgroup (pointStabilizer (linearAction d) vectorFour)).map
        (pointStabilizer (linearAction d) vectorFour).subtype =
          (S : Subgroup _) ⊓ pointStabilizer (linearAction d) vectorFour ∧
      (∃ s : pointStabilizer (linearAction d) vectorFour,
        s ∈ (P : Subgroup _) ∧
          (s : MulAut (BinaryLinear.OuterCyclic.LinearGroup 4)) ∉ innerGroup 4) ∧
      movingSpace vectorFour ⊓ fixedVectors (linearAction d)
        ((S : Subgroup _) ⊓ pointStabilizer (linearAction d) vectorFour) =
          fixedVectors (linearAction d) S ∧
      Module.finrank (ZMod 2) (fixedVectors (linearAction d) S) = 1 ∧
      ∃ a ∈ innerGroup 4, linearAction d a vectorFour = vectorFour ∧
        ∃ z ∈ fixedVectors (linearAction d) S, linearAction d a z ≠ z := by
  refine ⟨UpperSylow.standardSylow d hindex,
    PointSylow.pointSylow d (UpperSylow.normal_form d) hcard,
    UpperSylow.standardSylow_coe d hindex, ?_⟩
  rw [UpperSylow.standardSylow_coe]
  refine ⟨quadratic_vectorFour, ?_,
    PointSylow.pointSylow_map d (UpperSylow.normal_form d) hcard,
    ?_, moving_fixedVectors_eq_standard d, finrank_fixedVectors_standard d,
    inner_stabilizer_moves_fixedVector d⟩
  · intro v hv
    obtain ⟨g, hg⟩ := ModelOrbits.exists_inner_eq_of_pairing_one d hv quadratic_vectorFour
    exact ⟨MulAut.conj g, ⟨g, rfl⟩, hg⟩
  · exact ⟨⟨outerFour, outerFour_fixes_vectorFour d⟩,
      PointSylow.outerFour_mem_pointSylow d (UpperSylow.normal_form d) hcard,
      outerFour_not_inner d⟩

end BinaryNaturalDual.AdaptedPair.Four
