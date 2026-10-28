module
public import Theory.SpecificGroups.ReeF4.NormalizedRootCentralizers.CenterExponent.ElementaryTail
public import Theory.SpecificGroups.ReeF4.NormalizedRootCentralizers.CenterExponent.MiddleElimination
public import Theory.SpecificGroups.ReeF4.NormalizedRootCentralizers.CenterExponent.OuterElimination
/-!
# The full positive Ree center has exponent two

Unique fixed positive coordinates reduce a central element of the actual Ree
model to a literal product of the eight relative root blocks. Centrality gives
commutation with every main root curve. Two scalar calculations suffice:
first remove x₈, x₂, x₁, x₇ and y₁; then remove the remaining main B₂ parameters
x₅ and x₃. The remaining five curves lie in the independently proved elementary
split-root tail, so the original model element has square one.

The two independent coordinate eliminations are discharged below, giving
`unipotent_center_sq` for `m > 0`, with coefficient field of order
`2^(2*m+1)`. This supplies exactly the `hexp` argument of
`ReeF4.NormalizedRootCentralizers.center_eq_of_central_involutions`, without
using central-involution classification or a prior center identification.
The full center identification and Borel rigidity assembly remain in the parent
module, which may import this module without a cycle. The original conditional
coordinate-elimination interface is preserved.

Source: Aschbacher–Smith, proof of 13.6.6, printed p.927, with A.2.3–4;
GLS3 Table 2.4 and 2.4.5(d), `refs/KGroup/GLS3/chapter2.tex`.
-/

public section
namespace ReeF4.NormalizedRootCentralizers.CenterExponent
open Parabolics Parabolics.RadicalCoordinates.FixedCoordinates
open Parabolics.OuterLocal.SuzukiCommutators.NormalGeneration

/-- The exact exponent premise used by the full-center assembly, conditional
on the two scalar-coordinate eliminations. -/
theorem unipotent_center_sq_of_coordinate_elimination (m : ℕ)
    (houter : ∀ p : PositiveParameters m,
      (∀ i : Fin 8, ∀ t : CoefficientField m,
        Commute (positiveWord m p) (rootWord m i t)) → OuterCoordinatesZero p)
    (hmiddle : ∀ p : PositiveParameters m, OuterCoordinatesZero p →
      (∀ i : Fin 8, ∀ t : CoefficientField m,
        Commute (positiveWord m p) (rootWord m i t)) → p.main 1 = 0 ∧ p.main 3 = 0)
    (x : Model m) (hx : x ∈ unipotent m)
    (hc : ∀ u ∈ unipotent m, Commute x u) : x ^ 2 = 1 := by
  obtain ⟨p, hp, _⟩ := existsUnique_positiveWord m x hx
  have hcomm := positiveWord_commutes_of_central m x hc p hp
  have ho := houter p hcomm
  obtain ⟨hm1, hm3⟩ := hmiddle p ho hcomm
  apply toSplitGroup_injective m
  rw [map_pow, map_one, hp]
  apply positiveWord_sq_of_coordinate_vanishing m p
  · intro j hj
    change Fin 4 at j
    fin_cases j
    · exact ho.pair_eighth
    · exact ho.pair_second
    · simp [positive_pair_indices] at hj
    · simp [positive_pair_indices] at hj
  · intro j
    fin_cases j
    · exact ho.main_first
    · exact hm1
    · exact ho.main_seventh
    · exact hm3
  · intro j hj
    change Fin 4 at j
    fin_cases j
    · exact ho.central_first
    all_goals simp [positive_quartet_indices] at hj

/-- Every element central in the genuine positive Ree subgroup has square one.
Both coordinate-elimination premises are discharged by root commutator
calculations. This is the `hexp` premise of the full-center identification. -/
theorem unipotent_center_sq (m : ℕ) (hm : 0 < m)
    (x : Model m) (hx : x ∈ unipotent m)
    (hc : ∀ u ∈ unipotent m, Commute x u) : x ^ 2 = 1 :=
  unipotent_center_sq_of_coordinate_elimination m
    (outerCoordinatesZero_of_commute m) (middle_coordinates_zero m hm) x hx hc

end ReeF4.NormalizedRootCentralizers.CenterExponent
