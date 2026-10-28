module

public import CFSG.Quasithin.ChapterK.Section01To04.Exceptional.G2CubicDegree.BinaryObstruction.Involutions.OddElements.Representatives
public import CFSG.Quasithin.ChapterK.Section01To04.Exceptional.G2CubicDegree.BinaryObstruction.Involutions.OddElements.CycleCertificates.Minors

/-!
# Certified odd-word displacement on both degree-32 incidence-cycle factors

The kernel-checked minor witnesses give rank at least ten for `AB - I` and
at least twelve for `A - B` on each factor. Conjugation by the actual cycle
coordinates preserves these ranks. The established inverse-free identity
then gives the required displacement at the marked words `a*b` and `a*b⁻¹`.

Both factors are the literal subspace and quotient of the incidence kernel.
Their actors are `VertexCoordinates.groupGenerator`, as in `groupHom`;
the proof uses the existing generator-action equations on those spaces.
The unconditional `cycleSamples` supplies the numerical input to the odd
factor assembly. Global conjugacy coverage remains explicit in the consumer.

Source: Guralnick–Malle, Classification of 2F-modules I, Proposition 4.3,
pp.10–11. These degree-32 calculations extend the source's argument beyond
its prior offender-based exclusion, without assuming absolute irreducibility.
-/

public section

namespace CFSG.Quasithin.ChapterK.Exceptional.G2CubicDegree.BinaryObstruction.Involutions.OddElements
open G2DerivedPermutationFiltration
open G2DerivedPermutationFiltration.VertexCoordinates

section Coordinates
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

private theorem coordinate_rank (e : V ≃ₗ[ZMod 2] CycleData.Half) (T : Module.End (ZMod 2) V) :
    (LinearMap.toMatrix' (e.conj T)).rank =
      Module.finrank (ZMod 2) (LinearMap.range T) := by
  change Module.finrank (ZMod 2)
    (LinearMap.range (Matrix.toLin' (LinearMap.toMatrix' (e.conj T)))) = _
  rw [Matrix.toLin'_toMatrix', LinearEquiv.conj_apply,
    LinearMap.range_comp_of_range_eq_top _ e.symm.range, LinearMap.range_comp]
  exact (Submodule.equivMapOfInjective e.toLinearMap e.injective
    (LinearMap.range T)).finrank_eq.symm

private theorem coordinate_mul_sub (e : V ≃ₗ[ZMod 2] CycleData.Half)
    (A B : Module.End (ZMod 2) V) :
    LinearMap.toMatrix' (e.conj (A * B - LinearMap.id)) =
      LinearMap.toMatrix' (e.conj A) * LinearMap.toMatrix' (e.conj B) - 1 := by
  have hm : e.conj (A * B) = e.conj A * e.conj B := e.conj_comp B A
  rw [map_sub, map_sub, LinearEquiv.conj_id, LinearMap.toMatrix'_id,
    hm, LinearMap.toMatrix'_mul]

private theorem coordinate_bounds
    (ρ : Representation (ZMod 2) Group V)
    (e : V ≃ₗ[ZMod 2] CycleData.Half) (f : Fin 2)
    (ha : ∀ j, LinearMap.toMatrix' (e.conj (ρ (groupGenerator j))) = CycleData.factorMatrix f j)
    (hthree : 10 ≤ (CycleData.factorMatrix f 0 * CycleData.factorMatrix f 1 - 1).rank)
    (hseven : 12 ≤ (CycleData.factorMatrix f 0 - CycleData.factorMatrix f 1).rank) :
    RepresentativeBounds ρ (groupHom regularWord) (groupHom sevenWord) := by
  let : FiniteDimensional (ZMod 2) V :=
    FiniteDimensional.of_injective e.toLinearMap e.injective
  simp only [regularWord, sevenWord, map_mul, map_inv, groupHom_of]
  apply representativeBounds_of_generator_ranks
  · rw [← coordinate_rank e, coordinate_mul_sub, ha, ha]
    exact hthree
  · rw [← coordinate_rank e, map_sub, map_sub, ha, ha]
    exact hseven

/-- Keep the ambient space abstract when applying coordinates to a nested
subrepresentation, as in the existing cycle matrix-algebra criterion. -/
private theorem subspace_coordinate_bounds
    (ρ : Representation (ZMod 2) Group V) (S : Subrepresentation ρ)
    (e : S.toSubmodule ≃ₗ[ZMod 2] CycleData.Half) (f : Fin 2)
    (ha : ∀ j, LinearMap.toMatrix' (e.conj (S.toRepresentation (groupGenerator j))) =
      CycleData.factorMatrix f j)
    (hthree : 10 ≤ (CycleData.factorMatrix f 0 * CycleData.factorMatrix f 1 - 1).rank)
    (hseven : 12 ≤ (CycleData.factorMatrix f 0 - CycleData.factorMatrix f 1).rank) :
    RepresentativeBounds (V := S.toSubmodule) S.toRepresentation
      (groupHom regularWord) (groupHom sevenWord) :=
  coordinate_bounds S.toRepresentation e f ha hthree hseven

end Coordinates

/-- Normalize the actor before specializing the coordinate record. This keeps
elaboration from unfolding the large concrete subspace construction. -/
private theorem subspace_action_at_generators (c : CycleCoordinates)
    (hc : c.actor = groupGenerator) (j : Fin 2) :
    LinearMap.toMatrix' (c.subspaceCoordinates.conj
      (c.half.toRepresentation (groupGenerator j))) = CycleData.factorMatrix 0 j := by
  exact Eq.mp (congrArg (fun x : Group =>
    LinearMap.toMatrix' (c.subspaceCoordinates.conj (c.half.toRepresentation x)) =
      CycleData.factorMatrix 0 j) (congrFun hc j)) (c.subspace_action j)

private theorem quotient_action_at_generators (c : CycleCoordinates)
    (hc : c.actor = groupGenerator) (j : Fin 2) :
    LinearMap.toMatrix' (c.quotientCoordinates.conj
      (c.half.quotientRepresentation (groupGenerator j))) = CycleData.factorMatrix 1 j := by
  exact Eq.mp (congrArg (fun x : Group =>
    LinearMap.toMatrix' (c.quotientCoordinates.conj (c.half.quotientRepresentation x)) =
      CycleData.factorMatrix 1 j) (congrFun hc j)) (c.quotient_action j)

private theorem half_samples (c : CycleCoordinates) (hc : c.actor = groupGenerator) :
    RepresentativeBounds (V := c.half.toSubmodule) c.half.toRepresentation
      (groupHom regularWord) (groupHom sevenWord) :=
  subspace_coordinate_bounds cycleSubrepresentation.toRepresentation c.half
    c.subspaceCoordinates 0 (subspace_action_at_generators c hc)
    CycleCertificates.half_regular_rank CycleCertificates.half_seven_rank

private theorem quotient_samples (c : CycleCoordinates) (hc : c.actor = groupGenerator) :
    RepresentativeBounds (V := cycleSubrepresentation.toSubmodule ⧸ c.half.toSubmodule)
      c.half.quotientRepresentation (groupHom regularWord) (groupHom sevenWord) :=
  coordinate_bounds (V := cycleSubrepresentation.toSubmodule ⧸ c.half.toSubmodule)
    c.half.quotientRepresentation c.quotientCoordinates 1
    (quotient_action_at_generators c hc)
    CycleCertificates.quotient_regular_rank CycleCertificates.quotient_seven_rank

/-- At the specified root words, each literal degree-32 cycle factor has
displacement at least ten and twelve, respectively. -/
theorem cycleSamples : CycleSamples :=
  ⟨half_samples cycleCoordinates rfl, quotient_samples cycleCoordinates rfl⟩

/-- The numerical cycle-factor premise is discharged; the independent group
conjugacy certificate transports the bounds to all required odd elements. -/
theorem cycleBounds_of_conjugacyCoverage (hcov : ConjugacyCoverage) : CycleBounds :=
  cycleBounds_of_samples hcov cycleSamples

end CFSG.Quasithin.ChapterK.Exceptional.G2CubicDegree.BinaryObstruction.Involutions.OddElements
