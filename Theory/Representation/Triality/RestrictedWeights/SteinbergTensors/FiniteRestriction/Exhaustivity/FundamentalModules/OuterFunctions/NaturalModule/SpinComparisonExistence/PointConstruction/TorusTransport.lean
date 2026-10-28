module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.FundamentalModules.OuterFunctions.NaturalModule.SpinComparisonExistence.Data
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.AmbientCount.TorusGeometry.PinnedMaps

/-!
# Transport from the four marked coroots to the whole torus

The four fundamental characters separate source torus points. Their Kronecker
pairings express every torus point as the ordered product of its four marked
simple coroots. Consequently matching those coroots forces exactly the raw
coordinate formula in `RootwiseSpinHom`.

The character-duality argument is adapted from the private decomposition in
`ClassBound/AmbientCount/TorusGeometry/PinnedMaps.lean`.
Source: GLS3 Theorem 1.12.5(b) and Definition 1.14.2.
-/

@[expose] public noncomputable section
namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.OuterFunctions
namespace SpinComparisonExistence.PointConstruction
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open Triality.SimplyConnected Triality.SimplyConnected.Pinning
open D4RestrictedWeight
open ClassBound.AmbientCount.TorusGeometry (weight_coroot)

universe u
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k 2]
variable {K : Variety k} [AlgebraicGroup K]

private def fundamentalCharacter (S : Geometry K) (i : Fin 4) : TorusWeight S.torus :=
  S.weight (Multiplicative.ofAdd (Pi.single i 1))

omit [IsAlgClosed k] in
private theorem weight_expand (S : Geometry K) (a : Weight) :
    S.weight (Multiplicative.ofAdd a) =
      fundamentalCharacter S 0 ^ a 0 * fundamentalCharacter S 1 ^ a 1 *
      fundamentalCharacter S 2 ^ a 2 * fundamentalCharacter S 3 ^ a 3 := by
  unfold fundamentalCharacter
  simp only [← map_zpow S.weight, ← map_mul S.weight]
  congr 1
  change a = a 0 • Pi.single 0 1 + a 1 • Pi.single 1 1 +
    a 2 • Pi.single 2 1 + a 3 • Pi.single 3 1
  funext i
  fin_cases i <;> simp

private theorem torus_point_ext (S : Geometry K) (t u : S.torus.carrierVariety.Point)
    (h : ∀ i, (fundamentalCharacter S i).pointCharacter t =
      (fundamentalCharacter S i).pointCharacter u) : t = u := by
  apply (torusPointEval_bijective S.maximalTorus.1).injective
  apply MonoidHom.ext
  intro χ
  obtain ⟨a, rfl⟩ := S.weight.surjective χ
  change torusPointEval _ t (S.weight (Multiplicative.ofAdd a.toAdd)) =
    torusPointEval _ u (S.weight (Multiplicative.ofAdd a.toAdd))
  rw [weight_expand]
  have h' (i : Fin 4) : torusPointEval _ t (fundamentalCharacter S i) =
      torusPointEval _ u (fundamentalCharacter S i) := Units.ext (h i)
  simp only [map_mul, map_zpow, h']

private theorem simple_coroot_decomposition (S : Geometry K) (t : S.torus.carrierVariety.Point) :
    t = (S.roots.rootCocharacter (S.simpleRoot 0).val).onPoints
          ((fundamentalCharacter S 0).onPoints t) *
        (S.roots.rootCocharacter (S.simpleRoot 1).val).onPoints
          ((fundamentalCharacter S 1).onPoints t) *
        (S.roots.rootCocharacter (S.simpleRoot 2).val).onPoints
          ((fundamentalCharacter S 2).onPoints t) *
        (S.roots.rootCocharacter (S.simpleRoot 3).val).onPoints
          ((fundamentalCharacter S 3).onPoints t) := by
  apply torus_point_ext S
  intro i
  simp only [map_mul, fundamentalCharacter, weight_coroot]
  fin_cases i <;> simp [TorusCharacter.pointCharacter]


/-- Matching the four marked simple coroots gives the full raw torus formula. -/
theorem torus_eq_of_simpleCoroots (S : Geometry K) (f : K.Point →* Points k)
    (hf : ∀ (i : Fin 4) (z : (KMult k).Point),
      f (S.torus.includePoint ((S.roots.rootCocharacter (S.simpleRoot i).val).onPoints z)) =
        simpleCoroot k i (dPointEquiv 1 z 0))
    (t : S.torus.carrierVariety.Point) :
    f (S.torus.includePoint t) = CorootTorus.parameter k (rawTorusCoordinates k S t) := by
  conv_lhs => rw [simple_coroot_decomposition S t]
  change f (S.torus.inclusion.onPoints _) = _
  simp only [map_mul]
  have hinc (z : S.torus.carrierVariety.Point) :
      S.torus.inclusion.onPoints z = S.torus.includePoint z := rfl
  simp only [hinc, hf]
  simp only [CorootTorus.parameter, List.ofFn_succ, List.ofFn_zero,
    List.prod_cons, List.prod_nil, mul_one]
  simp only [mul_assoc]
  rfl

end SpinComparisonExistence.PointConstruction
end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.OuterFunctions
