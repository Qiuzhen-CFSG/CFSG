module

public import Theory.SpecificGroups.ReeF4.CentralCovers.OddPrimary.GoodPrimes.Cyclotomic.AlgebraicTorus
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.ExceptionalMorphism
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.Fusion.ConnectedLang.ZeroDifferential

/-!
# The algebraic Ree twist and Lang descent

The already constructed exceptional algebraic F4 morphism, composed with the
m-th coordinate Frobenius, realizes the precise Ree root formula and equals
its odd exceptional power on points. It is bijective on algebraically closed
points. For `m ≥ 1`, its differential vanishes: every coordinate of Frobenius
is a square, so its pullback is annihilated by every characteristic-two
derivation. Composition preserves this vanishing.

The connectedness of the concrete root-generated F4 carrier and the proved
zero-differential form of Lang's theorem therefore supply every Lang solution.
This avoids the unresolved numbered general Lang theorem. The differential
calculation is adapted from the coordinate-square proof in
`ConnectedLang/FrobeniusDifferential.lean`; the generic Lang proof is reused
from `ConnectedLang/ZeroDifferential.lean`.

Sources: Steinberg, *Endomorphisms of Linear Algebraic Groups*, 10.7–10.8,
`refs/KGroup/GLS3/Chapter2St2.tex`; GLS3 §§2.1–2.2.
-/

public section
namespace ReeF4.CentralCovers.OddPrimary.Cyclotomic
open Theory.AlgebraicGroup
open ReeF4.BinaryDegree.ExceptionalTensor
open ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg
open ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry
noncomputable section
variable {F : Type*} [Field F] [IsAlgClosed F] [CharP F 2]

def frobeniusIterate : ℕ → Theory.AlgebraicGroup.Morphism (AlgebraicCarrier F) (AlgebraicCarrier F)
  | 0 => Theory.AlgebraicGroup.Morphism.id _
  | n+1 => frobeniusMorphism.comp (frobeniusIterate n)

theorem frobeniusIterate_onPoints (n : ℕ) :
    (frobeniusIterate (F := F) n).onPoints = frobeniusEnd ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change frobeniusEnd.comp (frobeniusIterate n).onPoints = _
    rw [ih, pow_succ']
    rfl

theorem frobeniusIterate_root (n : ℕ) (r : F4Chevalley.Root) (t : F) :
    (frobeniusIterate n).onPoints (rootPoint r t) = rootPoint r (t^(2^n)) := by
  induction n with
  | zero => change rootPoint r t = rootPoint r (t^1); rw [pow_one]
  | succ n ih =>
    change frobeniusEnd ((frobeniusIterate n).onPoints (rootPoint r t)) = _
    rw [ih]
    change frobeniusEnd (algebraicRootElement r _) = algebraicRootElement r _
    rw [frobeniusEnd_root, ← pow_mul, ← pow_succ]

/-- The constructed exceptional morphism composed with the m-th coordinate Frobenius. -/
def algebraicReeTwist (m : ℕ) :
    Theory.AlgebraicGroup.Morphism (AlgebraicCarrier F) (AlgebraicCarrier F) :=
  ExceptionalMorphism.morphism.comp (frobeniusIterate m)

@[expose] def exceptionalPointEnd : Monoid.End (PointGroup F) :=
  (ExceptionalMorphism.morphism (F := F)).onPoints

theorem algebraicReeTwist_onPoints (m : ℕ) :
    (algebraicReeTwist (F := F) m).onPoints =
      exceptionalPointEnd (F := F) ^ (2*m+1) := by
  change (ExceptionalMorphism.morphism (F := F)).onPoints.comp (frobeniusIterate m).onPoints = _
  rw [frobeniusIterate_onPoints,
    exceptional_odd_power _ (show HasExceptionalRootFormula (exceptionalPointEnd (F := F)) from ExceptionalMorphism.morphism_rootFormula)]
  rfl

/-- The constructed morphism has the literal long/short Ree root formula. -/
theorem algebraicReeTwist_rootAction (m : ℕ) :
    HasReeRootAction m (algebraicReeTwist (F := F) m) := by
  classical
  intro r t
  change (ExceptionalMorphism.morphism (F := F)).onPoints
    ((frobeniusIterate m).onPoints (rootPoint r t)) = _
  rw [frobeniusIterate_root]
  change (ExceptionalMorphism.morphism (F := F)).onPoints (algebraicRootElement r _) = _
  rw [ExceptionalMorphism.morphism_root]
  by_cases hr : IsLongRoot r
  · rw [if_pos hr, exceptionalParameter_of_long hr]
    rfl
  · rw [if_neg hr, exceptionalParameter_of_short hr, ← pow_mul, ← pow_succ]
    rfl

theorem algebraicReeTwist_bijective (m : ℕ) :
    Function.Bijective (algebraicReeTwist (F := F) m).onPoints := by
  have hi (n : ℕ) : Function.Bijective (frobeniusIterate (F := F) n).onPoints := by
    induction n with
    | zero => exact Function.bijective_id
    | succ n ih => exact frobeniusEnd_bijective.comp ih
  exact ExceptionalMorphism.morphism_bijective.comp (hi m)

open Theory.AlgebraicGroup.Bor1

private theorem frobenius_differential :
    identityTangentMorphismLinearMap (frobeniusMorphism (F := F)) = 0 := by
  apply LinearMap.ext
  intro D
  apply coordinateTangentMap_injective (AlgebraicCarrier F)
  funext i
  let a := Variety.PolynomialFunction.ofPolynomial (AlgebraicCarrier F) (MvPolynomial.X i)
  have ha : frobeniusMorphism.toVariety.pullbackAlgHom a = a * a := by
    apply Variety.PolynomialFunction.ext
    intro x
    change evalPolynomial (frobeniusEnd x).val (MvPolynomial.X i) =
      evalPolynomial x.val (MvPolynomial.X i) * evalPolynomial x.val (MvPolynomial.X i)
    simp only [evalPolynomial_X, frobeniusEnd_coordinate, pow_two]
  change D (frobeniusMorphism.toVariety.pullbackAlgHom a) = 0
  rw [ha, Derivation.leibniz]
  exact CharTwo.add_self_eq_zero _

theorem frobeniusIterate_differential (m : ℕ) (hm : 1 ≤ m) :
    identityTangentMorphismLinearMap (frobeniusIterate (F := F) m) = 0 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  rw [frobeniusIterate, identityTangentMorphismLinearMap_comp,
    frobenius_differential, LinearMap.zero_comp]

theorem algebraicReeTwist_differential (m : ℕ) (hm : 1 ≤ m) :
    identityTangentMorphismLinearMap (algebraicReeTwist (F := F) m) = 0 := by
  rw [algebraicReeTwist, identityTangentMorphismLinearMap_comp,
    frobeniusIterate_differential m hm, LinearMap.comp_zero]

theorem algebraicReeTwist_lang (m : ℕ) (hm : 1 ≤ m) :
    Function.Surjective (fun g : AlgebraicPoints F =>
      g * ((algebraicReeTwist m).onPoints g)⁻¹) := by
  have h := langMorphism_surjective_of_differential_eq_zero (algebraicReeTwist (F := F) m)
    (algebraicReeTwist_bijective m).surjective F4Chevalley.carrier_isConnected
    (algebraicReeTwist_differential m hm)
  intro y
  obtain ⟨g, hg⟩ := h y
  refine ⟨g, ?_⟩
  simpa only [langMorphism_apply, map_inv] using hg

end
end ReeF4.CentralCovers.OddPrimary.Cyclotomic
