module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.AmbientCount.TorusData
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.AmbientCount.TorusGeometry.Inputs

/-!
# Conditional construction of the D4 torus correspondence

Starting with the independently specified Weyl geometry, algebraic restrictions
of the pinned maps and semisimple containment, this module derives all character
formulas and constructs `TorusData`. The graph-field map applies the diagram
first and then iterates Frobenius, exactly as `ClassBound.graphFieldEnd`.
The character calculation holds for every exponent, in particular `n = 1`.

This is conditional assembly. Existence of `WeylGeometry`, `PinnedTorusMaps` and
the semisimple conjugacy statement still has to be proved from `Geometry` before
this module establishes unconditional existence of `TorusData`.

Source: Steinberg, `refs/KGroup/GLS3/Chapter2St2.tex`, §§6, 11 and 14.8(a).
-/

@[expose] public noncomputable section
namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ClassBound.AmbientCount.TorusGeometry
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open D4RestrictedWeight

universe u
variable {k : Type u} [Field k] [CharP k 2]
variable {K : Variety k} [AlgebraicGroup K] {S : Geometry K}

/-- The point endomorphism obtained by applying the restricted diagram map
first and iterating the restricted Frobenius. -/
def PinnedTorusMaps.graphField (F : PinnedTorusMaps S) (n : ℕ) :
    Monoid.End (Variety.Point S.torus.carrierVariety) :=
  let φ : Monoid.End (Variety.Point S.torus.carrierVariety) := F.frobenius.onPoints
  (φ ^ n).comp F.diagram.onPoints

/-- Inclusion intertwines every iterate of the two Frobenius maps. -/
theorem PinnedTorusMaps.frobenius_iterate_ambient (F : PinnedTorusMaps S) (n : ℕ)
    (t : Variety.Point S.torus.carrierVariety) :
    S.torus.includePoint (F.frobenius.onPoints^[n] t) =
      S.frobenius.onPoints^[n] (S.torus.includePoint t) := by
  induction n generalizing t with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', F.frobenius_ambient, ih]

/-- This torus endomorphism restricts the literal ambient graph-field map. -/
theorem PinnedTorusMaps.graphField_ambient (F : PinnedTorusMaps S) (n : ℕ)
    (t : Variety.Point S.torus.carrierVariety) :
    S.torus.includePoint (F.graphField n t) = graphFieldEnd S n (S.torus.includePoint t) := by
  change S.torus.includePoint (F.frobenius.onPoints^[n] (F.diagram.onPoints t)) =
    S.frobenius.onPoints^[n] (S.diagram.toMulEquiv (S.torus.includePoint t))
  rw [F.frobenius_iterate_ambient, F.diagram_ambient]

variable [IsAlgClosed k]

/-- The coroot permutation determines the pullback of every actual weight. -/
theorem PinnedTorusMaps.diagram_weight (F : PinnedTorusMaps S)
    (a : Weight) (t : Variety.Point S.torus.carrierVariety) :
    (S.weight (Multiplicative.ofAdd a)).pointCharacter (F.diagram.onPoints t) =
      (S.weight (Multiplicative.ofAdd (a ∘ typeD4DiagramPermutation))).pointCharacter t := by
  simpa only [pow_one] using pullback_weight_of_coroot S F.diagram
    typeD4DiagramPermutation 1 (by simpa only [pow_one] using F.diagram_coroot) a t

/-- Squaring each simple coroot squares every character value. -/
theorem PinnedTorusMaps.frobenius_weight (F : PinnedTorusMaps S)
    (a : Weight) (t : Variety.Point S.torus.carrierVariety) :
    (S.weight (Multiplicative.ofAdd a)).pointCharacter (F.frobenius.onPoints t) =
      (S.weight (Multiplicative.ofAdd a)).pointCharacter t ^ 2 :=
  pullback_weight_of_coroot S F.frobenius id 2 F.frobenius_coroot a t

/-- Iteration gives the exact `2 ^ n` power on character values. -/
theorem PinnedTorusMaps.frobenius_iterate_weight (F : PinnedTorusMaps S)
    (n : ℕ) (a : Weight) (t : Variety.Point S.torus.carrierVariety) :
    (S.weight (Multiplicative.ofAdd a)).pointCharacter (F.frobenius.onPoints^[n] t) =
      (S.weight (Multiplicative.ofAdd a)).pointCharacter t ^ (2 ^ n) := by
  induction n generalizing t with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', F.frobenius_weight, ih, ← pow_mul, pow_succ]

/-- The graph-field character formula, with the prescribed arm cycle. -/
theorem PinnedTorusMaps.graphField_weight (F : PinnedTorusMaps S)
    (n : ℕ) (a : Weight) (t : Variety.Point S.torus.carrierVariety) :
    (S.weight (Multiplicative.ofAdd a)).pointCharacter (F.graphField n t) =
      (S.weight (Multiplicative.ofAdd (a ∘ typeD4DiagramPermutation))).pointCharacter t ^ (2 ^ n) := by
  change (S.weight (Multiplicative.ofAdd a)).pointCharacter
    (F.frobenius.onPoints^[n] (F.diagram.onPoints t)) = _
  rw [F.frobenius_iterate_weight, F.diagram_weight]

/-- Construct the complete torus contract from the three independent geometric
inputs. Their unconditional existence is not asserted by this definition. -/
def torusData (W : WeylGeometry S) (F : PinnedTorusMaps S)
    (hsemi : ∀ x : Variety.Point K, IsSemisimpleElement K x →
      ∃ t : Variety.Point S.torus.carrierVariety, IsConj x (S.torus.includePoint t))
    (n : ℕ) : TorusData S n where
  action := W.action
  map := F.graphField n
  map_ambient := F.graphField_ambient n
  conjugate_iff := W.conjugate_iff
  semisimple_conjugate := hsemi
  reflection_weight := by
    let := W.action
    intro i a t
    rw [W.reflection_point]
    exact simpleReflection_weight S i a t
  map_weight := F.graphField_weight n

end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ClassBound.AmbientCount.TorusGeometry
