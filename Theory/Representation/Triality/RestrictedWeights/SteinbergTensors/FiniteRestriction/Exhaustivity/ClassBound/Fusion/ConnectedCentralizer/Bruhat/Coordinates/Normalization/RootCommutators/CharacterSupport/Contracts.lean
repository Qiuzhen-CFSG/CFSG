module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.Fusion.ConnectedCentralizer.Bruhat.Coordinates.Normalization.RootCommutators.Closure
public import Theory.AlgebraicGroup.Tori.Character.AffinePolynomialSupport

/-!
Two regular-function inputs to the mixed root-commutator support argument.
These are explicit mathematical contracts, not asserted source theorems.
One lifts a root parameter equivariantly; the other detects strictly mixed
degrees in a polynomial with a torus character. Both use inverse conjugation.

Source: the character-support geometry underlying GLS3, 1.12.1(b) and 1.12.7(b).
-/

namespace Theory.AlgebraicGroup
universe u
variable {k : Type u} [Field k]

/-- Equivariant extension of the exact affine coordinate of each realized
root subgroup. This includes regular-function identities on the ambient group,
not merely tangent weights or a pointwise extension on the root subgroup. -/
@[expose] public def RootParameterEigenfunctionExtension
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) : Prop :=
  ∀ (c : D.Root) (x : OneParameterParametrization (D.rootSubgroup c).carrierVariety),
    ∃ F : Variety.PolynomialFunction K,
      (∀ z : k, F ((D.rootSubgroup c).includePoint (x.value z)) = z) ∧
      ∀ (s : Variety.Point T.carrierVariety) (g : Variety.Point K),
        F ((T.includePoint s)⁻¹ * g * T.includePoint s) =
          (D.rootWeight c).pointCharacter s * F g

/-- A nonzero polynomial with one torus character, vanishing whenever either
of its two parameter families is zero, has positive degree in both characters.
The Boolean labels specify the families; the conclusion uses integer degrees
in the character group, including in positive characteristic. -/
@[expose] public def MixedPolynomialCharacterSupport
    (T : Variety k) [AlgebraicGroup T] : Prop :=
  ∀ (sigma : Type u) [Finite sigma] (side : sigma → Bool)
    (a b c : TorusCharacter T) (P : MvPolynomial sigma k),
    (∃ z : sigma → k, MvPolynomial.eval z P ≠ 0) →
    (∀ (s : Variety.Point T) (z : sigma → k),
      MvPolynomial.eval
        (fun i => (if side i then a else b).pointCharacter s * z i) P =
          c.pointCharacter s * MvPolynomial.eval z P) →
    (∀ (e : Bool) (z : sigma → k),
      MvPolynomial.eval (fun i => if side i = e then 0 else z i) P = 0) →
    ∃ i j : ℕ, 0 < i ∧ 0 < j ∧ c = a ^ i * b ^ j

end Theory.AlgebraicGroup
