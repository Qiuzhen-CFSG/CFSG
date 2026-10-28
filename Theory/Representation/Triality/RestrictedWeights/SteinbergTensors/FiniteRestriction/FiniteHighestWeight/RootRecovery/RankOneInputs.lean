module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight.RootRecovery
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.LeftContracts
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.LeftWeights.Coroots
public import Mathlib.FieldTheory.Finite.Basic

/-!
# Actual rank-one comparisons for left D4 weight recovery

The simple-root orbits are the central vertex `1` and the arms in order
`0, 2, 3`. Their positive curves and left coroot products are specified as
actual points of the supplied geometry. `FiniteRootChart` asks for a regular
SL2 map, an actual finite subfield, and a compatible map into the literal
elementary subgroup. It contains no representation conclusion and its
existence is a separate geometric obligation.

`FiniteSL2HighestVectorRecovery` is the independent rational rank-one
obligation. A possible proof uses finite diagonal characters and the Weyl
translate to distinguish exponent zero from the maximal restricted exponent.
It allows reducible rational SL2 modules: restriction from D4 need not be
irreducible. No orbit-module identification or finite irreducibility is assumed.

Source: GLS3 Definition 2.8.1 and Theorem 2.8.2; Steinberg,
`refs/KGroup/GLS3/Chapter2St2.tex`, §§12 and 13.3(a). Coroot inversion follows
the checked left adapter; the original positive roots and diagram are unchanged.
-/

@[expose] public noncomputable section
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open D4RestrictedWeight
open scoped MatrixGroups
namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.RootRecovery
universe u
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k 2]
variable {K : Variety k} [AlgebraicGroup K]

/-- The two orbits of simple roots under the given diagram automorphism. -/
inductive RootOrbit | central | arms
  deriving DecidableEq

/-- The sizes of the two finite fields are `2^n` and `2^(3*n)`. -/
def RootOrbit.fieldExponent (o : RootOrbit) (n : ℕ) : ℕ :=
  match o with | .central => n | .arms => 3 * n

/-- The actual exponent on the left diagonal of the orbit SL2. -/
def RootOrbit.degree (o : RootOrbit) (n : ℕ) (a : Weight) : ℤ :=
  match o with
  | .central => a 1
  | .arms => a 0 + (2 : ℤ)^n * a 2 + ((2 : ℤ)^n)^2 * a 3

/-- The positive root parameter; the arm order follows `0 -> 2 -> 3 -> 0`. -/
def RootOrbit.upperPoint (o : RootOrbit) (S : Geometry K) (n : ℕ) (t : k) : Variety.Point K :=
  match o with
  | .central => rootPoint S (S.simpleRoot 1).val t
  | .arms => rootPoint S (S.simpleRoot 0).val t *
      rootPoint S (S.simpleRoot 2).val (t ^ (2^n)) *
      rootPoint S (S.simpleRoot 3).val (t ^ ((2^n)^2))

/-- The actual left coroot product, before inclusion into the ambient group. -/
def RootOrbit.torusPoint (o : RootOrbit) (S : Geometry K) (n : ℕ)
    (t : Variety.Point (KMult k)) : Variety.Point S.torus.carrierVariety :=
  match o with
  | .central => (S.leftSimpleCoroot 1).onPoints t
  | .arms => (S.leftSimpleCoroot 0).onPoints t *
      (S.leftSimpleCoroot 2).onPoints (t ^ (2^n)) *
      (S.leftSimpleCoroot 3).onPoints (t ^ ((2^n)^2))

/-- Coefficient inclusion of an actual finite subfield into the algebraic SL2. -/
def finiteSL2Inclusion (F : Subfield k) :
    SL(2, F) →* Variety.Point (slVariety k 2) :=
  { toFun := fun g => (slPointEquiv 2).symm (Matrix.SpecialLinearGroup.map F.subtype g)
    map_one' := by
      apply (slPointEquiv 2).injective
      exact map_one (Matrix.SpecialLinearGroup.map F.subtype)
    map_mul' := fun g h => by
      apply (slPointEquiv 2).injective
      exact map_mul (Matrix.SpecialLinearGroup.map F.subtype) g h }

/-- A geometric comparison, with all group maps and point equalities explicit.
No representation-theoretic conclusion is a field of this structure. -/
structure FiniteRootChart (S : Geometry K) (n : ℕ) (o : RootOrbit) where
  field : Subfield k
  finite : Finite field
  card : Nat.card field = 2 ^ (o.fieldExponent n)
  map : Theory.AlgebraicGroup.Morphism (slVariety k 2) K
  upper : ∀ t : k, map.onPoints (standardSL2UpperMorphism.onPoints (kPlusPoint t)) =
    o.upperPoint S n t
  diagonal : ∀ t : Variety.Point (KMult k),
    map.onPoints (standardSL2DiagonalMorphism.onPoints t) =
      S.torus.includePoint (o.torusPoint S n t)
  finiteMap : SL(2, field) →*
    graphFieldElementarySubgroup S.diagram.toMulEquiv S.frobenius.onPoints n
  finite_compat : ∀ g, S.inclusion n (finiteMap g) = map.onPoints (finiteSL2Inclusion field g)

attribute [instance] FiniteRootChart.finite

/-- The rank-one statement needed by D4 assembly, for arbitrary rational SL2
representations. No irreducibility or orbit-module identification is assumed. -/
def FiniteSL2HighestVectorRecovery : Prop :=
  ∀ (F : Subfield k) [Finite F]
    (V W : Type u) [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    (ρ : RationalRepresentation (slVariety k 2) V)
    (τ : RationalRepresentation (slVariety k 2) W),
    IsRationalRepresentation ρ → IsRationalRepresentation τ →
    ∀ (m l : ℤ), 0 ≤ m → m < Nat.card F → 0 ≤ l → l < Nat.card F →
    ∀ (v : V) (w : W), v ≠ 0 → w ≠ 0 →
    (∀ t : k, (ρ.action (standardSL2UpperMorphism.onPoints (kPlusPoint t))).1 v = v) →
    (∀ t : k, (τ.action (standardSL2UpperMorphism.onPoints (kPlusPoint t))).1 w = w) →
    (∀ t : Variety.Point (KMult k),
      (ρ.action (standardSL2DiagonalMorphism.onPoints t)).1 v =
        (dPointEquiv 1 t 0 : k)^m • v) →
    (∀ t : Variety.Point (KMult k),
      (τ.action (standardSL2DiagonalMorphism.onPoints t)).1 w =
        (dPointEquiv 1 t 0 : k)^l • w) →
    ∀ e : V ≃ₗ[k] W, e v = w →
      (∀ g : SL(2, F), ∀ x : V,
        e ((ρ.action (finiteSL2Inclusion F g)).1 x) =
          (τ.action (finiteSL2Inclusion F g)).1 (e x)) → m = l

end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.RootRecovery
