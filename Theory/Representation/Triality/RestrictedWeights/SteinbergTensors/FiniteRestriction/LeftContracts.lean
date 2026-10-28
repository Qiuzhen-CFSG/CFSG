module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Contracts
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.LeftWeights

/-!
# Source-correct finite restriction obligations

These are obligations for Steinberg §13.3 / GLS3 2.8.2, on the unchanged
positive Borel and literal elementary subgroup. Positive fundamental and
restricted coordinates use the left embedding. No existence, irreducibility,
separation or exhaustivity assertion is proved by defining these predicates.
-/

@[expose] public section
namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction
open Theory.AlgebraicGroup
open Theory.AlgebraicGroup.StandardRootSystem.D4RestrictedWeight
universe u
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k 2]
variable {K : Variety k} [AlgebraicGroup K]

/-- Highest weight for the unchanged Borel and the direct left eigencharacter. -/
def HasLeftHighestWeight (S : Geometry K) (A : RationalFactor K) (a : Weight) : Prop :=
  ∃ v, HasHighWeight A.action S.bigCell.data.B S.torus v (S.leftWeightEmbedding a)

/-- This bridge negates the raw label, without changing the positive range. -/
theorem hasLeftHighestWeight_iff (S : Geometry K) (A : RationalFactor K) (a : Weight) :
    HasLeftHighestWeight S A a ↔ HasHighestWeight S A (-a) := Iff.rfl

/-- Restricted rational irreducibles remain irreducible on the elementary group. -/
def LeftRestrictedIrreducibility (S : Geometry K) (n : ℕ) : Prop :=
  ∀ (A : RationalFactor K) (a : Weight),
    InRestrictedRange n a → HasLeftHighestWeight S A a →
      Representation.IsIrreducible (A.restrict (S.inclusion n)).ρ

/-- A genuine intertwiner of finite restrictions cannot identify distinct
restricted highest weights. The reverse implication is already proved. -/
def LeftRestrictedSeparation (S : Geometry K) (n : ℕ) : Prop :=
  ∀ (A C : RationalFactor K) (a b : Weight),
    InRestrictedRange n a → InRestrictedRange n b →
      HasLeftHighestWeight S A a → HasLeftHighestWeight S C b →
        Nonempty (Representation.Equiv (A.restrict (S.inclusion n)).ρ
          (C.restrict (S.inclusion n)).ρ) → a = b

/-- Every irreducible elementary-group module has an actual restricted
rational lift, with a linear intertwining equivalence. -/
def LeftRestrictedExhaustivity (S : Geometry K) (n : ℕ) : Prop :=
  ∀ V : FDRep k (graphFieldElementarySubgroup S.diagram.toMulEquiv S.frobenius.onPoints n),
    Representation.IsIrreducible V.ρ →
      ∃ (A : RationalFactor K) (a : Weight),
        InRestrictedRange n a ∧ HasLeftHighestWeight S A a ∧
          Nonempty (Representation.Equiv V.ρ (A.restrict (S.inclusion n)).ρ)


/-- Finite positive-unipotent invariants of a restricted rational factor lie
in its actual highest line. The opposite containment is proved in `Unipotent`. -/
def LeftFiniteHighestLine (S : Geometry K) (n : ℕ) : Prop :=
  ∀ (A : RationalFactor K) (a : Weight), InRestrictedRange n a →
    ∀ v : A.Space,
      HasHighWeight A.action S.bigCell.data.B S.torus v (S.leftWeightEmbedding a) →
        ∀ w : A.Space,
          (∀ g : positiveUnipotent S n, (A.restrict (S.inclusion n)).ρ g.val w = w) →
            w ∈ Submodule.span k ({v} : Set A.Space)

/-- The actual elementary-group orbit of a restricted highest vector spans.
This statement concerns the finite orbit, not the full algebraic-group orbit. -/
def LeftFiniteHighestOrbitSpan (S : Geometry K) (n : ℕ) : Prop :=
  ∀ (A : RationalFactor K) (a : Weight), InRestrictedRange n a →
    ∀ v : A.Space,
      HasHighWeight A.action S.bigCell.data.B S.torus v (S.leftWeightEmbedding a) →
        Submodule.span k (Set.range (fun g =>
          (A.restrict (S.inclusion n)).ρ g v)) = ⊤

/-- Finite root actions recover the integral highest weight when an actual
intertwiner already carries one chosen highest vector to another. Highest-line
detection is deliberately separated from this root-action obligation. -/
def LeftHighestVectorWeightRecovery (S : Geometry K) (n : ℕ) : Prop :=
  ∀ (A C : RationalFactor K) (a b : Weight),
    InRestrictedRange n a → InRestrictedRange n b →
      ∀ (v : A.Space) (w : C.Space),
        HasHighWeight A.action S.bigCell.data.B S.torus v (S.leftWeightEmbedding a) →
        HasHighWeight C.action S.bigCell.data.B S.torus w (S.leftWeightEmbedding b) →
          ∀ e : Representation.Equiv (A.restrict (S.inclusion n)).ρ
            (C.restrict (S.inclusion n)).ρ, e v = w → a = b


/-- Existence of rational irreducibles for all restricted highest weights.
This is an obligation, not a field of the geometric setup. -/
def LeftRestrictedRationalExistence (S : Geometry K) (n : ℕ) : Prop :=
  ∀ a : Weight, InRestrictedRange n a → ∃ A : RationalFactor K, HasLeftHighestWeight S A a

/-- Only the four fundamental rational highest weights are needed for the
existence construction. No finite restriction or tensor simplicity is assumed. -/
def LeftFundamentalRationalExistence (S : Geometry K) : Prop :=
  ∀ i : Fin 4, ∃ A : RationalFactor K, HasLeftHighestWeight S A (Pi.single i 1)



end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction
