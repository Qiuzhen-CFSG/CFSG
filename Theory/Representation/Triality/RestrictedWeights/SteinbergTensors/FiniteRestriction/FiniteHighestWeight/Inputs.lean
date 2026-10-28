module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Contracts

/-!
# Finite highest-vector proof obligations

These are explicit intermediate statements, not hypotheses of `Geometry` and
not asserted theorems. Finite highest-line detection and cyclicity supply
irreducibility. Weight recovery is independent: once an actual intertwiner
carries a highest vector to a highest vector, finite root actions must recover
all four integral coordinates. Merely comparing finite torus characters does
not prove this last statement.

Sources: GLS3, Definition 2.8.1 and Theorem 2.8.2;
Steinberg, `Chapter2St2.tex`, Theorem 13.3(a).
-/

@[expose] public section

namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction

open Theory.AlgebraicGroup
open Theory.AlgebraicGroup.StandardRootSystem.D4RestrictedWeight

universe u
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k 2]
variable {K : Variety k} [AlgebraicGroup K]

/-- Finite positive-unipotent invariants of a restricted rational factor lie
in its actual highest line. The opposite containment is proved in `Unipotent`. -/
def FiniteHighestLine (S : Geometry K) (n : ℕ) : Prop :=
  ∀ (A : RationalFactor K) (a : Weight), InRestrictedRange n a →
    ∀ v : A.Space,
      HasHighWeight A.action S.bigCell.data.B S.torus v (S.coordinateEmbedding a) →
        ∀ w : A.Space,
          (∀ g : positiveUnipotent S n, (A.restrict (S.inclusion n)).ρ g.val w = w) →
            w ∈ Submodule.span k ({v} : Set A.Space)

/-- The actual elementary-group orbit of a restricted highest vector spans.
This statement concerns the finite orbit, not the full algebraic-group orbit. -/
def FiniteHighestOrbitSpan (S : Geometry K) (n : ℕ) : Prop :=
  ∀ (A : RationalFactor K) (a : Weight), InRestrictedRange n a →
    ∀ v : A.Space,
      HasHighWeight A.action S.bigCell.data.B S.torus v (S.coordinateEmbedding a) →
        Submodule.span k (Set.range (fun g =>
          (A.restrict (S.inclusion n)).ρ g v)) = ⊤

/-- Finite root actions recover the integral highest weight when an actual
intertwiner already carries one chosen highest vector to another. Highest-line
detection is deliberately separated from this root-action obligation. -/
def HighestVectorWeightRecovery (S : Geometry K) (n : ℕ) : Prop :=
  ∀ (A C : RationalFactor K) (a b : Weight),
    InRestrictedRange n a → InRestrictedRange n b →
      ∀ (v : A.Space) (w : C.Space),
        HasHighWeight A.action S.bigCell.data.B S.torus v (S.coordinateEmbedding a) →
        HasHighWeight C.action S.bigCell.data.B S.torus w (S.coordinateEmbedding b) →
          ∀ e : Representation.Equiv (A.restrict (S.inclusion n)).ρ
            (C.restrict (S.inclusion n)).ρ, e v = w → a = b

end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction
