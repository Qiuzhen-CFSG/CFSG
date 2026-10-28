module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.InnerEscape.TwentyFive.Geometry.ActorFusion.LocalBounds

/-!
# Remaining characteristic-five coordinate calculations

The single-centralizer calculation identifies its derived four-group with
the intersection of the literal large subgroup and the original linear
kernel, and supplies a local conjugator for each nonlinear bad actor.
The independent pair calculation bounds one projected intersection.
Neither statement contains an ambient orbit span, family escape, or the
final fusion predicate. `ActorFusion` assembles them using `LocalBounds`.
Their unconditional proofs in the actual field model are still required.

Source: Aschbacher--Smith E.1.14(6), printed p.214, and its reference to
Aschbacher (1982), Lemma 4.10.
-/

public section
noncomputable section
open Subgroup GorensteinWalter Matrix

namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.InnerEscape.TwentyFive.Geometry.Frame

variable {F : Type*} [Field F] [Finite F] {σ : F ≃+* F}
variable (c : Frame σ) (hF : Nat.card F = 5 ^ 2) (hσ : orderOf σ = 2)

namespace ActorFusion

/-- A bound on one literal projective image of the intersection. -/
@[expose] def PairIntersectionBound : Prop :=
  Nat.card (((c.large hF hσ false ⊓ c.large hF hσ true).subgroupOf
    (c.centralizerAt false)).map (c.projection hF hσ false)) ≤ 2

variable [Finite (innerModel F σ)]

/-- Local model calculations in S₅ × C₂. The conjugator belongs to the
specified centralizer; neither ambient fusion nor actor coverage is an input. -/
structure LocalCalculation : Prop where
  small_card : ∀ i, Nat.card (c.small hF hσ i) = 4
  linear_marking : ∀ i,
    c.large hF hσ i ⊓ pGammaL2LinearKernel F (innerModel F σ) = c.small hF hσ i
  spread : ∀ i A, c.Eligible A → ¬ c.IsPositioned hF hσ i A →
    ¬ A ≤ pGammaL2LinearKernel F (innerModel F σ) →
    ∃ g ∈ c.centralizerAt i,
      A.map (MulAut.conj g).toMonoidHom ≤ (c.T : Subgroup _) ∧
      c.large hF hσ i ≤ A ⊔ A.map (MulAut.conj g).toMonoidHom

end ActorFusion

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.InnerEscape.TwentyFive.Geometry.Frame
