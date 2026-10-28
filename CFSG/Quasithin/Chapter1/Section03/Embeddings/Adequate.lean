module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.Statements
public import Theory.SpecificGroups.Held.Model.Basic

/-!
# The intrinsic embedding conclusion retaining Held

The intrinsic local hypotheses, including a genuine Sylow subgroup in H,
allow an additional p=3 invariant Held component. This companion preserves
all four original alternatives and their literal quotient, complement and
action data. The additional case retains the same elementary plane,
C-component, quasisimple core quotient and component-orbit containment.

These are conclusion contracts, not an asserted classification. The source
producer is qt-1-03-embeddings and its component-containment and invariant-three
branches. In the actual Chapter 15 configuration, both Fitting branches of
the additional Held case have separate ambient exclusions.
Source: the intrinsic reduction used in Aschbacher--Smith 1.3.4 and 15.4.20,
pp.509--511,1163--1164; corrected as recorded in quasithin-proof-basis.md.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.XiEmbedding
universe u
variable {G : Type u} [Group G]

/-- The additional actual invariant Held model permitted by the intrinsic input. -/
def HeldAlternative (p : ℕ) (T P L : Subgroup G) : Prop :=
  p = 3 ∧ Nonempty (P ≃* Plane p) ∧ T ≤ normalizer L ∧
    Nonempty (XiQuotient L ≃* Held.He)

/-- The original four alternatives together with the retained Held case. -/
def AdequateConclusion (p : ℕ) (T X P H : Subgroup G) : Prop :=
  (X.subgroupOf H).Normal ∨ ∃ L : Subgroup G,
    L ∈ cComponentsIn H ∧ IsQuasisimple (XiQuotient L) ∧
      X ≤ componentOrbit L T ∧ (Alternatives p T P L ∨ HeldAlternative p T P L)

/-- The adequate intrinsic theorem's complete universal proof obligation.
Unlike its old companion, this contract does not discard the actual Held case. -/
def AdequateLocalEmbeddingTheorem (κ : GroupClass.{u}) : Prop :=
  ∀ (A : Type u) [Group A] [Finite A] (p : ℕ) (T X P H : Subgroup A),
    LocalInput p T X P H → IsSQTK κ H → IsSylowIn 2 T H →
      AdequateConclusion p T X P H

end CFSG.Quasithin.Chapter1.XiEmbedding
