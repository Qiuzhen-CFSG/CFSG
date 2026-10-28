module

public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.Embeddings
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.Statements

/-!
# Model interfaces for the involution-centralizer argument

The six possible overgroups of the A₆ section on printed p.715 are actual
group models. The intrinsic Ξ implication below retains the genuine Sylow
hypothesis and the additional Held alternative required by the source audit.
These are specifications of inputs and outputs, not assertions that the
appendix comparison or the intrinsic classification has been proved.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Proposition 8.2.2(1), p.715; A.3.12, pp.47–48; Proposition 1.3.4,
pp.509–511. See `docs/quasithin-proof-basis.md` for the intrinsic correction.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter8.Section02.Offenders.Parabolic.Exclusion.CentralizerEmbedding
open Subgroup Theory.GroupTheory Chapter1 Chapter1.XiEmbedding
open Chapter1.Section02.LocalModels
universe u

/-- The complete list on p.715 after comparing the smaller A₆ section with
all twenty-two alternatives of A.3.12. -/
def A6OvergroupModel (Q : Type u) [Group Q] : Prop :=
  IsAlternating Q 6 ∨ IsAlternating Q 7 ∨
    Nonempty (Q ≃* Sporadic.Mathieu.M11) ∨
    Nonempty (Q ≃* Sporadic.Mathieu.M22) ∨
    Nonempty (Q ≃* Sporadic.Mathieu.M23) ∨ ClassicalGroup.IsPSU Q 3 5

/-- The sufficient intrinsic p=3 conclusion retains Held, including the
actual plane marking, component normalization and component containment. -/
def AdequateXiConclusion {A : Type u} [Group A] (T X P H : Subgroup A) : Prop :=
  (X.subgroupOf H).Normal ∨ ∃ K : Subgroup A,
    K ∈ cComponentsIn H ∧ IsQuasisimple (XiQuotient K) ∧
      X ≤ componentOrbit K T ∧
      (Alternatives 3 T P K ∨
        (Nonempty (P ≃* Plane 3) ∧ T ≤ normalizer K ∧
          Nonempty (XiQuotient K ≃* Held.He)))

/-- An explicit earlier theorem contract. Its producer is the adequate
intrinsic branch of `qt-1-03-embeddings`; this definition does not prove it. -/
def EarlierAdequateXi (κ : GroupClass.{u}) : Prop :=
  ∀ (A : Type u) [Group A] [Finite A] (T X P H : Subgroup A),
    LocalInput 3 T X P H → IsSQTK κ H → IsSylowIn 2 T H →
      AdequateXiConclusion T X P H

end CFSG.Quasithin.Chapter8.Section02.Offenders.Parabolic.Exclusion.CentralizerEmbedding
