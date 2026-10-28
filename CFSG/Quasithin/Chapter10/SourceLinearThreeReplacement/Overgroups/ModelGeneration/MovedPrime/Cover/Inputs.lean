module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.ModelGeneration.MovedPrime.Inputs
public import Theory.GroupTheory.NormalizerAction

/-!
# Two structural inputs for the moved prime cover

The faithful component action reduces to an actual prime-field PSL₂ or
PGL₂ group. Its selected local subgroups either generate the simple normal
subgroup through solvable Sylow-invariant seeds, or it has a unique maximal
Sylow overgroup. In the second case that uniqueness must be lifted through
the exchanged component pair. Neither input asserts E-generation.

Source: Aschbacher--Smith E.1.11--14, E.2.2, and the reuse in 10.3.3,
printed pp.212--216 and 756--757. These contracts separate model subgroup
geometry from the literal ambient normalizer/centralizer transport.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.ModelGeneration.Cover
universe u

/-- A generating family inside L, each solvable and normalized by the
specified subgroup R. This retains the embeddings needed by the orbit lift. -/
def HasSolvableNormalizedCover {G : Type*} [Group G] (L R : Subgroup G) : Prop :=
  ∃ Δ : Set (Subgroup G),
    (∀ B ∈ Δ, B ≤ L ∧ Group.IsSolvable B ∧ R ≤ normalizer (B : Set G)) ∧
      sSup Δ = L

/-- The prime-field model dichotomy in the faithful normal-component setting.
The simple normal subgroup has an actual PSL₂ model, and its centralizer is
trivial. The nonminimal branch requests selected seeds, not a classification
of all parabolics or all proper overgroups. -/
def PrimeAutomizerCoverDichotomy : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] (L : Subgroup G), L.Normal →
    centralizer (L : Set G) = ⊥ → ∀ (R : Sylow 2 G),
      L ⊔ (R : Subgroup G) = ⊤ → ∀ p : ℕ,
        p.Prime → Odd p → 7 ≤ p → ClassicalGroup.IsPSL L 2 p →
          ChapterB.IsMinimalParabolicOver R ⊤ ∨
            HasSolvableNormalizedCover L (R : Subgroup G)

/-- Unique-maximal-overgroup transport from the actual component automizer.
The Sylow in the quotient must be exactly the image of S intersected with
the literal component normalizer. Ambient core-freeness and the source
quasithin hypothesis are retained, rather than asserted for an arbitrary H. -/
def MovedAutomizerMinimalLift : Prop :=
  ∀ (H : Type u) [Group H] [Finite H], IsSQTK KnownSimple.IsKnownSimple H →
    pCore 2 H = ⊥ → ∀ (S : Sylow 2 H) (K : Subgroup H),
      IsComponent H K → IsSimpleGroup K → ¬K.Normal →
      K ⊔ (S : Subgroup H) = ⊤ →
      ∀ (R : Sylow 2 (NormalizerAction.Star K)),
        (R : Subgroup (NormalizerAction.Star K)) = NormalizerAction.sylowImage K S →
        ChapterB.IsMinimalParabolicOver R ⊤ → ChapterB.IsMinimalParabolicOver S ⊤

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.ModelGeneration.Cover
