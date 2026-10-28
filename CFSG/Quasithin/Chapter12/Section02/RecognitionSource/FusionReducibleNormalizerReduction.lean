module

public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizerSetup
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.Basic
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.G2

/-!
# The two remaining source inputs for the reducible Sylow normalizer

In a counterexample to 3.3.1, the reduction through 3.3.25(1) gives an
actual A₆, G₂(2), or L₃(2) block. The terminal argument through 3.3.31
forces C_T(L) to vanish. For the original reducible chosen module this
contradicts C_V(L) ≠ 1, since V ≤ T.

This module publishes the exact independent contracts and their application
to 12.2.16. Both contracts remain explicit earlier-source obligations; this
conditional assembly does not claim the requested normalizer containment
without them. Each block predicate includes the actual quotient and natural
module model, not a group-family tag.

Source: Aschbacher–Smith 3.3.8–31, printed pp.587–602; 12.2.16, pp.799–800.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizer
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The surviving intrinsic block types of 3.3.25(1), with concrete models. -/
def BlockAlternative (L : Subgroup G) : Prop :=
  ChapterC.IsAlternatingBlock L 6 ∨ ChapterC.IsG2TwoBlock L ∨
    ChapterC.IsLinearTwoBlock L 3

/-- The block reduction required only at the actual reducible consumer. -/
def BlockReductionSource (T : Sylow 2 G) (L V : Subgroup G) : Prop :=
  Hypothesis1223 KnownSimple.IsKnownSimple T L → ChosenModule T L V →
    Structural1222.{u} KnownSimple.IsKnownSimple → NoEscape L V →
    V ⊓ centralizer (L : Set G) ≠ ⊥ →
    ¬ normalizer (T : Set G) ≤ normalizer (L : Set G) → BlockAlternative L

/-- The terminal source branch may be proved independently with the actual
block alternative explicit. Its producer must discharge all its local geometry. -/
def BlockCentralizerSource (T : Sylow 2 G) (L V : Subgroup G) : Prop :=
  Hypothesis1223 KnownSimple.IsKnownSimple T L → ChosenModule T L V →
    Structural1222.{u} KnownSimple.IsKnownSimple → NoEscape L V →
    V ⊓ centralizer (L : Set G) ≠ ⊥ →
    ¬ normalizer (T : Set G) ≤ normalizer (L : Set G) → BlockAlternative L →
    (T : Subgroup G) ⊓ centralizer (L : Set G) = ⊥

/-- Actual application: the two independent earlier-source implications
suffice for the exact Sylow-normalizer premise in the reducible fusion rows. -/
theorem sylow_normalizer_le_of_block_sources
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple) (hnone : NoEscape L V)
    (hne : V ⊓ centralizer (L : Set G) ≠ ⊥)
    (reduction : BlockReductionSource T L V) (terminal : BlockCentralizerSource T L V) :
    normalizer (T : Set G) ≤ normalizer (L : Set G) := by
  by_contra hescape
  have hblock := reduction h D structural hnone hne hescape
  exact sylow_centralizer_ne_bot D hne (terminal h D structural hnone hne hescape hblock)

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizer
