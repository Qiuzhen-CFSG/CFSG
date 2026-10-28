module

public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizerBlockCentralizerMovement
public import Theory.GroupTheory.CommutatorPreimage

/-!
# Local invariance and the terminal block branches

The source uses X=O²(C_L(Ω₁Z(T))) and R=O₂(XT) in the alternating-six
and G₂(2) rows. In the linear-three row it uses the preimage of the center
of T/O₂(LT). The latter is expressed by its literal commutator condition.
These definitions do not assume that either construction is invariant under
the whole Sylow normalizer.

The three source implications below separate local invariance from its two
independent geometric consumers. Their premises remain explicit until final
assembly discharges them. Movement and disjoint Sylow centralizers are already
constructed in the imported module; the chosen V is not identified with the
omega-center-generated module.

Source: Aschbacher–Smith 3.3.23–31, printed pp.598–602.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizer
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The original residual of the centralizer inside L, mapped into G. -/
def blockLocalResidual (T : Sylow 2 G) (L : Subgroup G) : Subgroup G :=
  (pResidual 2 (L ⊓ centralizer (omegaCenterIn (T : Subgroup G) : Set G) : Subgroup G)).map
    (L ⊓ centralizer (omegaCenterIn (T : Subgroup G) : Set G)).subtype

/-- The two-core of the literal local residual join. -/
def blockLocalCore (T : Sylow 2 G) (L : Subgroup G) : Subgroup G :=
  (blockLocalResidual T L ⊔ (T : Subgroup G)).pCoreIn 2

/-- Preimage of Z(T/O₂(LT)), retaining its commutator description. -/
def blockLinearCentralPreimage (T : Sylow 2 G) (L : Subgroup G) : Subgroup G :=
  commutatorPreimage (T : Subgroup G) (T : Subgroup G)
    ((L ⊔ (T : Subgroup G)).pCoreIn 2)

/-- The exact local invariance used by the terminal geometric argument. -/
def BlockLocalInvariance (T : Sylow 2 G) (L : Subgroup G) : Prop :=
  ((ChapterC.IsAlternatingBlock L 6 ∨ ChapterC.IsG2TwoBlock L) →
    normalizer (T : Set G) ≤ normalizer (blockLocalResidual T L : Set G) ∧
    normalizer (T : Set G) ≤ normalizer (blockLocalCore T L : Set G)) ∧
  (ChapterC.IsLinearTwoBlock L 3 → normalizer (T : Set G) ≤
    normalizer (blockLinearCentralPreimage T L : Set G))

/-- Earlier-source producer of 3.3.23(1) and 3.3.25(2). -/
def BlockLocalInvarianceSource (T : Sylow 2 G) (L V : Subgroup G) : Prop :=
  Hypothesis1223 KnownSimple.IsKnownSimple T L → ChosenModule T L V →
    Structural1222.{u} KnownSimple.IsKnownSimple → NoEscape L V →
    V ⊓ centralizer (L : Set G) ≠ ⊥ →
    ¬ normalizer (T : Set G) ≤ normalizer (L : Set G) → BlockAlternative L →
    BlockLocalInvariance T L

/-- The G₂(2) and L₃(2) eliminations with local invariance explicit. -/
def NonalternatingBlockCentralizerSource (T : Sylow 2 G) (L V : Subgroup G) : Prop :=
  Hypothesis1223 KnownSimple.IsKnownSimple T L → ChosenModule T L V →
    Structural1222.{u} KnownSimple.IsKnownSimple → NoEscape L V →
    V ⊓ centralizer (L : Set G) ≠ ⊥ →
    ¬ normalizer (T : Set G) ≤ normalizer (L : Set G) →
    BlockLocalInvariance T L → (ChapterC.IsG2TwoBlock L ∨ ChapterC.IsLinearTwoBlock L 3) →
    (T : Subgroup G) ⊓ centralizer (L : Set G) = ⊥

/-- The alternating-six terminal argument with local invariance explicit. -/
def AlternatingBlockCentralizerSource (T : Sylow 2 G) (L V : Subgroup G) : Prop :=
  Hypothesis1223 KnownSimple.IsKnownSimple T L → ChosenModule T L V →
    Structural1222.{u} KnownSimple.IsKnownSimple → NoEscape L V →
    V ⊓ centralizer (L : Set G) ≠ ⊥ →
    ¬ normalizer (T : Set G) ≤ normalizer (L : Set G) →
    BlockLocalInvariance T L → ChapterC.IsAlternatingBlock L 6 →
    (T : Subgroup G) ⊓ centralizer (L : Set G) = ⊥

/-- Assembly discharges local invariance before using either terminal branch. -/
theorem blockCentralizerSource_of_local_branches {T : Sylow 2 G} {L V : Subgroup G}
    (localSource : BlockLocalInvarianceSource T L V)
    (nonalternating : NonalternatingBlockCentralizerSource T L V)
    (alternating : AlternatingBlockCentralizerSource T L V) :
    BlockCentralizerSource T L V := by
  intro h D structural hnone hfixed hescape hb
  have hi := localSource h D structural hnone hfixed hescape hb
  rcases hb with ha | hb
  · exact alternating h D structural hnone hfixed hescape hi ha
  · exact nonalternating h D structural hnone hfixed hescape hi hb

/-- Literal application to the original reducible normalizer consumer. -/
theorem sylow_normalizer_le_of_local_block_branches {T : Sylow 2 G} {L V : Subgroup G}
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple) (hnone : NoEscape L V)
    (hfixed : V ⊓ centralizer (L : Set G) ≠ ⊥)
    (reduction : BlockReductionSource T L V)
    (localSource : BlockLocalInvarianceSource T L V)
    (nonalternating : NonalternatingBlockCentralizerSource T L V)
    (alternating : AlternatingBlockCentralizerSource T L V) :
    normalizer (T : Set G) ≤ normalizer (L : Set G) :=
  sylow_normalizer_le_of_block_sources h D structural hnone hfixed reduction
    (blockCentralizerSource_of_local_branches localSource nonalternating alternating)

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizer
