module

public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizerBlockReductionRows
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizerBlockReductionControl

/-!
# Specialized block reduction for the reducible chosen module

An escaping Sylow normalizer supplies the multiple-overgroup guard for
the separate seven-row classification. Nonzero fixed space reduces that
classification to four actual chosen-module models. The eight-letter row
is excluded by the residual and Thompson identities of 3.3.21(d–e);
the other three rows require their intrinsic block constructions.

The contracts below are explicit unfinished source implications. This
conditional assembly proves neither their hypotheses nor the unconditional
block reduction. In particular a marked action on the chosen V alone is
not asserted to identify the canonical block module or the entire two-core.

Source: Aschbacher–Smith 3.3.21(d–e), 3.3.23–25, printed pp.596–600;
12.2.2(3) and 12.2.16, pp.795,799–800.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizer
open ChapterB.QuasisimpleSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The two literal identities used in the shortened 3.3.21(e) argument.
The first residual is O^{3'}, whereas the component residual is O². -/
def OmegaResidualIdentities (T : Sylow 2 G) (L : Subgroup G) : Prop :=
  (primeToResidual 3 (centralizer (omegaCenterIn (T : Subgroup G) : Set G))).map
      (centralizer (omegaCenterIn (T : Subgroup G) : Set G)).subtype = omegaLocalResidual T L ∧
    elementaryAbelianMaxJ (omegaResidualCore T L) =
      elementaryAbelianMaxJ ((L ⊔ (T : Subgroup G)).pCoreIn 2)

/-- Reconstruction of the intrinsic binary linear block from the actual
four-dimensional extension row, including elimination of the MS shadows. -/
def LinearThreeBlockConstruction (T : Sylow 2 G) (L V : Subgroup G) : Prop :=
  Hypothesis1223 KnownSimple.IsKnownSimple T L → ∀ D : ChosenModule T L V,
    Structural1222.{u} KnownSimple.IsKnownSimple → NoEscape L V →
    V ⊓ centralizer (L : Set G) ≠ ⊥ →
    ¬ normalizer (T : Set G) ≤ normalizer (L : Set G) →
    Section04.SmallFusion.SLThreeExtension D → ChapterC.IsLinearTwoBlock L 3

/-- Reconstruction from the original faithful A₆ action. The actor is
L/C_L(V); any identification with L/O₂(L) must be proved by the producer. -/
def AlternatingSixBlockConstruction (T : Sylow 2 G) (L V : Subgroup G) : Prop :=
  Hypothesis1223 KnownSimple.IsKnownSimple T L → ∀ D : ChosenModule T L V,
    Structural1222.{u} KnownSimple.IsKnownSimple → NoEscape L V →
    V ⊓ centralizer (L : Set G) ≠ ⊥ →
    ¬ normalizer (T : Set G) ≤ normalizer (L : Set G) →
    (letI := D.actionCentralizer_normal;
      ActionEquiv D.faithfulAction (BinaryPermutation.alternatingCoreRepresentation (Fin 6))) →
    ChapterC.IsAlternatingBlock L 6

/-- Reconstruction from the genuine seven-dimensional Weyl model for
G₂(2)′, with the original quotient actor. -/
def G2BlockConstruction (T : Sylow 2 G) (L V : Subgroup G) : Prop :=
  Hypothesis1223 KnownSimple.IsKnownSimple T L → ∀ D : ChosenModule T L V,
    Structural1222.{u} KnownSimple.IsKnownSimple → NoEscape L V →
    V ⊓ centralizer (L : Set G) ≠ ⊥ →
    ¬ normalizer (T : Set G) ≤ normalizer (L : Set G) →
    ActionEquiv D.quotientAction (Atlas.G2.Natural.OrthogonalCover.action (ZMod 2)) →
    ChapterC.IsG2TwoBlock L

/-- Only the local residual and Thompson identities are required from the
eight-letter geometry; the normalizer contradiction is proved below. -/
def AlternatingEightResidualConstruction (T : Sylow 2 G) (L V : Subgroup G) : Prop :=
  Hypothesis1223 KnownSimple.IsKnownSimple T L → ∀ D : ChosenModule T L V,
    Structural1222.{u} KnownSimple.IsKnownSimple → NoEscape L V →
    V ⊓ centralizer (L : Set G) ≠ ⊥ →
    ¬ normalizer (T : Set G) ≤ normalizer (L : Set G) →
    ActionEquiv D.quotientAction (BinaryPermutation.alternatingCoreRepresentation (Fin 8)) →
    OmegaResidualIdentities T L

/-- Conditional assembly of the four concrete rows. The guarded module
classification and all four reconstruction implications remain explicit. -/
theorem blockReductionSource_of_model_constructions
    (modules : Theorem1222ModulesOfMany.{u} KnownSimple.IsKnownSimple)
    (linearThree : LinearThreeBlockConstruction T L V)
    (six : AlternatingSixBlockConstruction T L V)
    (g2 : G2BlockConstruction T L V)
    (eight : AlternatingEightResidualConstruction T L V) : BlockReductionSource T L V := by
  intro h D structural hnone hne hescape
  cases reducibleModels_of_escape modules h D hne hescape with
  | linearThree E => exact Or.inr (Or.inr (linearThree h D structural hnone hne hescape E))
  | alternatingSix E => exact Or.inl (six h D structural hnone hne hescape E)
  | g2 E => exact Or.inr (Or.inl (g2 h D structural hnone hne hescape E))
  | alternatingEight E =>
      obtain ⟨he, hJ⟩ := eight h D structural hnone hne hescape E
      exact (hescape (sylow_normalizer_le_of_omegaResidual_thompson h D he hJ)).elim

/-- Application to the preserved parent interface. The independent terminal
block-centralizer theorem is used exactly as in the original assembly. -/
theorem sylow_normalizer_le_of_model_constructions
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple) (hnone : NoEscape L V)
    (hne : V ⊓ centralizer (L : Set G) ≠ ⊥)
    (modules : Theorem1222ModulesOfMany.{u} KnownSimple.IsKnownSimple)
    (linearThree : LinearThreeBlockConstruction T L V)
    (six : AlternatingSixBlockConstruction T L V)
    (g2 : G2BlockConstruction T L V)
    (eight : AlternatingEightResidualConstruction T L V)
    (terminal : BlockCentralizerSource T L V) :
    normalizer (T : Set G) ≤ normalizer (L : Set G) :=
  sylow_normalizer_le_of_block_sources h D structural hnone hne
    (blockReductionSource_of_model_constructions modules linearThree six g2 eight) terminal

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizer
