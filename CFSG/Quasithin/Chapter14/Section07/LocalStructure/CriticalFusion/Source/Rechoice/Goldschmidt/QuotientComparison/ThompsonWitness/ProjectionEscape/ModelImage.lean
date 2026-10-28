module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.QuotientComparison.ThompsonWitness.ProjectionEscape
public import Theory.SpecificGroups.PSL3Two.Parabolics.ProjectionResidualImage

/-!
# The finite parabolic image calculation in 14.7.70

The source's literal YT action has a two-group kernel and image S₃. The
independent finite-group theorem therefore supplies `ParabolicImageTheorem`
with no extra mathematical premises. Its residual image is the marked
line A₄, and the subgroup mapping onto the Borel has nontrivial S₃ image.

The two consumer theorems below discharge this model premise in the actual
normalizer escape and Thompson arguments. Construction of the genuine
normalizer projection remains independent, owned by
qt-14-07-rechoice-escape-normalizer-projection; the earlier source inputs
retain their original producers and final assembly remains with
qt-14-07-rechoice-witness-normalizer-escape.

Source: Aschbacher–Smith, combined manuscript, 1 March 2004,
Lemma 14.7.70, printed p.1074 (PDF p.1091).
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.QuotientComparison.ThompsonWitness.ProjectionEscape
open Representation Chapter12.Section08 Stellmacher
universe u

/-- The independent finite-model contract, in every universe and with the
original homomorphisms and residual conventions. -/
theorem parabolicImageTheorem : ParabolicImageTheorem.{u} := by
  intro X _ _ f hf hk π A hA hescape
  exact Matrix.PSL3Two.ProjectionResidualImage.parabolic_residual_image
    f hf hk π A hA hescape

variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  {d : Data T L V F W} {c : CriticalPath (L := L) F}

/-- The actual escape consumer now requires only the independent normalizer
projection construction; its finite-model premise is proved here. -/
theorem normalizer_escape_with_projection
    (p : NormalizerProjection T L V F) (h : Geometry d c) (k : CoreFacts c) :
    ¬ Y c ≤ normalizer (L : Set G) :=
  normalizer_escape_of_projection p parabolicImageTheorem h k

/-- Discharge the same model premise in the original Thompson application,
retaining its genuine earlier-source and normalizer-projection inputs. -/
theorem thompson_escape_with_projection
    (p : NormalizerProjection T L V F) (h : Geometry d c) (k : CoreFacts c)
    (earlier : EarlierSetupResults KnownSimple.IsKnownSimple.{u})
    (thompson : EarlierThompsonNormality.{u}) :
    ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ (I c).pCoreIn 2 :=
  thompson_escape_of_projection p parabolicImageTheorem h k earlier thompson

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.QuotientComparison.ThompsonWitness.ProjectionEscape
