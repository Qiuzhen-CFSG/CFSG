module
public import Theory.SpecificGroups.McLaughlin.Multiplier.ModelComparison.Action
public import Theory.SpecificGroups.McLaughlin.Multiplier.ModelComparison.GeneratorLifts.Points
public import Theory.SpecificGroups.McLaughlin.Multiplier.ModelComparison.GeneratorLifts.LatticeIsometries
public import Theory.SpecificGroups.McLaughlin.Multiplier.ModelComparison.GeneratorLifts.PointActionA
public import Theory.SpecificGroups.McLaughlin.Multiplier.ModelComparison.GeneratorLifts.PointActionB
/-!
# Lifts of the literal McLaughlin generators

The two rational matrices preserve the Leech form and lattice in both
directions and fix the marked norm-six vector and endpoint. Restriction thus
places them in the actual triangle stabilizer. Their integer point-image
certificates give the exact inverse-source degree-275 permutations under one
common labelling. The faithful action extends these lifts to an unconditional
marked embedding of the original carrier.

Coordinates and Leech geometry follow Gerald Höhn's ATLAS, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917 (LICENSES/ATLAS.txt and
LICENSES/ATLAS-CITATION.cff). The original permutation convention is
ATLAS McLG1-p275B0, inverted for a left action. The discovery data are
untrusted witnesses; every assertion used here is proved in Lean's kernel.
-/
@[expose] public section
noncomputable section
namespace Theory.SpecificGroups.McLaughlin.Multiplier.ModelComparison
open Atlas.Lattices
open Sporadic.LeechRelated.McL

theorem markedLiftA_apply (x : Fin 275) :
    markedLiftA • markedPointEquiv x = markedPointEquiv (generatorA x) := by
  apply Subtype.ext
  apply Subtype.ext
  apply rationalEmbedding_injective
  change rationalEmbedding (restrictToLeech rationalIsometryA (markedPoint x).val).val = _
  rw [restriction_agrees]
  exact mapA_point x

theorem markedLiftB_apply (x : Fin 275) :
    markedLiftB • markedPointEquiv x = markedPointEquiv (generatorB x) := by
  apply Subtype.ext
  apply Subtype.ext
  apply rationalEmbedding_injective
  change rationalEmbedding (restrictToLeech rationalIsometryB (markedPoint x).val).val = _
  rw [restriction_agrees]
  exact mapB_point x

/-- Lifts of the original two generators in the actual marked Leech model. -/
def generatorLifts : GeneratorLifts where
  pointEquiv := markedPointEquiv
  liftA := markedLiftA
  liftB := markedLiftB
  liftA_apply := markedLiftA_apply
  liftB_apply := markedLiftB_apply

/-- The marked embedding needs no order or graph-automorphism recognition. -/
def markedCarrierEmbedding : Carrier →* Atlas.Sporadic.McLaughlin.Model :=
  generatorLifts.carrierEmbedding

theorem markedCarrierEmbedding_injective : Function.Injective markedCarrierEmbedding :=
  generatorLifts.carrierEmbedding_injective

theorem markedCarrierEmbedding_apply (g : Carrier) (x : Fin 275) :
    markedCarrierEmbedding g • markedPointEquiv x = markedPointEquiv (g.val x) :=
  generatorLifts.carrierEmbedding_apply g x

end Theory.SpecificGroups.McLaughlin.Multiplier.ModelComparison
