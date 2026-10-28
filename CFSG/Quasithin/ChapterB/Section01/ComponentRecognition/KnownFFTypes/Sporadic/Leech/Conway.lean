module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Leech.Conway.Reduction

/-!
# Conditional assembly of the three Conway FF exclusions

The common reduction has been applied separately to the exact Co₁, Co₂ and Co₃
catalogue carriers. The generation/rank estimates and the small-module
normalizer estimates are still explicit inputs. These declarations are not
unconditional proofs of the three source exclusions.

Source target: Aschbacher–Smith B.1.13, printed pp.73–74, using Guralnick–Malle,
*Classification of 2F-modules, II*, Table 2. The catalogue models are
`Co1G1-f2r24B0`, `Co2G1-p2300B0` and `Co3G1-p276B0`; no lattice-model comparison
is used here.
-/

public section
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.Leech
universe u v

/-- Conditional Co₁ assembly, retaining both missing model estimates. -/
theorem faithfulExclusion_co1_of_estimates
    (hglobal : Conway.NormalizerEstimates.{u,v} .co1)
    (hsmall : Conway.SmallModuleEstimate.{u,v} .co1) : FaithfulExclusion.{u,v} .co1 :=
  Conway.exclusion_of_estimates .co1 hglobal hsmall

/-- Conditional Co₂ assembly, retaining both missing model estimates. -/
theorem faithfulExclusion_co2_of_estimates
    (hglobal : Conway.NormalizerEstimates.{u,v} .co2)
    (hsmall : Conway.SmallModuleEstimate.{u,v} .co2) : FaithfulExclusion.{u,v} .co2 :=
  Conway.exclusion_of_estimates .co2 hglobal hsmall

/-- Conditional Co₃ assembly, retaining both missing model estimates. -/
theorem faithfulExclusion_co3_of_estimates
    (hglobal : Conway.NormalizerEstimates.{u,v} .co3)
    (hsmall : Conway.SmallModuleEstimate.{u,v} .co3) : FaithfulExclusion.{u,v} .co3 :=
  Conway.exclusion_of_estimates .co3 hglobal hsmall

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.Leech
