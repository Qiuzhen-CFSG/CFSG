module
public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal.NormalizerModule.AbelianSection.Incidence
public import Theory.GroupTheory.PGroup.Omega

/-!
# Concrete model premises for the conditional HS abelian section

These are properties of the actual degree-100 HS carrier and the specified
elementary-eight normalizer. In particular the coordinate equivalence is on
its literal two-core, and the omega subgroup is marked by the original
inclusion. No assertion about a cover core or its Frattini section is an input.

Source: Aschbacher–Smith I.2.2(5), final HS paragraph, p.412 / PDF p.423;
GLS3 Table 5.3m and the action on the elementary eight on p.306.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal.AbelianSection
open Sporadic.LeechRelated.HS.BlockNormalizer
open Sporadic.LeechRelated.HS.EvenLocalCandidates

variable {K : Type*} [Group K]

/-- The earlier centralizer restriction inputs, discharged by the higher HS
assembly. They do not assume any normalizer-cover incidences. -/
structure CentralizerInput
    (e : (K ⧸ center K) ≃* Sporadic.LeechRelated.HS.Carrier) (u : K) : Prop where
  center_le : center K ≤ centralizerTwoResidual u
  residual_image : (centralizerTwoResidual u).map (modelMap e) = centralizerTwoResidual e0
  center_image : (coreCenter u).map (modelMap e) = coreCenter e0
  centralizes : centralizerTwoResidual u ≤ centralizer (coreCenter u : Set K)

/-- Model facts to be supplied by the concrete normalizer geometry owner. -/
structure ModelInput where
  coordinates : pCore 2 baseNormalizer ≃* Multiplicative (Fin 3 → ZMod 4)
  omega_image :
    ((omega (pCore 2 baseNormalizer) (p := 2) 1).map
      (pCore 2 baseNormalizer).subtype).map baseNormalizer.subtype = baseElementary
  seven : Sylow 7 baseNormalizer
  seven_fixed : pCore 2 baseNormalizer ⊓ centralizer (seven : Set baseNormalizer) = ⊥
  core_le_residual :
    (pCore 2 baseNormalizer).map baseNormalizer.subtype ≤ centralizerTwoResidual e0
  center_le_normalizer : coreCenter e0 ≤ baseNormalizer
  center_generates :
    normalClosure ((coreCenter e0).subgroupOf baseNormalizer : Set baseNormalizer) =
      pCore 2 baseNormalizer
  elementary_le_core : baseElementary ≤ centralizerCore e0

end CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal.AbelianSection
