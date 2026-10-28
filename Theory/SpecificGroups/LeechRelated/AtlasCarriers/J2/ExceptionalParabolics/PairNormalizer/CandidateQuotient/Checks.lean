module
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.PairNormalizer.CandidateQuotient.Data

/-!
# Checked multiplication and separation of the eighteen quotient representatives

Every model product is lifted to an equality of degree-100 permutations with
an explicit radical factor. Comparing images of points 0, 1 and 2 shows that
only the identity representative can lie in the radical. These are kernel
computations on the original ATLAS carrier, with no assumed group order or
splitting. Source: GLS3 Table 5.3g; Aschbacher--Smith, printed p.511.
-/

@[expose] public section
namespace Sporadic.LeechRelated.J2.ExceptionalParabolics.PairNormalizer.CandidateQuotient
open Theory.GroupTheory GeneratorPair.SecondOrbitCertificate Seed RadicalData

set_option maxRecDepth 100000

theorem model_bijective : Function.Bijective model := by
  decide +kernel

theorem model_mul : ∀ i j, model (mulIndex i j) = model i * model j := by
  apply allFin
  decide +kernel

theorem repTable_mul : ∀ i j,
    repTable i * repTable j = qTable (radicalFactor i j) * repTable (mulIndex i j) := by
  apply allFin
  decide +kernel

theorem repTable_separation : ∀ i j,
    (repTable i 0, repTable i 1, repTable i 2) =
      (qTable j 0, qTable j 1, qTable j 2) → i = 0 := by
  apply allFin
  decide +kernel

end Sporadic.LeechRelated.J2.ExceptionalParabolics.PairNormalizer.CandidateQuotient
