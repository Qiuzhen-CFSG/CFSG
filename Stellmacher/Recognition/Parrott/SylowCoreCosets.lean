module

public import Stellmacher.Recognition.Parrott.SylowCoreCoefficients
public import Stellmacher.Recognition.Parrott.SylowCoreCovariance

/-!
# Correlated core cosets in the initial Parrott frame

The initial action gives the four covariance identities for the derived-core
commutator `p = [a,d]` and square `k = c²`.  The coefficient calculation then
extracts one Boolean choice for all five central cosets.  This module performs
that final assembly while retaining the supplied coordinates.

Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
printed pp.678–679, equations (11)–(15).
-/

namespace Stellmacher.Recognition.ParrottSylowInitialData

variable {G : Type*} [Group G] {z : G}
variable {e : ParrottSecondElementaryData z}
variable {n : ParrottNormalizerFusionData e}

/-- The five correlated core coset alternatives for the supplied initial frame.

The nonsolvability, `N₂` and simplicity hypotheses are part of the global
Parrott context.  The local calculation itself uses the centralizer
hypotheses to establish covariance and the elementary coefficient argument to
select the common Boolean.
-/
public theorem exists_core_coset_alternatives [Finite G] [IsSimpleGroup G]
    (f : ParrottSylowInitialData n) (_hns : ¬ Group.IsSolvable G)
    (_hN : IsNTwoGroup G) (h : ParrottCentralizerHypotheses z) :
    ∃ caseTwo : Bool, f.CoreCosetAlternatives caseTwo := by
  have hc : f.CoreCovariance := f.core_covariance h
  exact f.exists_core_coset_alternatives_of_covariance h hc

end Stellmacher.Recognition.ParrottSylowInitialData
