module

public import CFSG.Quasithin.ChapterG.Section11.StrictWholeExclusion

/-!
# The strict exclusion selects the equality branch

The original strict-intersection contradiction is re-exported from
`StrictWholeExclusion`. Its proof constructs the crossing cubic and literal
quotient action, excludes the thirteen catalogue rows and exceptional full-four
action, and eliminates the remaining whole components.

Since Z_S lies in U ∩ V, this contradiction gives U ∩ V = Z_S for the
original sourceClosure U and layer V. This is the branch premise consumed by
the equality recognition; no equality-branch core or classification witness
is assumed. The earlier LocalAnalysis remains an input of the identification
assembly.

Source: Aschbacher--Smith, 6.2.13--19, printed pp.687--691.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M R : Subgroup G} {n : ℕ} {z : G}

/-- Excluding strict intersection supplies the literal equality-branch premise. -/
theorem LocalAnalysis.sourceClosure_intersection_eq_ZS
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hTH : (T : Subgroup G) ≤ centralizer ({z} : Set G)) :
    sourceClosure (T : Subgroup G) L R z ⊓ layer L R = ZS (T : Subgroup G) L R := by
  rcases eq_or_lt_of_le (ZS_le_sourceClosure_intersection h611 hz) with heq | hstrict
  · exact heq.symm
  · exact (A.false_of_local_analysis_of_strict_intersection
      h611 hnatural hz horder hTH hstrict).elim

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
