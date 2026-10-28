module

public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.SourceCompletion.CanonicalRadical
public import CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination.SourceControl

/-!
# The canonical radical's starred membership and literal control consumer

Apply the source-complete C.2.7 exclusion to the original Ξ_p(L), and feed its
starred membership to `Context.control_of_radical_star`. The original Context
and OrbitFacts contracts are preserved. The actual marked A.3.12 input is
proved from the full containing-model catalogue and signed odd-ternary
extension, so starred membership needs only Context. The control application
retains exactly the earlier OrbitFacts required by its original consumer.
Source: Aschbacher–Smith, 13.1.4(4), printed pp.867–868, using 1.3.8, pp.512–514.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination
open Chapter1 Chapter1.Section02
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L : Subgroup G} {p : ℕ} [Fact p.Prime]

/-- The original canonical radical is starred once the genuine earlier A.3.12
embedding input is supplied. C.2.7 is discharged on the actual pushing-up group. -/
theorem Context.radical_star_of_marked_A312 (h : Context T L p)
    (hMarked : RadicalNormalizers.MarkedA312Input p L T) :
    XiP p L ∈ XiStar G (T : Subgroup G) :=
  RadicalExclusions.ModelReduction.XiP_mem_XiStar_of_marked_A312
    h.hypothesis.simpleQTKE T h.maximal.1 h.nonquasisimple h.odd h.divides hMarked

/-- Apply the original radical's exclusion to the literal local control consumer,
retaining the explicit marked input for compatibility. -/
theorem Context.control_of_marked_A312 (h : Context T L p) (o : OrbitFacts T L p)
    (hMarked : RadicalNormalizers.MarkedA312Input p L T) : Control T L p :=
  h.control_of_radical_star o (h.radical_star_of_marked_A312 hMarked)

/-- Original 13.1.4(4): the canonical radical is starred under the published
Context, with all marked embedding and pushing-up model premises discharged. -/
theorem Context.radical_star (h : Context T L p) :
    XiP p L ∈ XiStar G (T : Subgroup G) :=
  RadicalExclusions.ModelReduction.XiP_mem_XiStar_knownSimple
    h.hypothesis.simpleQTKE T h.maximal.1 h.nonquasisimple h.odd h.divides

/-- The literal local control consumer with no additional radical-star premise. -/
theorem Context.control (h : Context T L p) (o : OrbitFacts T L p) : Control T L p :=
  h.control_of_radical_star o h.radical_star

end CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination
