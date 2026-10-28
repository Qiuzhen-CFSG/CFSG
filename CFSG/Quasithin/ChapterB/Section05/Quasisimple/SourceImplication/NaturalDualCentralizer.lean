module

public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.NaturalDualCentralizer.Reduction
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.NaturalDualCentralizer.IncidentStructure
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.NaturalDualCentralizer.IncidentOffenders

/-!
# The natural-plus-dual branch of B.5.1(6)

For the actual natural-plus-dual action of SL_d(2), with d = 4 or 5,
the pointwise centralizer of every Sylow fixed space has extraspecial
two-core of order `2^(1+2*(d-2))`, quotient PSL_(d-2)(2), and no best
offender contained in the ambient image of its two-core.

The Sylow fixed space consists of two incident endpoint lines. Its literal
centralizer is identified with their pair stabilizer using the specified
SL-to-linear equivalence. The incident-pair structure and displacement
calculations discharge both remaining inputs of that reduction. No
classification or induction hypothesis enters this theorem. Transport to
arbitrary marked actions and trivial summands remains with the full B.5.1
assembly.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.5.1(6),
printed pp.99 and 103.
-/

public section

namespace CFSG.Quasithin.ChapterB.QuasisimpleSource.NaturalDualCentralizer

/-- The concrete natural-plus-dual calculation in B.5.1(6), with both the
incident core structure and offender exclusion proved. -/
theorem sylowFixedCentralizer_naturalPlusDual {d : ℕ} (hd : d = 4 ∨ d = 5)
    (T : Sylow 2 (Matrix.SpecialLinearGroup (Fin d) (ZMod 2))) :
    Nonempty (SylowFixedCentralizer (naturalPlusDual d) ⊤ d T) :=
  sylowFixedCentralizer_of_incident_structure hd (incident_core_structure hd) T

end CFSG.Quasithin.ChapterB.QuasisimpleSource.NaturalDualCentralizer
