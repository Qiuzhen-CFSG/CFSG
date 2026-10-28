module

public import Theory.SpecificGroups.Triality.RadicalCoordinates.FixedPoints
public import Theory.SpecificGroups.Triality.ConcreteBruhat.Torus.Borel

/-!
# The full split Levi in the triality parabolics

GLS3 distinguishes the subsystem subgroup M_J from the full Levi H M_J.
Here `splitLevi` is M_J, and adjoining the original coroot torus gives the
full Levi candidate. Both factors are graph-field invariant. This module
only supplies its definition, containment and invariance; the product and
fixed-point assertions require further mathematics.

Source: GLS3 Definition 2.6.4 and Theorem 2.6.5(f,g)
(`refs/KGroup/GLS3/chapter2.tex`).
-/

@[expose] public section
noncomputable section
namespace Triality.Standard.RadicalCoordinates
open Parabolics ConcreteBruhat

/-- GLS3's full split Levi, retaining the torus omitted from `splitLevi`. -/
def splitFullLevi (P : Parameters) (a : Node) : Subgroup (SplitGroup P) :=
  splitLevi P a ⊔ splitTorus P

theorem splitFullLevi_le_splitParabolic (P : Parameters) (a : Node) :
    splitFullLevi P a ≤ splitParabolic P a :=
  sup_le (splitLevi_le_splitParabolic P a)
    ((splitTorus_le_splitBorel P).trans le_sup_left)

theorem splitFullLevi_invariant (P : Parameters) (a : Node) :
    (splitFullLevi P a).map (graphFieldAutomorphism P).toMonoidHom =
      splitFullLevi P a := by
  rw [splitFullLevi, Subgroup.map_sup, splitLevi_invariant, splitTorus_invariant]

end Triality.Standard.RadicalCoordinates
