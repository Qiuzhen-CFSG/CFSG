module

public import CFSG.Quasithin.ChapterI.Section01.LieMultipliers.G2
public import Theory.SpecificGroups.G2.FourNontrivialCover

/-!
# The Conway square in the G₂(4) multiplier calculation

The marked Conway square constructs a finite quasisimple pullback with
nontrivial center and the actual G₂(4) central quotient. Applying the
existing source-cover comparison supplies the cyclic order-two canonical
kernel once its independent upper bound is proved.

The Conway embedding, marked isometry, and upper bound remain explicit
inputs. This is the assembly of those independent results, not an
unconditional proof of Aschbacher–Smith I.1.3(1), printed p.407. The
geometric construction comes from the I.2.2(5) argument on printed p.411.
-/

namespace CFSG.Quasithin.ChapterI.LieMultipliers.G2

open Theory.GroupTheory Atlas.Conway Atlas.Lattices Atlas.G2.FiniteCover
open Atlas.G2.FourNontrivialCover

/-- Actual consumer application of the constructed pullback to the source
multiplier comparison, retaining only the independent geometric and upper-bound inputs. -/
public theorem fourKernel_equiv_two_of_conway_square
    (j : FourBase →* LeechCentralQuotient) (hj : Function.Injective j)
    (b : FourBase) (a : LeechIsometryGroup)
    (ha : leechCentralProjection a = j b) (hsq : a ^ 2 = negationIsometry)
    (hbound : Nat.card (Kernel FourField) ≤ 2) :
    Nonempty (Kernel FourField ≃* Multiplicative (ZMod 2)) := by
  let : IsQuasisimple (pullback j) := isQuasisimple_of_marked_square j hj b a ha hsq
  exact fourKernel_equiv_two_of_source_cover
    (quotientCenterEquivOfMarkedSquare j hj b a ha hsq) (center_ne_bot j) hbound

end CFSG.Quasithin.ChapterI.LieMultipliers.G2
