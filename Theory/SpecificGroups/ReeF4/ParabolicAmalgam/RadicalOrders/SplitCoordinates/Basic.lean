module

public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.RadicalOrders.Coordinates

/-!
# The height filtration for split Ree coordinates

All three supports consist of positive roots. Their integral base heights
therefore give positive natural degrees, independently of the field size.
These degrees are used both to collect root factors and to recover parameters
from the Cartan columns of their actual matrix product.

Source: the ordered Chevalley root construction underlying Aschbacher–Smith,
F.1.12(I)(5), printed p.263 of `refs/quasithin.pdf`.
-/

@[expose] public section
noncomputable section

namespace ReeF4.Parabolics.RadicalCoordinates

open Theory.AlgebraicGroup StandardRootSystem

/-- The natural degree of a root; it agrees with base height on our supports. -/
def rootDegree (r : F4Chevalley.Root) : ℕ :=
  (typeF4RootPairing_base.height r).toNat

theorem supported_isPos {k : Support} (r : Root k) :
    typeF4RootPairing_base.IsPos r.val := by
  cases k with
  | positive => exact r.property
  | radical s => exact r.property.1

theorem rootDegree_pos {k : Support} (r : Root k) : 0 < rootDegree r.val := by
  have h := supported_isPos r
  change 0 < typeF4RootPairing_base.height r.val at h
  exact Int.pos_iff_toNat_pos.mp h

theorem rootDegree_cast {k : Support} (r : Root k) :
    (rootDegree r.val : ℤ) = typeF4RootPairing_base.height r.val :=
  Int.toNat_of_nonneg (le_of_lt (supported_isPos r))

end ReeF4.Parabolics.RadicalCoordinates
