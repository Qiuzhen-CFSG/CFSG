module

public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.M12Local.CoverCoordinates.Quadratic
public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.M12Local.CoverCoordinates.SymplecticCore

/-!
# Marked square coordinates on the actual M₁₂ cover

The common symplectic-core construction identifies the literal subgroups
X = O²(C_K(u)) and R = O₂(X), including their images and the center of R.
Quadratic descent then constructs the square form modulo the chosen
fourth-orbit square, and transport supplies its cubic action and fusion marks.

The quotient orbit data, order-two ambient center, and source restriction (i)
remain explicit inputs. All cover-coordinate construction premises are
discharged here; no involution table or square-uniqueness premise is needed.
Quasisimplicity is used upstream to establish the center order and restriction
(i), so the construction itself does not require that additional hypothesis.

Source: Aschbacher–Smith, I.2.2(5), printed pp.411–412 / PDF pp.422–423.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.M12Local.CoverCoordinates
variable {K : Type*} [Group K] [Finite K]

/-- Every lift of the marked central involution is an involution and admits
the marked square coordinates on its actual residual two-core. This discharges
the cover-coordinate input to the M₁₂ square calculation, retaining only the
independently supplied quotient orbit data and source restriction (i). -/
theorem marked_coordinates (e : (K ⧸ center K) ≃* Sporadic.Mathieu.M12)
    (hZ : Nat.card (center K) = 2) (hr : CentralCoverRestriction K)
    (m : Sporadic.Mathieu.M12SmallPair.CoverOrbitData) (u : K)
    (hu : e (QuotientGroup.mk' (center K) u) = Sporadic.Mathieu.M12SmallPair.z) :
    orderOf u = 2 ∧ Nonempty (MarkedSquareCoordinates e u m) := by
  exact (SymplecticCore.coreLiftData e u hZ m hr hu).marked_coordinates m hZ hu

end CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.M12Local.CoverCoordinates
