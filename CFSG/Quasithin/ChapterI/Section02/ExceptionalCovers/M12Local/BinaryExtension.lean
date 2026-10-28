module

public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.M12Local.Definitions
public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.M12Local.SquareCalculation
public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.M12Local.BinaryExtension.Recognition
public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.M12Local.BinaryExtension.CentralizerQuotient
public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.M12Local.BinaryExtension.Realization
public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.M12Local.BinaryExtension.Splitting

/-!
# Binary constituents of the marked M₁₂ cover

The source's actual quotient R/⟨v₄⟩ is elementary abelian of order 32, or is
a central product of two actual embedded quaternion groups. The supplied
fusion marks remove the E₄ × Q₈ possibility. In the elementary branch the
actual cubic norm splits this quotient over the image of Z(K), and the
extra central-class involution lifts to an involution in C_K(u).

The actual full-centralizer quotient maps onto S₃ with this core quotient as
kernel. The cubic norm has a normal kernel, and the extra involution splits
the remaining central extension of S₃. Pulling back constructs a retraction
of C_K(u) onto Z(K) in the elementary branch. The marked coordinates and
model orbit data remain explicit inputs; no quotient realization or splitting
premise remains. Source restriction (i) excludes this branch in the parent.

Source: Aschbacher–Smith, I.2.2(5), printed p.412 / PDF p.423.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.M12Local
namespace MarkedSquareCoordinates
variable {K : Type*} [Group K] [Finite K] {u : K}
variable {e : (K ⧸ center K) ≃* Sporadic.Mathieu.M12}
variable {m : Sporadic.Mathieu.M12SmallPair.CoverOrbitData}
variable (d : MarkedSquareCoordinates e u m)

/-- The two actual group structures allowed by the marked cover coordinates. -/
theorem binary_models (hZ : Nat.card (center K) = 2) :
    Nonempty (d.toSquareCoordinates.BinaryQuotient ≃* Multiplicative (Fin 5 → ZMod 2)) ∨
      Nonempty (QuaternionCentralProductData d.toSquareCoordinates.BinaryQuotient) :=
  d.toSquareCoordinates.quotient_models d.noncentral hZ

/-- The elementary branch has a concrete model and a complement selected by
conjugation by the actual cubic lift. -/
theorem elementary_core_split (hZ : Nat.card (center K) = 2) (hq : d.quadratic = 0) :
    Nonempty (d.toSquareCoordinates.BinaryQuotient ≃* Multiplicative (Fin 5 → ZMod 2)) ∧
      IsCompl (d.quotientRetraction hq).ker d.toSquareCoordinates.quotientCenter :=
  ⟨d.toSquareCoordinates.quotient_equiv_elementary d.noncentral hZ hq,
    d.quotientRetraction_complement hq⟩

/-- The elementary branch splits off the actual ambient center from C_K(u).
The S₃ quotient, its cubic action, and its extra involution are constructed
from the marked coordinates and fusion data. This supplies `hsplit` in
`SquareCoordinates.noncentral_axis_order_four`. -/
theorem elementary_centralizer_retraction (hZ : Nat.card (center K) = 2)
    (hu : orderOf u = 2) (hq : d.quadratic = 0) :
    Nonempty (CentralizerRetraction u) := by
  obtain ⟨s⟩ := d.nonempty_centralizerQuotientData hZ hu
  exact d.centralizerRetraction_of_quadratic_eq_zero hZ s hq

end MarkedSquareCoordinates
end CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.M12Local
