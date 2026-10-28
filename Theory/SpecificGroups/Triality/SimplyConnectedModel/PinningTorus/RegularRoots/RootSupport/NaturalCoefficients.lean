module

public import Theory.SpecificGroups.Triality.SimplyConnectedModel.PinningTorus.RegularRoots.TorusCoordinates
public import Theory.SpecificGroups.Triality.SimplyConnectedModel.PinningTorus.RegularRoots.RootSupport.NaturalCoefficients.Detection
public import Theory.SpecificGroups.Triality.SimplyConnectedModel.PinningTorus.RegularRoots.RootSupport.NaturalCoefficients.Weights

/-!
# Natural coefficients detect equivariant additive Spin curves

An injective regular additive curve in the characteristic-two Spin carrier
has a nonzero natural matrix coefficient between distinct hyperbolic planes.
The quotient of its column and row torus characters is a concrete coordinate
root. The given conjugation equation therefore supplies a nonzero polynomial
with precisely the corresponding root-character scaling law.

The argument uses the regular forward natural action, polynomial identities
from the quadratic form, and faithfulness on field points. No maximality
hypothesis on the torus is needed. The input `HasCorootCoordinates` fixes the
geometric coordinates and the source numbering.

Source: GLS3 Definitions 1.9.1–3, the conjugation convention in 1.12.1(g), and
the natural representation in 1.14 (`refs/KGroup/GLS3/Chapter1.tex`).
-/

public section
noncomputable section
namespace Triality.SimplyConnected.Pinning
open Theory Theory.AlgebraicGroup
universe u
variable (k : Type u) [Field k] [IsAlgClosed k] [CharP k 2]

local instance (T : ClosedSubgroup (groupVariety k)) : AlgebraicGroup T.carrierVariety :=
  T.carrierAlgebraicGroup

namespace NaturalCoefficients

/-- A nonzero, non-diagonal, non-opposite natural coefficient, together with
its explicit root exponent and its scaling equation. -/
theorem exists_root_coefficient
    (T : ClosedSubgroup (groupVariety k))
    (e : @Iso k _ (dVariety k 4) T.carrierVariety _ T.carrierAlgebraicGroup)
    (he : HasCorootCoordinates k T e)
    (f : AlgebraicGroup.Morphism (KPlus k) (groupVariety k))
    (hf : Function.Injective f.onPoints) (χ : TorusWeight T)
    (hχ : ∀ s a, (T.includePoint s)⁻¹ * f.onPoints (kPlusPoint a) * T.includePoint s =
      f.onPoints (kPlusPoint (χ.pointCharacter s * a))) :
    ∃ (p q : Index) (r : RootIndex),
      pairIndex p ≠ pairIndex q ∧ polynomial k f p q ≠ 0 ∧
      evenOrthogonalRootExponent 4 r = entryExponent q - entryExponent p ∧
      ∀ (s : Variety.Point T.carrierVariety) (a : k),
        (polynomial k f p q).eval (χ.pointCharacter s * a) =
          (coordinateRootWeight k T e r).pointCharacter s * (polynomial k f p q).eval a := by
  obtain ⟨p, q, hpq, hP⟩ := exists_polynomial_ne_zero_distinct_pairs k f hf
  obtain ⟨r, hr⟩ := exists_rootExponent_eq_entry_sub p q hpq
  exact ⟨p, q, r, hpq, hP, hr, polynomial_scaling k T e he f χ hχ p q r hr⟩

end NaturalCoefficients

/-- Every injective equivariant regular additive curve has a nonzero natural
coefficient transforming by a coordinate-root character. -/
theorem exists_coordinateRootWeight_polynomial_of_injective_curve
    (T : ClosedSubgroup (groupVariety k))
    (e : @Iso k _ (dVariety k 4) T.carrierVariety _ T.carrierAlgebraicGroup)
    (he : HasCorootCoordinates k T e)
    (f : AlgebraicGroup.Morphism (KPlus k) (groupVariety k))
    (hf : Function.Injective f.onPoints) (χ : TorusWeight T)
    (hχ : ∀ s a, (T.includePoint s)⁻¹ * f.onPoints (kPlusPoint a) * T.includePoint s =
      f.onPoints (kPlusPoint (χ.pointCharacter s * a))) :
    ∃ (r : RootIndex) (P : Polynomial k), P ≠ 0 ∧
      ∀ (s : Variety.Point T.carrierVariety) (a : k),
        P.eval (χ.pointCharacter s * a) =
          (coordinateRootWeight k T e r).pointCharacter s * P.eval a := by
  obtain ⟨p, q, r, _, hP, _, hscale⟩ :=
    NaturalCoefficients.exists_root_coefficient k T e he f hf χ hχ
  exact ⟨r, NaturalCoefficients.polynomial k f p q, hP, hscale⟩

end Triality.SimplyConnected.Pinning
