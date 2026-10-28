module

public import Theory.SpecificGroups.Triality.SimplyConnectedModel.PinningTorus.RegularRoots.TorusCoordinates
public import Theory.SpecificGroups.Triality.SimplyConnectedModel.PinningTorus.RegularRoots.RootSupport.CharacterPowers
public import Theory.SpecificGroups.Triality.SimplyConnectedModel.PinningTorus.RegularRoots.RootSupport.NaturalCoefficients

/-!
# Exhaustive character support of Spin torus roots

A parametrization of an actual root subgroup gives an injective regular
additive curve in Spin with the defining torus conjugation equation. A nonzero
polynomial coefficient of this curve that scales by a coordinate-root
character identifies its parameter character: comparison of coefficients
gives a power relation, and the primitive simple-coroot exponent forces that
power to be one.

In characteristic two, `NaturalCoefficients` proves the required detection
from the regular natural action and its faithfulness on field points. Applying
it to a parametrized root subgroup proves that every actual torus root is a
coordinate-root character. The only geometric inputs are the maximal torus,
its algebraic isomorphism with the split torus, and the simple-coroot point
formula. The argument is independent of forward root-curve construction and
uses neither tangent injectivity nor a regular inverse to the Spin cover.

Source: GLS3 Definitions 1.9.1–3 and §§1.12–1.14
(`refs/KGroup/GLS3/Chapter1.tex`).
-/

public section
noncomputable section
namespace Triality.SimplyConnected.Pinning
open Theory Theory.AlgebraicGroup
universe u
variable (k : Type u) [Field k] [IsAlgClosed k]

local instance rootSupportAlgebraicGroup
    (T : ClosedSubgroup (groupVariety k)) : AlgebraicGroup T.carrierVariety :=
  T.carrierAlgebraicGroup

/-- Reduction of actual root support to polynomial detection of injective
regular additive curves. The curve-detection premise is an extra obligation,
not a consequence of point injectivity of the Spin cover. -/
theorem torusRootSet_subset_coordinateRootWeight_of_curve_detection
    (T : ClosedSubgroup (groupVariety k))
    (e : @Iso k _ (dVariety k 4) T.carrierVariety _ T.carrierAlgebraicGroup)
    (hdetect : ∀ (f : AlgebraicGroup.Morphism (KPlus k) (groupVariety k)),
      Function.Injective f.onPoints → ∀ χ : TorusWeight T,
      (∀ (s : Variety.Point T.carrierVariety) (a : k),
        (T.includePoint s)⁻¹ * f.onPoints (kPlusPoint a) * T.includePoint s =
          f.onPoints (kPlusPoint (χ.pointCharacter s * a))) →
      ∃ (r : RootIndex) (P : Polynomial k), P ≠ 0 ∧
        ∀ (s : Variety.Point T.carrierVariety) (a : k),
          P.eval (χ.pointCharacter s * a) =
            (coordinateRootWeight k T e r).pointCharacter s * P.eval a) :
    TorusRootSet T ⊆ Set.range (coordinateRootWeight k T e) := by
  rintro χ ⟨X, hX, hχ⟩
  let := X.carrierAlgebraicGroup
  let x : OneParameterParametrization X.carrierVariety := Classical.choice hX.2
  let f := X.inclusion.comp x.hom
  have hf : Function.Injective f.onPoints :=
    X.inclusion_injective.comp x.toMulEquiv.injective
  obtain ⟨r, P, hP, hscale⟩ := hdetect f hf χ (fun s a => hχ x a s)
  exact ⟨r, (eq_coordinateRootWeight_of_polynomial k T e χ r P hP hscale).symm⟩

variable [CharP k 2]

/-- Every actual root of a maximal Spin torus with the geometric source
coroot coordinates is one of the coordinate-root characters. -/
theorem torusRootSet_subset_coordinateRootWeight
    (T : ClosedSubgroup (groupVariety k)) (_hT : IsMaximalTorus T)
    (e : @Iso k _ (dVariety k 4) T.carrierVariety _ T.carrierAlgebraicGroup)
    (he : HasCorootCoordinates k T e) :
    TorusRootSet T ⊆ Set.range (coordinateRootWeight k T e) :=
  torusRootSet_subset_coordinateRootWeight_of_curve_detection k T e
    (exists_coordinateRootWeight_polynomial_of_injective_curve k T e he)

/-- The character of any actual torus root has an explicit coordinate-root
index, with no root-realization or tangent-support premise. -/
theorem exists_coordinateRootWeight_of_mem_torusRootSet
    (T : ClosedSubgroup (groupVariety k)) (hT : IsMaximalTorus T)
    (e : @Iso k _ (dVariety k 4) T.carrierVariety _ T.carrierAlgebraicGroup)
    (he : HasCorootCoordinates k T e) (χ : TorusWeight T)
    (hχ : χ ∈ TorusRootSet T) :
    ∃ r : RootIndex, χ = coordinateRootWeight k T e r := by
  obtain ⟨r, hr⟩ := torusRootSet_subset_coordinateRootWeight k T hT e he hχ
  exact ⟨r, hr.symm⟩

end Triality.SimplyConnected.Pinning
