module

public import Theory.SpecificGroups.Triality.PositiveRootCoordinates.Scalars
public import Theory.SpecificGroups.Triality.RootGeometryBasic
public import Theory.AlgebraicGroup.RootSystems.IntegralRootCurveSimpleGeneration

/-!
# The twelve integral Geck curves in the split triality group

Each coordinate uses the existing integral root operator, specialized to the
actual cubic coefficient field. All-root generation places these units in the
simple Geck group. The four simple curves agree with the pinned generators of
`Parabolics.positiveSubgroup`. The ordered product is defined here without
assuming either uniqueness or that its range is a subgroup.

Source: GLS3, 2.3.6–7 and §§2.4–2.6 (`refs/KGroup/GLS3/chapter2.tex`).
-/

@[expose] public section
noncomputable section
open Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction
namespace Triality.Standard.PositiveCoordinates

/-- The canonical integral root curve, as an element of the actual split group. -/
def curve (P : Parameters) (i : Fin 12) (t : ExtensionField P) : SplitGroup P :=
  ⟨rootCurveUnit (integralChevalleyRootOperators (b := typeDRootPairing_base 2))
    (rootIndex i) t, rootCurveUnit_mem_simpleSubgroup _ _⟩

/-- The underlying matrix unit is the integral divided-power curve specialized to the field. -/
theorem curve_unit (P : Parameters) (i : Fin 12) (t : ExtensionField P) :
    (curve P i t).val =
      rootCurveUnit (integralChevalleyRootOperators (b := typeDRootPairing_base 2))
        (rootIndex i) t := rfl

@[simp] theorem curve_zero (P : Parameters) (i : Fin 12) : curve P i 0 = 1 :=
  Subtype.ext (rootCurveUnit_zero _ _)

theorem curve_add (P : Parameters) (i : Fin 12) (s t : ExtensionField P) :
    curve P i (s + t) = curve P i s * curve P i t :=
  Subtype.ext (rootCurveUnit_add _ _ _ _)

theorem curve_inv (P : Parameters) (i : Fin 12) (t : ExtensionField P) :
    (curve P i t)⁻¹ = curve P i (-t) :=
  Subtype.ext (rootCurveUnit_inv _ _ _)

/-- The four simple coordinates are the existing positive simple generators. -/
@[simp] theorem curve_simple (P : Parameters) (i : Fin 4) (t : ExtensionField P) :
    curve P (simplePosition i) t = Parabolics.positiveRoot P i t := by
  apply Subtype.ext
  dsimp only [curve, Parabolics.positiveRoot, RootPairing.SimpleGeckGroup.positive]
  rw [rootIndex_simple, ← typeDRootPairing_baseEquiv_val]
  exact rootCurveUnit_simple _ _

/-- Product in the orbit-compatible order fixed in `Roots`. -/
def orderedProduct (P : Parameters) (a : Coordinates P) : SplitGroup P :=
  (List.ofFn fun i : Fin 12 => curve P i (a i)).prod

@[simp] theorem orderedProduct_zero (P : Parameters) :
    orderedProduct P (fun _ => 0) = 1 := by
  simp [orderedProduct]

end Triality.Standard.PositiveCoordinates
