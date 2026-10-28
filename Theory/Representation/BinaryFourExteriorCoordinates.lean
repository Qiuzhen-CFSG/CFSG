module
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order20160A8.ExteriorAction
public import Mathlib.LinearAlgebra.ExteriorPower.Basis

/-!
# Coordinates on the binary exterior square

The six minors in the checked ATLAS model are the coordinates of the literal
exterior square of the binary four-space. Pairing with the six dual wedges
constructs the equivalence; naturality on decomposable wedges proves its
compatibility with every matrix, preserving the supplied actor marking.

This connects the middle-root construction used in Aschbacher--Smith B.4.2
and G.9.3 to the exterior-power model used in 13.8.25. The imported ATLAS
construction retains its attribution and license in its owning modules.
-/

@[expose] public noncomputable section
namespace Representation.BinaryFourExteriorCoordinates
open Atlas.Order20160A8.Bivectors
abbrev Four := Fin 4 → ZMod 2
abbrev Exterior := ⋀[ZMod 2]^2 Four

/-- The six coordinates, paired against 01, 02, 03, 12, 13, 23. -/
def coordinates : Exterior →ₗ[ZMod 2] Six (ZMod 2) :=
  LinearMap.pi fun i => exteriorPower.pairingDual (ZMod 2) Four 2
    (exteriorPower.ιMulti (ZMod 2) 2
      ![LinearMap.proj (first i), LinearMap.proj (second i)])

theorem coordinates_wedge (v : Fin 2 → Four) :
    coordinates (exteriorPower.ιMulti (ZMod 2) 2 v) = wedge (v 0) (v 1) := by
  ext i
  fin_cases i <;>
    simp [coordinates, exteriorPower.pairingDual_ιMulti_ιMulti,
      Matrix.det_fin_two, first, second, wedge]

theorem coordinates_surjective : Function.Surjective coordinates := by
  rw [← LinearMap.range_eq_top]
  apply top_unique
  rw [← (Pi.basisFun (ZMod 2) (Fin 6)).span_eq]
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  refine ⟨exteriorPower.ιMulti (ZMod 2) 2
    ![Pi.single (first i) 1, Pi.single (second i) 1], ?_⟩
  simp only [coordinates_wedge, Matrix.cons_val_zero, Matrix.cons_val_one,
    wedge_basis, Pi.basisFun_apply]

/-- The literal exterior power and the compound-matrix model are isomorphic. -/
def equiv : Exterior ≃ₗ[ZMod 2] Six (ZMod 2) :=
  LinearEquiv.ofBijective coordinates ⟨
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by rw [exteriorPower.finrank_eq]; simp [Four, Six]; decide)).mpr coordinates_surjective,
    coordinates_surjective⟩

/-- The comparison intertwines the actual action of every four-by-four matrix. -/
theorem equiv_map (A : Matrix (Fin 4) (Fin 4) (ZMod 2)) (v : Exterior) :
    equiv (exteriorPower.map 2 A.toLin' v) = exteriorMap A (equiv v) := by
  suffices coordinates.comp (exteriorPower.map 2 A.toLin') =
      (exteriorMap A).comp coordinates from LinearMap.congr_fun this v
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro w
  simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply, exteriorPower.map_apply_ιMulti,
    coordinates_wedge, exteriorMap_wedge, Function.comp_apply, Matrix.toLin'_apply]
end Representation.BinaryFourExteriorCoordinates
