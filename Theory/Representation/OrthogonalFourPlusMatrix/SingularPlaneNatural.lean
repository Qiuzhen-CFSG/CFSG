module
public import Theory.Representation.OrthogonalFourPlusMatrix.SingularPlaneOrbit

/-!
# Natural coordinates on the tensor singular plane

The first factor acts naturally on matrices with zero first column.
Transporting the plane by (a,b) is the same as transporting it by (1,b),
since a already preserves the plane. Right multiplication commutes with
the original first factor, so these coordinates preserve its literal action.

Source: Aschbacher–Smith9.1.2 and9.2.2(3), combined manuscript,
printed pp.729–731. The application retains the original component marking.
-/

@[expose] public noncomputable section
open Matrix Representation Representation.BinaryOffender
namespace ClassicalOrthogonal.FourPlusMatrix.Binary

private theorem planeMap_injective : Function.Injective planeMap := by
  intro v w h
  funext i
  have hi := congrArg (fun M : V => M i 1) h
  fin_cases i <;> simpa [planeMap] using hi

private theorem action_mul_apply (a b : G) (v : V) :
    action (a*b) v = action a (action b v) :=
  congrArg (fun f : Module.End (ZMod 2) V => f v) (action.map_mul a b)

theorem plane_first_factor_invariant (g : SpecialLinearGroup (Fin 2) F) :
    plane.map (action (g,1)) = plane := by
  apply le_antisymm
  · rintro _ ⟨_,⟨v,rfl⟩,rfl⟩
    rw [←planeMap_action]
    exact ⟨_,rfl⟩
  · rintro _ ⟨v,rfl⟩
    refine ⟨planeMap (SL2FourNatural.action g⁻¹ v),⟨_,rfl⟩,?_⟩
    rw [←planeMap_action]
    change planeMap (SL2FourNatural.action g (SL2FourNatural.action g⁻¹ v)) = planeMap v
    rw [←LinearEquiv.mul_apply,←map_mul,mul_inv_cancel,map_one]
    rfl

theorem plane_map_eq_right (g : G) :
    plane.map (action g) = plane.map (action (1,g.2)) := by
  have he : action g = (action (1,g.2)).comp (action (g.1,1)) := by
    apply LinearMap.ext
    intro v
    change action g v = action (1,g.2) (action (g.1,1) v)
    rw [←action_mul_apply]
    have hp : g = (1,g.2)*(g.1,1) := by
      apply Prod.ext <;> simp
    rw [←hp]
  rw [he,Submodule.map_comp,plane_first_factor_invariant]

def planeNaturalMap (g : G) : SL2FourNatural.V →ₗ[ZMod 2] V :=
  (action (1,g.2)).comp planeMap

theorem planeNaturalMap_range (g : G) :
    (planeNaturalMap g).range = plane.map (action g) := by
  rw [plane_map_eq_right]
  exact LinearMap.range_comp _ _

private theorem planeNaturalMap_injective (g : G) : Function.Injective (planeNaturalMap g) :=
  (linearAction (1,g.2)).injective.comp planeMap_injective

theorem planeNaturalMap_equivariant (g : G) (a : SL2FourNatural.SL) (v : SL2FourNatural.V) :
    planeNaturalMap g (SL2FourNatural.action a v) = action (a,1) (planeNaturalMap g v) := by
  change action (1,g.2) (planeMap (a.val *ᵥ v)) =
    action (a,1) (action (1,g.2) (planeMap v))
  rw [planeMap_action,←action_mul_apply,←action_mul_apply]
  have he : (1,g.2)*(a,1) = (a,1)*(1,g.2) := by
    apply Prod.ext <;> simp
  rw [he]

theorem sylow_plane_natural_coordinates (P : Sylow 2 G) :
    ∃ c : SL2FourNatural.V ≃ₗ[ZMod 2] firstOrbit (fixedSpace action (P : Subgroup G)),
      ∀ (a : SL2FourNatural.SL) (v : SL2FourNatural.V),
        (c (SL2FourNatural.action a v) : V) = action (a,1) (c v : V) := by
  obtain ⟨g,hg⟩ := sylow_fixedSpace_conjugate_point P
  have hr : (planeNaturalMap g).range = firstOrbit (fixedSpace action (P : Subgroup G)) := by
    rw [hg,firstOrbit_map,firstOrbit_point_eq_plane,planeNaturalMap_range]
  let c := (LinearEquiv.ofInjective (planeNaturalMap g) (planeNaturalMap_injective g)).trans
    (LinearEquiv.ofEq _ _ hr)
  refine ⟨c,?_⟩
  intro a v
  exact planeNaturalMap_equivariant g a v

end ClassicalOrthogonal.FourPlusMatrix.Binary
