module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.WeakClosure.CoordinateModel
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OrthogonalLocal.Geometry.Planes

/-!
# The two vector orbits in the compatible wreath coordinates

Independent order-three rotations of the two definite planes, together with
their interchange, transport any two nonidentity vectors of the same quadratic
value. A fixed vector of an actor interchanging the planes is singular. The
finite certificates involve only eighteen explicit actors and sixteen vectors;
they use the literal matrix action and are checked by the kernel.

Surjectivity and equivariance lift these transporters to conjugators in `M`.
Every Sylow two-subgroup has an element interchanging the planes, so its fixed
vectors are singular. The comparison with the given quadratic form remains
the explicit `OrthogonalCoordinateModel` premise of these transport results.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), printed
pp.1121–1122 and the two orbits preceding 15.3.46 on pp.1140–1141.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter15.Section03.FusionCore
open Subgroup
attribute [local instance] orthogonalAction

private instance : Fintype OrthogonalActor :=
  Fintype.ofEquiv ((OrthogonalPlaneIndex → OrthogonalPlaneActor) × OrthogonalPlaneIndex)
    (RegularWreathProduct.equivProd _ _).symm

private def orbitRotation : OrthogonalPlaneActor := ⟨!![0, 1; 1, 1], by decide⟩
private abbrev OrbitCode := Fin 3 × Fin 3 × OrthogonalPlaneIndex
private def orbitActor (k : OrbitCode) : OrthogonalActor :=
  ⟨fun i => if i = 1 then orbitRotation ^ k.1.val else orbitRotation ^ k.2.1.val, k.2.2⟩

set_option synthInstance.maxSize 4096 in
set_option maxRecDepth 10000 in
private theorem orbit_certificate : ∀ v w : OrthogonalVector, v ≠ 1 → w ≠ 1 →
    orthogonalCoordinateValue v = orthogonalCoordinateValue w →
    ∃ k : OrbitCode, orbitActor k • v = w := by decide +kernel

/-- The literal wreath action is transitive on each nonzero quadratic fiber. -/
theorem coordinate_orbit (v w : OrthogonalVector) (hv : v ≠ 1) (hw : w ≠ 1)
    (hq : orthogonalCoordinateValue v = orthogonalCoordinateValue w) :
    ∃ g : OrthogonalActor, g • v = w := by
  obtain ⟨k, hk⟩ := orbit_certificate v w hv hw hq
  exact ⟨orbitActor k, hk⟩

set_option maxRecDepth 10000 in
private theorem swap_fixed_certificate : ∀ g : OrthogonalActor, ∀ v : OrthogonalVector,
    g.right ≠ 1 → g • v = v → orthogonalCoordinateValue v = 0 := by decide +kernel

/-- A vector fixed by an actor interchanging the definite planes is singular. -/
theorem coordinate_singular_of_swap_fixed (g : OrthogonalActor) (v : OrthogonalVector)
    (hg : g.right ≠ 1) (hv : g • v = v) : orthogonalCoordinateValue v = 0 :=
  swap_fixed_certificate g v hg hv

open scoped IsMulCommutative
variable {G : Type*} [Group G] {M V P : Subgroup G} [IsElementaryAbelian 2 V]
  {d : NaturalOrthogonalAction M V}

/-- The coordinate transporters are actual conjugators in the given local group. -/
theorem OrthogonalCoordinateModel.conjugateBy_of_value_eq
    (k : OrthogonalCoordinateModel d P) (v w : V) (hv : v ≠ 1) (hw : w ≠ 1)
    (hq : d.form (Additive.ofMul v) = d.form (Additive.ofMul w)) :
    ConjugateBy M (v : G) (w : G) := by
  have hne (x : V) (hx : x ≠ 1) : k.action.coordinates x ≠ 1 := by
    intro he
    exact hx (k.action.coordinates.injective (he.trans (map_one _).symm))
  rw [k.form_eq, k.form_eq] at hq
  obtain ⟨g, hg⟩ := coordinate_orbit _ _ (hne v hv) (hne w hw) hq
  obtain ⟨m, hm⟩ := k.action.onto g
  refine ⟨m, m.property, ?_⟩
  have he := k.action.compatible m v
  rw [hm, hg] at he
  exact congrArg Subtype.val (k.action.coordinates.injective he)

/-- Fixed vectors of the actual Sylow subgroup are singular for the given form. -/
theorem OrthogonalCoordinateModel.singular_of_fixedPlane_sylow [Finite G]
    (k : OrthogonalCoordinateModel d P) (T : Sylow 2 G) (hTM : (T : Subgroup G) ≤ M)
    (v : V) (hv : (v : G) ∈ fixedPlane V T) : d.form (Additive.ofMul v) = 0 := by
  have hright := OrthogonalGeometry.sylow_right_image (k.action.sylowImage T hTM)
  have hmem : Multiplicative.ofAdd (1 : ZMod 2) ∈
      (k.action.image T).map
        (RegularWreathProduct.rightHom : OrthogonalActor →* OrthogonalPlaneIndex) := by
    rw [← k.action.coe_sylowImage T hTM, hright]
    exact mem_top _
  obtain ⟨g, hg, hgr⟩ := hmem
  have hfixed := hv
  rw [k.action.fixedPlane_eq_map hTM] at hfixed
  obtain ⟨w, hw, hwv⟩ := hfixed
  have hcoord : k.action.coordinates v = w := by
    apply k.action.coordinates.symm.injective
    rw [k.action.coordinates.symm_apply_apply]
    exact Subtype.ext hwv.symm
  rw [k.form_eq, hcoord]
  apply coordinate_singular_of_swap_fixed g w ?_ (hw g hg)
  change g.right = Multiplicative.ofAdd (1 : ZMod 2) at hgr
  rw [hgr]
  decide

end CFSG.Quasithin.Chapter15.Section03.FusionCore
