module

public import Mathlib.RingTheory.RootsOfUnity.Basic
public import Theory.AlgebraicGroup.Borel.AdjointCenter
public import Theory.AlgebraicGroup.RootSystems.SpinOddCenter
public import Theory.AlgebraicGroup.RootSystems.AlgebraicGroups.theorem_1_10_4_c

/-!
# Type-B center transport

This module records the two center transports needed by the type-`B` table.
The point-group equivalence in `OddOrthogonalModel` identifies the center of a
geometric Spin carrier with the center of the Clifford `spinGroup`; the first
theorem transports any concrete `rootsOfUnity 2` calculation across that
equivalence.  The second theorem transports the same calculation through a
surjective isogeny: the image of the source center is the target center by the
proved connected-isogeny center theorem.

The remaining model-specific input is deliberately explicit: a proof of the
Clifford statement
`center (spinGroup q) ≃* rootsOfUnity 2 k` and connectedness of the source
carrier must come from the odd-orthogonal construction.  This keeps the
transport layer independent of unresolved root-model or classification
declarations.  The source is GLS3, Chapter 1, Theorem 1.12.5(c)-(d), with the
type-`B` row of Table 1.12.5.

Because the model's Clifford action is supplied by
`spinGroup.conjAct_smul_ι_mem_range_ι`, all model arguments and center
transports below explicitly require `[Invertible (2 : k)]`; characteristic two
is outside this Spin/SO interface.
-/

universe u

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k] [Invertible (2 : k)]

set_option linter.style.haveILetI false

/-- Transport the Clifford Spin center calculation to the rational points of
an `OddOrthogonalModel` carrier. -/
public noncomputable def oddOrthogonalModel_center_iso_rootsOfUnity_two
    {V : Type u} [AddCommGroup V] [Module k V]
    {q : QuadraticForm k V} (model : OddOrthogonalModel q)
    (hCenter : Subgroup.center (spinGroup q) ≃* rootsOfUnity 2 k) :
    letI := model.spin.carrierAlgebraicGroup
    Subgroup.center (Variety.Point model.spin.carrierVariety) ≃*
      rootsOfUnity 2 k :=
  (Subgroup.centerCongr model.spinPoints).trans hCenter

private noncomputable def centerMapOfSurjectiveMorphism
    {V : Type u} [AddCommGroup V] [Module k V]
    {q : QuadraticForm k V} (model : OddOrthogonalModel q)
    {K : Variety k} [AlgebraicGroup K]
    (φ : AlgebraicGroup.Morphism model.spin.carrierVariety K)
    (hφ : Function.Surjective φ.onPoints) :
    letI := model.spin.carrierAlgebraicGroup
    Subgroup.center (Variety.Point model.spin.carrierVariety) →*
      Subgroup.center (Variety.Point K) := by
  letI := model.spin.carrierAlgebraicGroup
  let e : Subgroup.center (Variety.Point model.spin.carrierVariety) →*
      Subgroup.center (Variety.Point K) :=
    { toFun := fun z => ⟨φ.onPoints z, by
          apply Subgroup.mem_center_iff.mpr
          intro y
          obtain ⟨x, rfl⟩ := hφ y
          rw [← φ.onPoints.map_mul, ← φ.onPoints.map_mul,
            Subgroup.mem_center_iff.mp z.property x]
        ⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := by
        intro x y
        apply Subtype.ext
        simp }
  exact e

/-- Every connected odd-orthogonal Spin center calculation maps onto the center
of a target reached by a surjective isogeny.  In particular, this is the
homomorphic-image half of the type-`B` row for any target version once the
standard Spin model is connected and its center calculation is supplied. -/
public theorem typeB_center_surjective_of_isogeny
    {V : Type u} [AddCommGroup V] [Module k V]
    {q : QuadraticForm k V} (model : OddOrthogonalModel q)
    {K : Variety k} [AlgebraicGroup K]
    (φ : AlgebraicGroup.Morphism model.spin.carrierVariety K)
    (hφ : IsIsogeny φ)
    (hSpinConnected : _root_.IsConnected
      (Set.univ : Set (Variety.Point model.spin.carrierVariety)))
    (hCenter : Subgroup.center (spinGroup q) ≃* rootsOfUnity 2 k) :
    ∃ f : rootsOfUnity 2 k →* Subgroup.center (Variety.Point K),
      Function.Surjective f := by
  letI := model.spin.carrierAlgebraicGroup
  let e : rootsOfUnity 2 k ≃*
      Subgroup.center (Variety.Point model.spin.carrierVariety) :=
    (oddOrthogonalModel_center_iso_rootsOfUnity_two model hCenter).symm
  let f : rootsOfUnity 2 k →* Subgroup.center (Variety.Point K) :=
    (centerMapOfSurjectiveMorphism model φ hφ.1).comp e.toMonoidHom
  refine ⟨f, ?_⟩
  intro z
  have hz : (z : Variety.Point K) ∈
      (Subgroup.center (Variety.Point K) : Set (Variety.Point K)) := z.property
  rw [← isogeny_image_center_eq_center_of_connected φ hφ hSpinConnected] at hz
  obtain ⟨x, hx, hzx⟩ := hz
  refine ⟨e.symm ⟨x, hx⟩, ?_⟩
  apply Subtype.ext
  change φ.onPoints (e (e.symm ⟨x, hx⟩)) = z
  rw [e.apply_symm_apply]
  exact hzx

end Theory.AlgebraicGroup
