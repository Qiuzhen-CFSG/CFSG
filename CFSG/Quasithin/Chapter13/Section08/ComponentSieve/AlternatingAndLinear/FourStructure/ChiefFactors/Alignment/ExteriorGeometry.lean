module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors.Alignment.Models
public import Theory.SpecificGroups.BinaryLinear.FourParabolicAction.Geometry
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order20160A8.ExteriorAction
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors.Alignment.ExteriorGeometry.Finite


/-!
# No invariant plane in the exterior square of a marked binary four-space

We identify the genuine exterior square with the six minor coordinates
01, 02, 03, 12, 13, 23 using exterior duality. Surjectivity follows because
every coordinate basis vector is decomposable; equality of dimensions makes
this identification a linear equivalence. The bivectors and their basis lemma
come from the attributed ATLAS port imported above.

For the standard plane, eight actual transvections in its stabilizer act by
the maps of `ExteriorGeometry.Finite`. A binary plane consists of precisely
{0, x, y, x+y} for a basis x, y, and the kernel-checked finite calculation
excludes such a stable set. Finally, an ambient linear equivalence transports
an arbitrary plane to the standard plane, and exterior functoriality transports
its invariant subspaces. No source subgroup identification or head conclusion
is assumed.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), 13.8.25, printed p.960 (PDF p.977), the exclusion
of the six-dimensional maximal quotient using the stabilized projective line.
-/

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors.Alignment.ExteriorGeometry

open Atlas.Order20160A8.Bivectors

private noncomputable def coordinates : ExteriorSquare →ₗ[ZMod 2] Six :=
  LinearMap.pi fun i => exteriorPower.pairingDual (ZMod 2) NaturalSpace 2
    (exteriorPower.ιMulti (ZMod 2) 2
      ![LinearMap.proj (first i), LinearMap.proj (second i)])

private theorem coordinates_wedge (v : Fin 2 → NaturalSpace) :
    coordinates (exteriorPower.ιMulti (ZMod 2) 2 v) = wedge (v 0) (v 1) := by
  ext i
  fin_cases i <;>
    simp [coordinates, exteriorPower.pairingDual_ιMulti_ιMulti,
      Matrix.det_fin_two, first, second, wedge]

private theorem coordinates_surjective : Function.Surjective coordinates := by
  rw [← LinearMap.range_eq_top]
  apply top_unique
  rw [← (Pi.basisFun (ZMod 2) (Fin 6)).span_eq]
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  refine ⟨exteriorPower.ιMulti (ZMod 2) 2
    ![Pi.single (first i) 1, Pi.single (second i) 1], ?_⟩
  simp only [coordinates_wedge, Matrix.cons_val_zero, Matrix.cons_val_one,
    wedge_basis, Pi.basisFun_apply]

private noncomputable def coordinatesEquiv : ExteriorSquare ≃ₗ[ZMod 2] Six :=
  LinearEquiv.ofBijective coordinates ⟨
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by simpa using exteriorSquare_finrank)).mpr coordinates_surjective,
    coordinates_surjective⟩

private def dest : Fin 8 → Fin 4 := ![0, 1, 2, 3, 0, 0, 1, 1]
private def src : Fin 8 → Fin 4 := ![1, 0, 3, 2, 2, 3, 2, 3]

private def gen (i : Fin 8) : BinaryLinear.GL NaturalSpace :=
  BinaryLinear.transvection (Pi.single (dest i) 1) (LinearMap.proj (src i))
    (by fin_cases i <;> simp [dest, src])

private theorem gen_apply (i : Fin 8) (v : NaturalSpace) :
    gen i v = v + v (src i) • Pi.single (dest i) 1 := rfl

private def standardPlane : Submodule (ZMod 2) NaturalSpace where
  carrier := {v | v 2 = 0 ∧ v 3 = 0}
  zero_mem' := by simp
  add_mem' := by rintro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩; simp_all
  smul_mem' := by rintro a x ⟨hx, hx'⟩; simp_all

private theorem gen_mem (i : Fin 8) : gen i ∈ BinaryLinear.parabolic standardPlane := by
  intro v
  change ((gen i v) 2 = 0 ∧ (gen i v) 3 = 0) ↔ (v 2 = 0 ∧ v 3 = 0)
  fin_cases i <;> simp [gen, dest, src, BinaryLinear.transvection]
  all_goals intro h; simp [h]

set_option maxHeartbeats 2000000 in
private def stepMap (i : Fin 8) : Six →ₗ[ZMod 2] Six where
  toFun := step i
  map_add' x y := by
    fin_cases i <;> dsimp [step] <;> ext j <;> fin_cases j <;>
      simp [add_assoc, add_comm, add_left_comm]
  map_smul' a x := by
    fin_cases i <;> dsimp [step] <;> ext j <;> fin_cases j <;> simp [mul_add]

set_option maxHeartbeats 4000000 in
private theorem coordinates_gen (i : Fin 8) (v : ExteriorSquare) :
    coordinates (exteriorPower.map 2 (gen i).toLinearMap v) = step i (coordinates v) := by
  suffices coordinates.comp (exteriorPower.map 2 (gen i).toLinearMap) =
      (stepMap i).comp coordinates from LinearMap.congr_fun this v
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro v
  simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
    exteriorPower.map_apply_ιMulti, coordinates_wedge]
  change wedge (gen i (v 0)) (gen i (v 1)) = step i (wedge (v 0) (v 1))
  simp only [gen_apply]
  fin_cases i <;> dsimp [dest, src, wedge, step] <;>
    ext j <;> fin_cases j <;>
    simp [CharTwo.sub_eq_add] <;> ring_nf <;>
    simp [show (2 : ZMod 2) = 0 by decide]

private noncomputable def planeEquiv : (Fin 2 → ZMod 2) ≃ₗ[ZMod 2] standardPlane where
  toFun v := ⟨![v 0, v 1, 0, 0], rfl, rfl⟩
  invFun v := ![v.val 0, v.val 1]
  map_add' v w := by ext i; fin_cases i <;> rfl
  map_smul' a v := by ext i; fin_cases i <;> rfl
  left_inv v := by ext i; fin_cases i <;> rfl
  right_inv v := by
    ext i
    fin_cases i <;> simp [v.property.1, v.property.2]

private theorem standardPlane_finrank : Module.finrank (ZMod 2) standardPlane = 2 := by
  rw [← planeEquiv.finrank_eq]
  simp

private theorem plane_vectors (S : Submodule (ZMod 2) Six)
    (b : Module.Basis (Fin 2) (ZMod 2) S) (v : S) :
    v = 0 ∨ v = b 0 ∨ v = b 1 ∨ v = b 0 + b 1 := by
  have hv := b.sum_repr v
  rw [Fin.sum_univ_two] at hv
  have scalars : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  rcases scalars (b.repr v 0) with h0 | h0 <;>
    rcases scalars (b.repr v 1) with h1 | h1 <;>
    simp_all

private theorem no_coordinate_plane
    (S : Submodule (ZMod 2) Six) (hS : Module.finrank (ZMod 2) S = 2)
    (hstable : ∀ i v, v ∈ S → step i v ∈ S) : False := by
  let b := Module.finBasisOfFinrankEq (ZMod 2) S hS
  have h0 : (b 0 : Six) ≠ 0 := by
    intro h
    exact b.ne_zero 0 (Subtype.ext h)
  have h1 : (b 1 : Six) ≠ 0 := by
    intro h
    exact b.ne_zero 1 (Subtype.ext h)
  have h01 : (b 0 : Six) ≠ b 1 := by
    intro h
    have := b.injective (Subtype.ext h)
    exact (by decide : (0 : Fin 2) ≠ 1) this
  apply finite_check (b 0) (b 1) h0 h1 h01
  intro i
  constructor
  · exact (plane_vectors S b ⟨_, hstable i _ (b 0).property⟩).imp
      (congrArg Subtype.val) (fun h => h.imp (congrArg Subtype.val)
        (fun h => h.imp (congrArg Subtype.val) (congrArg Subtype.val)))
  · exact (plane_vectors S b ⟨_, hstable i _ (b 1).property⟩).imp
      (congrArg Subtype.val) (fun h => h.imp (congrArg Subtype.val)
        (fun h => h.imp (congrArg Subtype.val) (congrArg Subtype.val)))

private theorem no_standard_plane (S : Submodule (ZMod 2) ExteriorSquare)
    (hS : Module.finrank (ZMod 2) S = 2)
    (hstable : ∀ g ∈ BinaryLinear.parabolic standardPlane, ∀ v ∈ S,
      exteriorPower.map 2 g.toLinearMap v ∈ S) : False := by
  apply no_coordinate_plane
    (S.map coordinatesEquiv.toLinearMap)
    ((coordinatesEquiv.finrank_map_eq S).trans hS)
  intro i v hv
  obtain ⟨w, hw, rfl⟩ := hv
  exact ⟨exteriorPower.map 2 (gen i).toLinearMap w,
    hstable (gen i) (gen_mem i) w hw, coordinates_gen i w⟩

private noncomputable def exteriorEquiv (g : BinaryLinear.GL NaturalSpace) :
    ExteriorSquare ≃ₗ[ZMod 2] ExteriorSquare :=
  LinearEquiv.ofBijective (exteriorPower.map 2 g.toLinearMap)
    ⟨exteriorPower.map_injective_field g.injective,
      exteriorPower.map_surjective g.surjective⟩

/-- A plane stabilizer on the natural binary four-space has no invariant
plane on its genuine exterior square. With `P` and `hP` supplied, this is exactly
the `hgeometry` premise of `not_exteriorSquare_head_of_plane_obstruction`. -/
public theorem no_invariant_plane (P : Submodule (ZMod 2) NaturalSpace)
    (hP : Module.finrank (ZMod 2) P = 2)
    (S : Submodule (ZMod 2) ExteriorSquare)
    (hS : Module.finrank (ZMod 2) S = 2)
    (hstable : ∀ g ∈ BinaryLinear.parabolic P, ∀ v ∈ S,
      exteriorPower.map 2 g.toLinearMap v ∈ S) : False := by
  obtain ⟨e, he⟩ := BinaryLinear.FourParabolicAction.exists_linearEquiv_map_eq
    standardPlane P (standardPlane_finrank.trans hP.symm)
  apply no_standard_plane (S.map (exteriorEquiv e.symm).toLinearMap)
    (((exteriorEquiv e.symm).finrank_map_eq S).trans hS)
  intro g hg v hv
  obtain ⟨w, hw, rfl⟩ := hv
  have hc : e * g * e⁻¹ ∈ BinaryLinear.parabolic P := by
    intro x
    rw [← he]
    simp only [Submodule.mem_map_equiv, LinearEquiv.mul_apply,
      LinearEquiv.symm_apply_apply, LinearEquiv.coe_inv]
    exact hg (e.symm x)
  refine ⟨exteriorPower.map 2 (e * g * e⁻¹).toLinearMap w,
    hstable _ hc w hw, ?_⟩
  change exteriorPower.map 2 e.symm.toLinearMap
      (exteriorPower.map 2 (e * g * e⁻¹).toLinearMap w) =
    exteriorPower.map 2 g.toLinearMap
      (exteriorPower.map 2 e.symm.toLinearMap w)
  have hcmap : e.symm.toLinearMap.comp (e * g * e⁻¹).toLinearMap =
      g.toLinearMap.comp e.symm.toLinearMap := by
    ext x
    simp
  simpa only [exteriorPower.map_comp, LinearMap.comp_apply] using
    LinearMap.congr_fun (congrArg (exteriorPower.map 2) hcmap) w

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors.Alignment.ExteriorGeometry
