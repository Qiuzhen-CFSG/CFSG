/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Lattices/IcosianAxisDirectSum.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Lattices.IcosianLatticeGlueQuotient
public import Theory.AtlasPort.Janko2.Lattices.IcosianAxisIntersection
public import Mathlib.Algebra.DirectSum.Module

/-!
# Icosian Axis Direct Sum

The three coordinate-axis intersections of the lattice form a direct sum
equal to twice the full integral coordinate module. Coordinate projections
construct the inverse of the summation map, including the external direct sum.

Source: Gerald Höhn, ATLAS, `Atlas/Lattices/IcosianAxisDirectSum.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0: module/public imports and exposed public
coordinate definitions; concrete carriers and theorem statements are retained.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Lattices
open Atlas.Algebra Atlas.Codes
open scoped BigOperators DirectSum

/-- Twice the full integral coordinate module. -/
def icosianTwiceCoordinates : Submodule icosianOrderᵐᵒᵖ IcosianCoordinates where
  carrier := {x | ∀ i,icosianModuloTwo (x i)=0}
  zero_mem' := by intro i; exact map_zero _
  add_mem' := by intro x y hx hy i; simp only [Pi.add_apply,map_add,hx i,hy i,add_zero]
  smul_mem' := by
    intro a x hx i
    change icosianModuloTwo (x i*a.unop)=0
    rw [map_mul,hx,zero_mul]

theorem icosianTwiceCoordinates_mem (x : IcosianCoordinates) :
    x ∈ icosianTwiceCoordinates ↔ ∃ y : IcosianCoordinates,x=(2 : ℤ) • y := by
  constructor
  · intro hx
    choose y hy using fun i => (icosianModuloTwo_eq_zero_iff_two_mul (x i)).mp (hx i)
    exact ⟨y,funext fun i => by simpa only [Pi.smul_apply,two_smul,two_mul] using hy i⟩
  · rintro ⟨y,rfl⟩ i
    apply (icosianModuloTwo_eq_zero_iff_two_mul _).mpr
    exact ⟨y i,by simp only [Pi.smul_apply,two_smul,two_mul]⟩

theorem icosianTwiceCoordinates_le_lattice : icosianTwiceCoordinates ≤ icosianLeechModule := by
  intro x hx
  rw [icosianLeechModule_matrix_glue]
  have he : (fun i => icosianModuloTwo (x i))=0 := funext hx
  rw [he]
  exact (icosianMatrixGlue GoldenFour).zero_mem

/-- The actual coordinate axis as an integral right module. -/
def icosianCoordinateAxis (i : Fin 3) : Submodule icosianOrderᵐᵒᵖ IcosianCoordinates where
  carrier := {x | ∀ j,j≠i → x j=0}
  zero_mem' := by simp
  add_mem' := by intro x y hx hy j hj; simp [hx j hj,hy j hj]
  smul_mem' := by intro a x hx j hj; simp [Pi.smul_apply,hx j hj]

def icosianLatticeAxis (i : Fin 3) : Submodule icosianOrderᵐᵒᵖ IcosianCoordinates :=
  icosianLeechModule ⊓ icosianCoordinateAxis i

theorem icosianLatticeAxis_le_twice (i : Fin 3) : icosianLatticeAxis i ≤ icosianTwiceCoordinates := by
  rintro x ⟨hx,hi⟩
  have he : x=icosianSingle i (x i) := by
    funext j
    by_cases hj : j=i
    · subst j; simp [icosianSingle]
    · simp [icosianSingle,hj,hi j hj]
  have hz : icosianModuloTwo (x i)=0 := by
    rw [he] at hx
    exact (icosianSingle_mem i (x i)).mp hx
  intro j
  by_cases hj : j=i
  · simpa only [hj] using hz
  · rw [hi j hj,map_zero]

theorem icosianTwice_single_mem_axis (x : icosianTwiceCoordinates) (i : Fin 3) :
    icosianSingle i (x.val i) ∈ icosianLatticeAxis i := by
  constructor
  · exact (icosianSingle_mem i (x.val i)).mpr (x.property i)
  · intro j hj
    simp [icosianSingle,hj]

def icosianAxisSum : (Π i : Fin 3,icosianLatticeAxis i) →ₗ[icosianOrderᵐᵒᵖ]
    icosianTwiceCoordinates where
  toFun x := ⟨∑ i,(x i).val,icosianTwiceCoordinates.sum_mem fun i _ =>
    icosianLatticeAxis_le_twice i (x i).property⟩
  map_add' x y := by apply Subtype.ext; simp [Finset.sum_add_distrib]
  map_smul' a x := by apply Subtype.ext; simp [Finset.smul_sum]

theorem icosianAxisSum_coordinate (x : Π i : Fin 3,icosianLatticeAxis i) (j : Fin 3) :
    (icosianAxisSum x).val j = (x j).val j := by
  change (∑ i,(x i).val) j = _
  rw [Finset.sum_apply]
  apply Finset.sum_eq_single j
  · intro b _ hbj
    exact (x b).property.2 j (Ne.symm hbj)
  · simp

theorem icosianAxisSum_bijective : Function.Bijective icosianAxisSum := by
  constructor
  · intro x y h
    funext i
    apply Subtype.ext
    funext j
    by_cases hj : j=i
    · subst j
      have he := congrFun (congrArg Subtype.val h) i
      simpa only [icosianAxisSum_coordinate] using he
    · rw [(x i).property.2 j hj,(y i).property.2 j hj]
  · intro x
    refine ⟨fun i => ⟨icosianSingle i (x.val i),icosianTwice_single_mem_axis x i⟩,?_⟩
    apply Subtype.ext
    funext j
    rw [icosianAxisSum_coordinate]
    simp [icosianSingle]

/-- The three actual lattice-axis intersections form a direct sum equal to2I³. -/
def icosianAxisDirectSumEquiv :
    (Π i : Fin 3,icosianLatticeAxis i) ≃ₗ[icosianOrderᵐᵒᵖ] icosianTwiceCoordinates :=
  LinearEquiv.ofBijective icosianAxisSum icosianAxisSum_bijective

theorem icosianLatticeAxes_iSup : (⨆ i : Fin 3,icosianLatticeAxis i)=icosianTwiceCoordinates := by
  apply le_antisymm
  · exact iSup_le icosianLatticeAxis_le_twice
  · intro x hx
    obtain ⟨y,hy⟩ := icosianAxisSum_bijective.2 ⟨x,hx⟩
    have he := congrArg Subtype.val hy
    change (∑ i,(y i).val)=x at he
    rw [← he]
    exact Submodule.sum_mem _ fun i _ => Submodule.mem_iSup_of_mem i (y i).property

theorem icosianLatticeTwice_eq_axes_comap :
    icosianLatticeTwice = (⨆ i : Fin 3,icosianLatticeAxis i).comap icosianLeechModule.subtype := by
  rw [icosianLatticeAxes_iSup]
  ext x
  change x ∈ icosianLatticeTwice ↔ x.val ∈ icosianTwiceCoordinates
  rw [icosianLatticeTwice_mem,icosianTwiceCoordinates_mem]

/-- Literal finite direct-sum formulation of the coordinate intersection result. -/
def icosianAxisExternalDirectSumEquiv :
    (⨁ i : Fin 3,icosianLatticeAxis i) ≃ₗ[icosianOrderᵐᵒᵖ] icosianTwiceCoordinates :=
  (DirectSum.linearEquivFunOnFintype icosianOrderᵐᵒᵖ (Fin 3) (fun i => ↥(icosianLatticeAxis i))).trans
    icosianAxisDirectSumEquiv

end Atlas.Lattices
