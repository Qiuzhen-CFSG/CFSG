module

public import Theory.Representation.MathieuCodeRestriction.Actions
public import Theory.Representation.BinaryOffender.CommutatorRank
public import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Eleven coordinates on the literal Mathieu cocode

Subtract the Golay encoder at its twelve pivot coordinates and retain eleven
nonpivot coordinates. The even words supported on each retained coordinate
and point 23 give a right inverse. Since the cocode has dimension eleven,
this is a linear equivalence. The native action's displacement matrix therefore
has exactly the fixed codimension of its generator on the actual quotient.

These coordinates support the involution calculations of Aschbacher–Smith,
H.14.4(3), combined manuscript of 1 March 2004, printed pp.397–399.
-/

@[expose] public section

open Sporadic.Mathieu Representation.BinaryOffender
open scoped BigOperators
namespace MathieuCode.CocodeOctad.Involutions
noncomputable section

abbrev Coordinates := Fin 11 → ZMod 2

def nonpivot : Fin 11 → Fin 24 := ![10,12,14,15,16,17,18,19,20,21,22]

def reduce : Full →ₗ[ZMod 2] Coordinates where
  toFun v i := v (nonpivot i) - ∑ j, v (pivot j) * row j (nonpivot i)
  map_add' v w := by ext i; simp [add_mul, Finset.sum_add_distrib]; ring
  map_smul' c v := by ext i; simp [mul_assoc, ← Finset.mul_sum, mul_sub]

lemma reduce_row (j : Fin 12) : reduce (row j) = 0 := by
  ext i
  simp [reduce, row_pivot]

lemma golay_le_reduce_ker : golay ≤ reduce.ker := by
  apply Submodule.span_le.mpr
  rintro _ ⟨j, rfl⟩
  exact reduce_row j

def coordinates : Cocode →ₗ[ZMod 2] Coordinates :=
  codeInCore.liftQ (reduce.comp Core.subtype) (fun _ hv => golay_le_reduce_ker hv)

lemma coordinates_mk (v : Core) : coordinates (codeInCore.mkQ v) = reduce v.val := rfl

def coordinateWord (j : Fin 11) : Core :=
  ⟨Pi.single (nonpivot j) 1 + Pi.single 23 1, by
    simp [BinaryPermutation.mem_core, Finset.sum_add_distrib]
    exact CharTwo.add_self_eq_zero (1 : ZMod 2)⟩

lemma reduce_coordinateWord : ∀ j : Fin 11,
    reduce (coordinateWord j).val = Pi.single j 1 := by
  decide +kernel

lemma pi_ext_one {n : ℕ} {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    {f g : (Fin n → ZMod 2) →ₗ[ZMod 2] W}
    (h : ∀ j, f (Pi.single j 1) = g (Pi.single j 1)) : f = g := by
  apply LinearMap.pi_ext
  intro j c
  have he : Pi.single j c = c • (Pi.single j 1 : Fin n → ZMod 2) := by
    simp [← Pi.single_smul]
  rw [he, map_smul, map_smul, h]

def sectionMap : Coordinates →ₗ[ZMod 2] Cocode :=
  ∑ j, (LinearMap.proj j).smulRight (codeInCore.mkQ (coordinateWord j))

lemma sectionMap_single (j : Fin 11) :
    sectionMap (Pi.single j 1) = codeInCore.mkQ (coordinateWord j) := by
  simp [sectionMap, Pi.single_apply]

lemma coordinates_sectionMap : coordinates.comp sectionMap = LinearMap.id := by
  apply pi_ext_one
  intro j
  simp only [LinearMap.comp_apply, sectionMap_single, coordinates_mk,
    reduce_coordinateWord, LinearMap.id_apply]

lemma coordinates_surjective : Function.Surjective coordinates := by
  intro v
  exact ⟨sectionMap v, LinearMap.congr_fun coordinates_sectionMap v⟩

def coordinateEquiv : Cocode ≃ₗ[ZMod 2] Coordinates :=
  LinearEquiv.ofBijective coordinates ⟨
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by rw [finrank_cocode]; simp [Coordinates])).mpr coordinates_surjective,
    coordinates_surjective⟩

lemma sectionMap_coordinates : sectionMap.comp coordinates = LinearMap.id := by
  apply LinearMap.ext
  intro v
  apply coordinateEquiv.injective
  exact LinearMap.congr_fun coordinates_sectionMap (coordinates v)

lemma sectionMap_surjective : Function.Surjective sectionMap := by
  intro v
  exact ⟨coordinates v, LinearMap.congr_fun sectionMap_coordinates v⟩

/-- Displacement matrix computed directly from the native permutation. -/
def displacementMatrix (g : M24) : Matrix (Fin 11) (Fin 11) (ZMod 2) :=
  fun i j => reduce (fullRepresentation g (coordinateWord j).val) i -
    (Pi.single j 1 : Coordinates) i

lemma displacementMatrix_eq (g : M24) :
    (displacementMatrix g).mulVecLin =
      (coordinates.comp (cocodeRepresentation g - LinearMap.id)).comp sectionMap := by
  apply pi_ext_one
  intro j
  ext i
  simp only [Matrix.mulVecLin_apply, Matrix.mulVec_single, MulOpposite.op_one, one_smul,
    LinearMap.comp_apply, sectionMap_single, LinearMap.sub_apply, LinearMap.id_apply,
    map_sub, cocodeRepresentation_mk, coordinates_mk, reduce_coordinateWord]
  rfl

lemma fixedCodim_eq_matrix_rank (g : M24) :
    fixedCodim cocodeRepresentation (Subgroup.zpowers g) = (displacementMatrix g).rank := by
  rw [fixedCodim_zpowers_eq_displacement_rank, Matrix.rank, displacementMatrix_eq,
    LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr sectionMap_surjective),
    LinearMap.range_comp]
  exact (coordinateEquiv.finrank_map_eq _).symm


end
end MathieuCode.CocodeOctad.Involutions
