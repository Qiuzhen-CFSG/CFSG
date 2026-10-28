module
public import Theory.Representation.SL5ExteriorSquare.DecomposablePreserver.Basic
public import Theory.LinearAlgebra.AdjacentSubspaceClique
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-!
# Adjacency of decomposable support planes

For a simple binary bivector the quadratic Plücker expressions vanish.
After transporting one summand to e₀ ∧ e₁, the expressions for it, the other
summand and their sum force the latter's lower three-by-three block to vanish.
Its nonzero symmetric coefficient matrix then has a nonzero column in the
first two-space. Transporting back gives a common support vector.

This supplies the adjacency hypothesis of the Grassmann clique argument in
Meierfrankenfeld–Stellmacher (1993), (1.6), pp.845–847. It uses the quadratic
Plücker expressions, not the vacuous characteristic-two exterior square test.
-/

public section

open scoped Matrix
namespace Representation.SL5ExteriorSquare
open SL5TenDimensional
namespace DecomposablePreserver

theorem plucker_wedge (a b : N) (i j k l : Fin 5) :
    bivectorMatrix (wedge a b) i j * bivectorMatrix (wedge a b) k l +
    bivectorMatrix (wedge a b) i k * bivectorMatrix (wedge a b) j l +
    bivectorMatrix (wedge a b) i l * bivectorMatrix (wedge a b) j k = 0 := by
  simp only [bivectorMatrix_wedge, Matrix.of_apply]
  ring_nf
  simp only [show (2 : ZMod 2) = 0 from rfl, mul_zero, add_zero]

theorem plucker_of_decomposable {v : V} (hv : InExteriorOrbit decomposable v)
    (i j k l : Fin 5) :
    bivectorMatrix v i j * bivectorMatrix v k l +
    bivectorMatrix v i k * bivectorMatrix v j l +
    bivectorMatrix v i l * bivectorMatrix v j k = 0 := by
  obtain ⟨a,b,rfl⟩ := exists_wedge_of_decomposable hv
  exact plucker_wedge a b i j k l

theorem bivectorMatrix_add (v w : V) :
    bivectorMatrix (v+w) = bivectorMatrix v + bivectorMatrix w := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [bivectorMatrix, alternatingMatrix]

theorem tail_zero_of_decomposable_sum {v : V} (hv : InExteriorOrbit decomposable v)
    (hs : InExteriorOrbit decomposable (decomposable + v)) :
    coordinates v 7 = 0 ∧ coordinates v 8 = 0 ∧ coordinates v 9 = 0 := by
  have h (k l : Fin 5) := plucker_of_decomposable hv 0 1 k l
  have h' (k l : Fin 5) := plucker_of_decomposable hs 0 1 k l
  have h7 := h 2 3
  have h8 := h 2 4
  have h9 := h 3 4
  have h7' := h' 2 3
  have h8' := h' 2 4
  have h9' := h' 3 4
  simp [-coordinates_apply, bivectorMatrix, alternatingMatrix,
    coordinates_decomposable] at h7 h8 h9 h7' h8' h9'
  constructor
  · linear_combination h7' - h7
  constructor
  · linear_combination h8' - h8
  · linear_combination h9' - h9

theorem column_mem_support (v : V) (j : Fin 5) :
    (fun i => bivectorMatrix v i j) ∈ support v := by
  refine ⟨Pi.single j 1, ?_⟩
  change (bivectorMatrix v).mulVec (Pi.single j 1) = _
  exact Matrix.mulVec_single_one (bivectorMatrix v) j

theorem common_vector_of_tail_zero {v : V} (hv : v ≠ 0)
    (ht : coordinates v 7 = 0 ∧ coordinates v 8 = 0 ∧ coordinates v 9 = 0) :
    ∃ a : N, a ≠ 0 ∧ a ∈ naturalFlag 2 ∧ a ∈ support v := by
  by_contra! hn
  have kill (a : N) (ha : a ∈ naturalFlag 2) (hs : a ∈ support v) : a = 0 := by
    by_contra h0
    exact hn a h0 ha hs
  have tail (j : Fin 5) (hj : 2 ≤ j.val) : (fun i => bivectorMatrix v i j) = 0 := by
    apply kill _ _ (column_mem_support v j)
    change ∀ i : Fin 5, 2 ≤ i.val → bivectorMatrix v i j = 0
    intro i hi
    fin_cases i <;> fin_cases j <;>
      simp_all [bivectorMatrix, alternatingMatrix, -coordinates_apply]
  have allcol (j : Fin 5) : (fun i => bivectorMatrix v i j) = 0 := by
    apply kill _ _ (column_mem_support v j)
    change ∀ i : Fin 5, 2 ≤ i.val → bivectorMatrix v i j = 0
    intro i hi
    have he := congrFun (tail i hi) j
    have hs := congrArg (fun M => M j i) (alternatingMatrix_transpose (coordinates v))
    exact hs.trans he
  apply hv
  apply bivectorMatrix_injective
  rw [bivectorMatrix_zero]
  ext i j
  exact congrFun (allcol j) i

theorem common_vector_standard {v : V} (hv : InExteriorOrbit decomposable v)
    (hs : InExteriorOrbit decomposable (decomposable + v)) :
    ∃ a : N, a ≠ 0 ∧ a ∈ support decomposable ∧ a ∈ support v := by
  have h0 : v ≠ 0 := fun hz => decomposable_ne_zero (hv.eq_zero_iff.mpr hz)
  simpa only [support, range_bivectorMatrix_decomposable] using
    common_vector_of_tail_zero h0 (tail_zero_of_decomposable_sum hv hs)

theorem support_action (g : Group) (v : V) :
    support (exteriorAction 2 g v) = (support v).map (specialLinearNatural 5 g) :=
  range_bivectorMatrix_action g v

theorem action_inv_cancel (g : Group) (v : V) :
    exteriorAction 2 g (exteriorAction 2 g⁻¹ v) = v := by
  change (exteriorAction 2 g * exteriorAction 2 g⁻¹) v = v
  rw [← map_mul, mul_inv_cancel, map_one]
  rfl

theorem common_vector_of_decomposable_sum {v w : V}
    (hv : InExteriorOrbit decomposable v) (hw : InExteriorOrbit decomposable w)
    (hs : InExteriorOrbit decomposable (v+w)) :
    ∃ a : N, a ≠ 0 ∧ a ∈ support v ∧ a ∈ support w := by
  obtain ⟨g,rfl⟩ := hv
  have hw' : InExteriorOrbit decomposable (exteriorAction 2 g⁻¹ w) :=
    hw.trans ⟨g⁻¹,rfl⟩
  have hs' : InExteriorOrbit decomposable
      (decomposable + exteriorAction 2 g⁻¹ w) := by
    have h : InExteriorOrbit decomposable (exteriorAction 2 g⁻¹
      (exteriorAction 2 g decomposable + w)) := hs.trans ⟨g⁻¹,rfl⟩
    have hc : exteriorAction 2 g⁻¹ (exteriorAction 2 g decomposable) = decomposable := by
      simpa only [inv_inv] using action_inv_cancel g⁻¹ decomposable
    simpa only [map_add, hc] using h
  obtain ⟨a,ha,ha1,ha2⟩ := common_vector_standard hw' hs'
  refine ⟨specialLinearNatural 5 g a, ?_, ?_, ?_⟩
  · intro hz
    exact ha ((Matrix.SpecialLinearGroup.toLin' g).injective
      (hz.trans (map_zero _).symm))
  · rw [support_action]
    exact ⟨a,ha1,rfl⟩
  · rw [← action_inv_cancel g w, support_action]
    exact ⟨a,ha2,rfl⟩

theorem supports_adjacent {v w : V}
    (hv : InExteriorOrbit decomposable v) (hw : InExteriorOrbit decomposable w)
    (hs : v = w ∨ InExteriorOrbit decomposable (v+w)) :
    2 ≤ Module.finrank (ZMod 2) ↥(support v ⊓ support w) + 1 := by
  rcases hs with rfl | hs
  · rw [inf_idem, finrank_support_of_decomposable hw]
    omega
  · obtain ⟨a,ha,ha1,ha2⟩ := common_vector_of_decomposable_sum hv hw hs
    have hle : Submodule.span (ZMod 2) {a} ≤ support v ⊓ support w :=
      (Submodule.span_singleton_le_iff_mem _ _).mpr ⟨ha1,ha2⟩
    have hd := Submodule.finrank_mono hle
    rw [finrank_span_singleton ha] at hd
    omega

end DecomposablePreserver
end Representation.SL5ExteriorSquare
