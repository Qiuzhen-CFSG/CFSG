module
public import Theory.Representation.SL5ExteriorSquare.LocalGeometry.Assembly
import Mathlib.Tactic.FinCases

/-!
# Fixed spaces of the four full block radicals on the exterior square

Cross-block transvections force fixed vectors into the standard exterior
subspaces of dimensions four, one, three and six. The hyperplane radical
fixes exactly the last six-space, using the literal shear calculation.
Source: Aschbacher--Smith 12.5.2 and C.4.8, pp.817,154.
-/
public noncomputable section
open Subgroup
namespace Representation.SL5ExteriorSquare
open SL5TenDimensional BinaryLinear.OuterCyclic

private def cutSupport : Fin 4 → Finset (Fin 10) :=
  ![{0,1,2,3},{0},{0,1,4},{0,1,2,4,5,7}]
private def cutLower : Fin 4 → Fin 10 → Fin 5 := ![
  ![0,0,0,0,0,0,0,0,0,0],
  ![0,1,1,1,0,0,0,0,0,0],
  ![0,0,1,1,0,0,0,0,0,0],
  ![0,0,0,1,0,0,0,0,0,0]]
private def cutUpper : Fin 4 → Fin 10 → Fin 5 := ![
  ![1,1,1,1,1,1,1,2,2,3],
  ![2,2,3,4,2,3,4,2,2,3],
  ![3,3,3,4,3,3,4,3,4,3],
  ![4,4,4,4,4,4,4,4,4,4]]
private def cutOutput : Fin 4 → Fin 10 → Fin 10 := ![
  ![0,0,0,0,1,2,3,2,3,3],
  ![0,0,0,0,0,0,0,2,3,3],
  ![0,0,0,0,0,0,0,1,1,3],
  ![0,0,0,0,0,0,0,0,1,2]]

private theorem elementary_cross_mem (k : ℕ) (i j : Fin 5)
    (hi : i.val < k) (hj : k ≤ j.val) : elementary i j ∈ parabolicUnipotent k := by
  have hij : i ≠ j := by intro h; subst j; omega
  have happly (v : Fin 5 → ZMod 2) :
      slEquivLinear 5 (elementary i j) v = v + Pi.single i (v j) := by
    simp only [elementary,dif_pos hij,slEquivLinear_apply,
      Matrix.SpecialLinearGroup.transvection_coe,Matrix.add_mulVec,
      Matrix.single_mulVec_eq,Matrix.one_mulVec]
    congr 1
    ext a
    by_cases ha : a = i <;> simp [ha]
  change (∀ v ∈ naturalFlag k, slEquivLinear 5 (elementary i j) v = v) ∧
    ∀ v, slEquivLinear 5 (elementary i j) v - v ∈ naturalFlag k
  constructor
  · intro v hv
    rw [happly,hv j hj]
    simp
  · intro v a ha
    rw [happly]
    simp [show a ≠ i by intro he; subst a; omega]

private theorem cut_coordinate_step (k : Fin 4) (v : V) (t : Fin 10)
    (ht : t ∉ cutSupport k) :
    coordinates (exteriorAction 2 (elementary (cutLower k t) (cutUpper k t)) v)
      (cutOutput k t) = coordinates v (cutOutput k t) + coordinates v t := by
  have row : actionMatrix (elementary (cutLower k t) (cutUpper k t)) (cutOutput k t) =
      Pi.single (cutOutput k t) 1 + Pi.single t 1 := by
    fin_cases k <;> fin_cases t
    all_goals first | exact (ht (by decide)).elim | (ext j; fin_cases j <;> rfl)
  rw [coordinates_action]
  change dotProduct (actionMatrix _ (cutOutput k t)) (coordinates v) = _
  rw [row,add_dotProduct]
  simp

private theorem fixed_le_cut_support (k : Fin 4) :
    BinaryOffender.fixedSpace (exteriorAction 2) (parabolicUnipotent (k.val+1)) ≤
      coordinateSpan (cutSupport k) := by
  intro v hv
  apply (mem_coordinateSpan _ _).mpr
  intro t ht
  have hlo : (cutLower k t).val < k.val+1 := by
    exact (by decide : ∀ (k : Fin 4) (t : Fin 10), (cutLower k t).val < k.val+1) k t
  have hhi : k.val+1 ≤ (cutUpper k t).val := by
    exact (by decide : ∀ (k : Fin 4) (t : Fin 10), k.val+1 ≤ (cutUpper k t).val) k t
  have he := hv ⟨_,elementary_cross_mem _ _ _ hlo hhi⟩
  change exteriorAction 2 (elementary (cutLower k t) (cutUpper k t)) v = v at he
  have hh := cut_coordinate_step k v t ht
  rw [he] at hh
  exact add_eq_left.mp hh.symm

/-- The literal full block radicals have fixed dimensions bounded by 4,1,3,6. -/
theorem finrank_fixed_parabolicUnipotent_le (k : Fin 4) :
    Module.finrank (ZMod 2)
      (BinaryOffender.fixedSpace (exteriorAction 2) (parabolicUnipotent (k.val+1))) ≤
        ![4,1,3,6] k := by
  have hd := Submodule.finrank_mono (fixed_le_cut_support k)
  rw [finrank_coordinateSpan] at hd
  have hc : (cutSupport k).card = ![4,1,3,6] k := by fin_cases k <;> decide
  exact hc ▸ hd

/-- The hyperplane block radical fixes exactly the original exterior six-space. -/
theorem fixedSpace_parabolicUnipotent_four :
    BinaryOffender.fixedSpace (exteriorAction 2) (parabolicUnipotent 4) = V₆ := by
  rw [parabolicUnipotent_four_eq_shearSubgroup]
  exact fixedSpace_shearSubgroup

end Representation.SL5ExteriorSquare
