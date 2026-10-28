module

public import Theory.AtlasPort.LinearGroups.G2.SolvableSylowPlacement.Cells
public import Theory.AtlasPort.LinearGroups.G2.PointOrbits

/-!
# Six unipotent orbits on singular octonion vectors

Successively inspect coordinates 7, 6, 5, 2, 1, 0. Positive root operations
eliminate the earlier coordinates, and the norm equation eliminates the
remaining coordinate opposite the pivot. This refines the four parabolic
orbits of `PointOrbits` into six unipotent orbits, over every field.

This is the vector-reduction step of the concrete existence part of GLS III,
Theorem 2.3.5 (`refs/KGroup/GLS3/chapter2.tex`). The reducers extend the licensed
ATLAS coordinate calculations in `SingularReduction` and `PointOrbits`,
revision 8eabb35afe2b5e45bf913a2d05c53e558d2e2917; see LICENSES/ATLAS.txt
and LICENSES/ATLAS-CITATION.cff.
-/

@[expose] public section

namespace Atlas.G2.SolvableSylowPlacement.BruhatGeometry
open Atlas.SplitOctonion Explicit PairStabilizer
variable {F : Type*} [Field F]

private def fifthReducer (x : Carrier F) : Model F :=
  let y := (rootF (-x 3 / x 5)).val x
  let z := (rootC (y 1 / y 5)).val y
  rootB (z 0 / z 5) * rootC (y 1 / y 5) * rootF (-x 3 / x 5)

private theorem fifthReducer_mem (x : Carrier F) : fifthReducer x ∈ unipotent := by
  apply unipotent.mul_mem
  · apply unipotent.mul_mem
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
  · exact Subgroup.subset_closure (by simp)

private theorem fifthReducer_eq (x : Carrier F) (ht : trace x = 0)
    (hn : SplitOctonion.norm x = 0) (h7 : x 7 = 0) (h6 : x 6 = 0) (h5 : x 5 ≠ 0) :
    (fifthReducer x).val x = x 5 • basisVector 5 := by
  have h4 : x 4 = -x 3 := eq_neg_of_add_eq_zero_right ht
  have hcoords : ∀ i : Fin 8, i ≠ 2 →
      (fifthReducer x).val x i = (x 5 • basisVector 5) i := by
    intro i hi
    fin_cases i <;> try contradiction
    all_goals simp [fifthReducer,rootB,rootC,rootF,rootBEquiv,rootCEquiv,
      rootFEquiv,rootBLinear,rootCLinear,rootFLinear,
      rootBApply,rootCApply,rootFApply,basisVector,h7,h6,h4]
    all_goals field_simp
    all_goals ring
  have hz := (automorphism_norm (fifthReducer x) x).trans hn
  have hzero : (fifthReducer x).val x 2 = 0 := by
    simp only [SplitOctonion.norm] at hz
    rw [hcoords 0 (by decide),hcoords 1 (by decide),hcoords 3 (by decide),
      hcoords 4 (by decide),hcoords 5 (by decide),hcoords 6 (by decide),hcoords 7 (by decide)] at hz
    simp [basisVector] at hz
    exact hz.resolve_right h5
  funext i
  by_cases hi : i = 2
  · subst i; simp [hzero,basisVector]
  · exact hcoords i hi

private theorem middleReducer_mem_unipotent (x : Carrier F) : middleReducer x ∈ unipotent := by
  apply unipotent.mul_mem
  · apply unipotent.mul_mem
    · apply unipotent.mul_mem
      · exact Subgroup.subset_closure (by simp)
      · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
  · exact Subgroup.subset_closure (by simp)

/-- Coordinate lines indexing the six positive-unipotent orbits. -/
def vectorIndex : Fin 6 → Fin 8 := ![0,1,2,5,6,7]

/-- Positive roots reduce a singular vector to one of six coordinate lines. -/
theorem unipotent_vector_reduction (x : Carrier F) (ht : trace x = 0)
    (hn : SplitOctonion.norm x = 0) (hx : x ≠ 0) :
    ∃ u ∈ unipotent (K := F), ∃ i : Fin 6, ∃ a : F, a ≠ 0 ∧
      u.val x = a • basisVector (vectorIndex i) := by
  by_cases h7 : x 7 = 0
  swap
  · exact ⟨chartReducer x, chartReducer_mem_unipotent x, 5, x 7, h7,
      chartReducer_eq x ht hn h7⟩
  by_cases h6 : x 6 = 0
  swap
  · exact ⟨middleReducer x, middleReducer_mem_unipotent x, 4, x 6, h6,
      middleReducer_eq x ht hn h7 h6⟩
  by_cases h5 : x 5 = 0
  swap
  · exact ⟨fifthReducer x, fifthReducer_mem x, 3, x 5, h5,
      fifthReducer_eq x ht hn h7 h6 h5⟩
  obtain ⟨h3,h4⟩ := lower_stratum_diagonal_zero x ht hn h5 h6 h7
  by_cases h2 : x 2 = 0
  swap
  · refine ⟨rootD (x 0 / x 2) * rootE (x 1 / x 2),
      unipotent.mul_mem (Subgroup.subset_closure (by simp))
        (Subgroup.subset_closure (by simp)), 2, x 2, h2, ?_⟩
    funext i
    fin_cases i <;> simp [rootD,rootDEquiv,rootDLinear,rootDApply,
      rootE,rootEEquiv,rootELinear,rootEApply,basisVector,vectorIndex,h3,h4,h5,h6,h7]
    all_goals field_simp
    all_goals ring
  by_cases h1 : x 1 = 0
  swap
  · refine ⟨rootF (x 0 / x 1), Subgroup.subset_closure (by simp), 1, x 1, h1, ?_⟩
    funext i
    fin_cases i <;> simp [rootF,rootFEquiv,rootFLinear,rootFApply,
      basisVector,vectorIndex,h2,h3,h4,h5,h6,h7]
    field_simp
    ring
  have he : x = x 0 • basisVector 0 := by
    funext i
    fin_cases i <;> simp [basisVector,h1,h2,h3,h4,h5,h6,h7]
  have h0 : x 0 ≠ 0 := by
    intro hh
    apply hx
    rw [he,hh,zero_smul]
  exact ⟨1,unipotent.one_mem,0,x 0,h0,he⟩

end Atlas.G2.SolvableSylowPlacement.BruhatGeometry
