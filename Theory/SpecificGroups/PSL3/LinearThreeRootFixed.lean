module
public import Theory.SpecificGroups.PSL3.LinearThreeAdditiveRadical

/-!
# The fixed line of the linear-three point radical

The two elementary transvections in the first row force the last two
coordinates of a fixed natural vector to vanish. Conversely the entire
point local fixes the first coordinate line. This identifies the fixed
space for the literal point radical over every field.

The source application identifies the center of the original secondary
radical in Aschbacher--Smith 4.3.14, printed pp.617--618.
-/

public section
open Subgroup Matrix
open scoped MatrixGroups
namespace Matrix.PSL3.LinearThree
variable (F : Type*) [Field F]

theorem pointRadicalSL_fixed_iff (v : Fin 3 → F) :
    (∀ g : pointLocalSL F, g ∈ pointRadicalSL F → g.val.val.mulVec v = v) ↔
      ∃ a : F, v = a • (![1,0,0] : Fin 3 → F) := by
  constructor
  · intro h
    let x : SL(3,F) := ⟨!![1,1,0;0,1,0;0,0,1], by simp [det_fin_three]⟩
    let y : SL(3,F) := ⟨!![1,0,1;0,1,0;0,0,1], by simp [det_fin_three]⟩
    have hx : x ∈ pointLocalSL F := by rw [mem_pointLocalSL_iff]; simp [x]
    have hy : y ∈ pointLocalSL F := by rw [mem_pointLocalSL_iff]; simp [y]
    have hxr : (⟨x,hx⟩ : pointLocalSL F) ∈ pointRadicalSL F := by
      rw [mem_pointRadicalSL_iff]; simp [x]
    have hyr : (⟨y,hy⟩ : pointLocalSL F) ∈ pointRadicalSL F := by
      rw [mem_pointRadicalSL_iff]; simp [y]
    have h1 := congrFun (h ⟨x,hx⟩ hxr) 0
    have h2 := congrFun (h ⟨y,hy⟩ hyr) 0
    have hv1 : v 1 = 0 := by simpa [x,mulVec,dotProduct,Fin.sum_univ_three] using h1
    have hv2 : v 2 = 0 := by simpa [y,mulVec,dotProduct,Fin.sum_univ_three] using h2
    refine ⟨v 0,?_⟩
    ext i
    fin_cases i <;> simp [hv1,hv2]
  · rintro ⟨a,rfl⟩ g _
    rw [mulVec_smul,show g.val.val.mulVec (![1,0,0] : Fin 3 → F) = ![1,0,0] from g.property]

end Matrix.PSL3.LinearThree
