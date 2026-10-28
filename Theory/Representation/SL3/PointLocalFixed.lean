module
public import Theory.Representation.SL3.DualLiftCentralizers

/-!
# Fixed points of the SL₃ vector stabilizer

The vector stabilizer fixes exactly its defining line on the natural module
and has no fixed covectors on the dual module. Elementary transvections
prove both statements, over any field and with the original point-local
convention. The nonblock source application uses them on the natural center
and both dual factors to compute C_Q(K₂).

Source: Aschbacher--Smith, C.1.34(3), pp.136--137, and original 4.3.2,
pp.617--619; the point-local matrix coordinates of A.3.14.
-/

public section
open Subgroup Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups
namespace Representation.SL3ParabolicNatural
open Matrix.PSL3.LinearThree
variable {F : Type*} [Field F]

theorem point_fixed_line (v : Fin 3 → F)
    (hv : ∀ g ∈ pointLocalSL F, specialLinearNatural 3 g v = v) :
    ∃ a : F, v = a • (![1,0,0] : Fin 3 → F) := by
  have ht {i : Fin 3} (hi : i ≠ 0) :
      transvection (Ne.symm hi) (1:F) ∈ pointLocalSL F := by
    rw [mem_pointLocalSL_iff]
    simp [transvection_coe, hi]
  have h1 := congrFun (hv _ (ht (by decide : (1 : Fin 3) ≠ 0))) 0
  have h2 := congrFun (hv _ (ht (by decide : (2 : Fin 3) ≠ 0))) 0
  rw [OneCohomology.SLHigherNatural.action_transvection] at h1 h2
  have hv1 : v 1 = 0 := by simpa using h1
  have hv2 : v 2 = 0 := by simpa using h2
  refine ⟨v 0, ?_⟩
  ext i
  fin_cases i <;> simp [hv1,hv2]

theorem point_dual_fixed_zero (f : Module.Dual F (Fin 3 → F))
    (hf : ∀ g ∈ pointLocalSL F, (specialLinearNatural 3).dual g f = f) : f = 0 := by
  have he (g : SL(3,F)) (hg : g ∈ pointLocalSL F) (v : Fin 3 → F) :
      f (specialLinearNatural 3 g v) = f v := by
    have hh := LinearMap.congr_fun (hf g⁻¹ ((pointLocalSL F).inv_mem hg)) v
    simpa only [Representation.dual_apply,inv_inv,Module.Dual.transpose_apply,LinearMap.comp_apply] using hh
  have hc {i j : Fin 3} (hij : i ≠ j) (hj : j ≠ 0) : f (Pi.single i 1) = 0 := by
    have ht : transvection hij (1:F) ∈ pointLocalSL F := by
      rw [mem_pointLocalSL_iff]
      simp [transvection_coe,hj]
    have hh := he _ ht (Pi.single j 1)
    rw [OneCohomology.SLHigherNatural.action_transvection] at hh
    simpa using hh
  apply (dualVectorCoordinates (F := F)).injective
  ext i
  rw [dualVectorCoordinates_apply,map_zero]
  fin_cases i
  · exact hc (by decide : (0 : Fin 3) ≠ 1) (by decide)
  · exact hc (by decide : (1 : Fin 3) ≠ 2) (by decide)
  · exact hc (by decide : (2 : Fin 3) ≠ 1) (by decide)
end Representation.SL3ParabolicNatural
