module

public import Theory.SpecificGroups.PSL3.SmallCompletion.Weyl

/-!
# The point-parabolic centralizer of the coordinate three-cycle

A projective commuting equation lifts with its complete scalar factor.
The fixed first column and the coordinate three-cycle then force every
off-diagonal entry to vanish. Thus the centralizer inside the original point
parabolic lies in the full projective torus.
-/

public section
open Matrix Subgroup
open scoped MatrixGroups
namespace Matrix.PSL3.SmallCompletion
open Matrix.PSL3.LinearThree Matrix.PSL3.CartanActions
variable (F : Type*) [Field F] [Finite F] [CharP F 2]

omit [Finite F] [CharP F 2] in
private theorem scalar_of_projection_eq (x y : SL(3,F))
    (h : projection F x=projection F y) :
    ∃ a : F, a^3=1 ∧ x.val=a • y.val := by
  have hc := (projection F).eq_iff.mp h
  rw [projection_ker] at hc
  obtain ⟨a,ha,he⟩ := SpecialLinearGroup.mem_center_iff.mp hc
  refine ⟨a,ha,?_⟩
  calc
    x.val=(y*(y⁻¹*x)).val := by simp only [mul_inv_cancel_left]
    _=y.val*Matrix.scalar (Fin 3) a := by rw [SpecialLinearGroup.coe_mul,←he]
    _=a • y.val := by ext i j; simp [Matrix.scalar,Matrix.mul_diagonal,mul_comm]

/-- The actual point-parabolic centralizer of the standard exterior cubic
lies in the full torus, with no assumption discarding projective scalars. -/
theorem point_cycle_centralizer_le_torus (x : PSL(3,F))
    (hx : x∈pointParabolic F)
    (hc : Commute x (reflection F false*reflection F true)) : x∈torus F := by
  obtain ⟨g,rfl⟩ := projection_surjective F x
  have hg : g∈pointParabolicSL F := (pointParabolic_comap F) ▸ hx
  obtain ⟨h10,h20⟩ := (mem_pointParabolicSL_iff F g).mp hg
  let c := reflectionSL F false*reflectionSL F true
  have he : projection F (g*c)=projection F (c*g) := by
    simpa only [c,map_mul,reflection] using hc.eq
  obtain ⟨a,ha,he⟩ := scalar_of_projection_eq F _ _ he
  have ha0 : a≠0 := by intro hh; simp [hh] at ha
  have hcval : c.val=!![0,1,0;0,0,1;1,0,0] := by
    change (reflectionSL F false).val*(reflectionSL F true).val=_
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [reflectionSL,Matrix.mul_apply,Fin.sum_univ_three]
  change g.val*c.val=a • (c.val*g.val) at he
  have h02 := congrFun (congrFun he 0) 0
  have h12 := congrFun (congrFun he 1) 0
  have h21 := congrFun (congrFun he 1) 1
  have h01 := congrFun (congrFun he 2) 1
  simp [hcval,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_three,
    h10,h20,ha0] at h02 h12 h21 h01
  change g∈(torus F).comap (projection F)
  rw [torus_comap,mem_torusSL_iff_entries]
  exact ⟨h01,h02,h10,h12,h20,h21⟩

end Matrix.PSL3.SmallCompletion
