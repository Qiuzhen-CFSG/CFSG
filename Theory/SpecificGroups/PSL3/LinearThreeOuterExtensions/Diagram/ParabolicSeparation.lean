module
public import Theory.SpecificGroups.PSL3.LinearThreeOuterExtensions.Diagram
import all Theory.SpecificGroups.PSL3.LinearThreeOuterExtensions.Diagram
/-!
# Point and plane parabolic classes over every finite field

A plane stabilizer cannot preserve a line: its three elementary shears
force each coordinate of any proposed spanning vector to vanish. Lift a
putative projective conjugacy through the literal SL₃ quotient and apply
this matrix observation to the first column of its conjugating matrix.
Thus point and plane parabolics have disjoint inner-conjugacy classes.
Inverse transpose exchanges them, so any inner translate of the graph
automorphism fails to preserve point type.

This extends the existing binary diagram geometry without changing its
public API. The internal import deliberately reuses the diagram family's
subgroup-map identities. Source: Aschbacher–Smith E.2.2(2d), printed
pp.215–216, and the actual A₂ diagram conventions in GLS3 §2.7.
-/
public section
open scoped MatrixGroups
open Subgroup Matrix Matrix.PSL3 Matrix.PSL3.LinearThree
open Matrix.PSL3.OuterSolvable Matrix.PSL3.RootPlaneGeometry
namespace Matrix.PSL3.LinearThree.OuterExtensions.ParabolicSeparation
variable (F:Type*) [Field F] [Finite F]

private theorem column_zero_of_root (g:SL(3,F)) (i j:Fin 3) (hij:i≠j)
    (hmem:g⁻¹ * SpecialLinearGroup.transvection hij (1:F) * g∈pointParabolicSL F) :
    g.val j 0=0 := by
  let x:=SpecialLinearGroup.transvection hij (1:F)
  let b:=g⁻¹*x*g
  have hb := (mem_pointParabolicSL_iff F b).mp hmem
  have he : x*g=g*b := by dsimp only [b]; group
  have hc (k:Fin 3) : (x.val*g.val) k 0=g.val k 0*b.val 0 0 := by
    have hh := congrArg (fun A:SL(3,F)=>A.val k 0) he
    change (x.val*g.val : Matrix (Fin 3) (Fin 3) F) k 0=(g.val*b.val) k 0 at hh
    simpa only [Matrix.mul_apply,Fin.sum_univ_three,hb.1,hb.2,mul_zero,add_zero] using hh
  by_contra hz
  have hj := hc j
  change (((1+single i j (1:F))*g.val):Matrix (Fin 3) (Fin 3) F) j 0=_ at hj
  rw [add_mul,one_mul,add_apply,
    single_mul_apply_of_ne (1:F) i j j 0 hij.symm,add_zero] at hj
  have ha : b.val 0 0=1 := by
    apply mul_left_cancel₀ hz
    simpa only [mul_one] using hj.symm
  have hi:=hc i
  change (((1+single i j (1:F))*g.val):Matrix (Fin 3) (Fin 3) F) i 0=_ at hi
  rw [add_mul,one_mul,add_apply,single_mul_apply_same,one_mul,ha,mul_one] at hi
  exact hz (add_eq_left.mp hi)

private theorem no_conjugate_line_in_point (g:SL(3,F))
    (h:∀x∈lineParabolicSL F,g⁻¹*x*g∈pointParabolicSL F) : False := by
  have hroot (i j:Fin 3) (hij:i≠j) (hi:i≠2) : g.val j 0=0 := by
    apply column_zero_of_root F g i j hij
    apply h
    rw [mem_lineParabolicSL_iff]
    fin_cases i <;> fin_cases j <;>
      simp_all [SpecialLinearGroup.transvection_coe]
  have h0:=hroot 1 0 (by decide) (by decide)
  have h1:=hroot 0 1 (by decide) (by decide)
  have h2:=hroot 0 2 (by decide) (by decide)
  have hh:=congrArg (fun A:SL(3,F)=>A.val 0 0) (inv_mul_cancel g)
  change (g⁻¹.val*g.val : Matrix (Fin 3) (Fin 3) F) 0 0=1 at hh
  simp only [Matrix.mul_apply,Fin.sum_univ_three,h0,h1,h2,mul_zero,zero_add] at hh
  exact zero_ne_one hh

/-- Point and plane stabilizers are not inner-conjugate over any finite field. -/
theorem pointParabolic_not_conjugate_line (g:PSL(3,F)) :
    (pointParabolic F).map (MulAut.conj g).toMonoidHom≠lineParabolic F := by
  intro he
  obtain ⟨g,rfl⟩:=projection_surjective F g
  apply no_conjugate_line_in_point F g
  intro x hx
  have hxp : projection F x∈(pointParabolic F).map
      (MulAut.conj (projection F g)).toMonoidHom :=
    he ▸ mem_map_of_mem (projection F) hx
  have hm := (mem_map_equiv).mp hxp
  have hq : projection F (g⁻¹*x*g)∈pointParabolic F := by
    simpa only [MulAut.conj_symm_apply,map_mul,map_inv] using hm
  rw [← pointParabolic_comap F]
  exact hq


/-- The two entire inner-conjugacy classes are disjoint over every finite field. -/
theorem point_line_conjugates_ne (g h:PSL(3,F)) :
    (pointParabolic F).map (MulAut.conj g).toMonoidHom≠
      (lineParabolic F).map (MulAut.conj h).toMonoidHom := by
  intro he
  have hh:=congrArg (fun P:Subgroup PSL(3,F)=>P.map (MulAut.conj h⁻¹).toMonoidHom) he
  rw [map_conj_conj,map_conj_conj,inv_mul_cancel,map_one] at hh
  change (pointParabolic F).map (MulAut.conj (h⁻¹*g)).toMonoidHom=
    (lineParabolic F).map (MonoidHom.id _) at hh
  rw [Subgroup.map_id] at hh
  exact pointParabolic_not_conjugate_line F _ hh

/-- A genuine graph actor, with its arbitrary inner factor, moves the point
parabolic conjugacy class. This includes every odd prime field. -/
theorem not_preservesPointType_inner_graph (g:PSL(3,F)) :
    ¬ PreservesPointType F (MulAut.conj g*graph F) := by
  rintro ⟨h,hh⟩
  obtain ⟨k,hk⟩:=graph_mapsParabolicType F true
  change (pointParabolic F).map (graph F).toMonoidHom=
    (lineParabolic F).map (MulAut.conj k).toMonoidHom at hk
  rw [map_aut_mul,hk,map_conj_conj] at hh
  exact point_line_conjugates_ne F h (g*k) hh.symm
end Matrix.PSL3.LinearThree.OuterExtensions.ParabolicSeparation
