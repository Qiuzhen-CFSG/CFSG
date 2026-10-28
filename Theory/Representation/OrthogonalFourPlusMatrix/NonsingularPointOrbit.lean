module
public import Theory.Representation.OrthogonalFourPlusMatrix.NonsingularPoint
public import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
/-!
# Additive generation by a singular vector in a nonsingular point stabilizer

Over a finite field of characteristic two, the diagonal SL₂ orbit of a
nonzero singular trace-zero matrix generates the complete trace-zero space
as an additive group. An upper transvection reduces the seed to a matrix
unit; diagonal matrices produce all its field multiples because squaring is
surjective. Opposite matrix units and one transvection then supply every
scalar diagonal. Right multiplication transports this additive argument to
the literal stabilizer of an arbitrary nonsingular matrix.

Source application: Aschbacher--Smith 9.1.2(4) and9.4.1, printed pp.729,735.
-/

@[expose] public noncomputable section
set_option linter.unusedSimpArgs false
open Matrix ClassicalOrthogonal.FourPlusMatrix
namespace ClassicalOrthogonal.FourPlusMatrix.PointOrbit
variable {F : Type*} [Field F] [CharP F 2]
private def upper (t : F) : SpecialLinearGroup (Fin 2) F :=
  ⟨!![1,t;0,1], by simp [det_fin_two]⟩
private theorem upper_inv (t : F) : (upper t)⁻¹ = upper t := by
  apply inv_eq_of_mul_eq_one_left
  apply Subtype.ext
  change !![1,t;0,1] * !![1,t;0,1] = (1 : Mat (F := F))
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [upper, mul_apply, Fin.sum_univ_two, CharTwo.add_self_eq_zero]
private theorem upper_action (t : F) (M : Mat (F := F)) :
    matrixAction (upper t,upper t) M =
      !![M 0 0 + t*M 1 0, M 0 1 + t*(M 0 0+M 1 1) + t^2*M 1 0;
      M 1 0, M 1 1 + t*M 1 0] := by
  change (upper t).val*M*(upper t)⁻¹.val = _
  rw [upper_inv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [upper,mul_apply,vecMul,dotProduct,Fin.sum_univ_two] <;> ring
private def swap : SpecialLinearGroup (Fin 2) F :=
  ⟨!![0,1;1,0],by simp [det_fin_two,CharTwo.neg_eq]⟩
private theorem swap_inv : (swap (F := F))⁻¹ = swap := by
  apply inv_eq_of_mul_eq_one_left
  apply Subtype.ext
  change !![0,1;1,0] * !![0,1;1,0] = (1 : Mat (F := F))
  ext i j
  fin_cases i <;> fin_cases j <;> simp [swap,mul_apply,vecMul,dotProduct,Fin.sum_univ_two]
private theorem swap_action (M : Mat (F := F)) :
    matrixAction (swap,swap) M = !![M 1 1,M 1 0;M 0 1,M 0 0] := by
  change (swap (F := F)).val*M*swap⁻¹.val = _
  rw [swap_inv]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [swap,mul_apply,vecMul,dotProduct,Fin.sum_univ_two]

private theorem exists_upper_mem (W : AddSubgroup (Mat (F := F)))
    (hW : ∀ g : SpecialLinearGroup (Fin 2) F, ∀ M ∈ W, matrixAction (g,g) M ∈ W)
    (z : Mat (F := F)) (hz : z ∈ W) (hz0 : z ≠ 0)
    (hzd : z.det = 0) (hzt : z 0 0 = z 1 1) :
    ∃ c : F, c ≠ 0 ∧ !![0,c;0,0] ∈ W := by
  by_cases hc : z 1 0 = 0
  · have ha : z 0 0 = 0 := by
      have h : z 0 0 ^ 2 = 0 := by simpa [det_fin_two,←hzt,hc,pow_two] using hzd
      exact (pow_eq_zero_iff (by decide : 2 ≠ 0)).mp h
    have hd : z 1 1 = 0 := hzt.symm.trans ha
    have hb : z 0 1 ≠ 0 := by
      intro hb
      apply hz0
      ext i j
      fin_cases i <;> fin_cases j <;> simp [ha,hb,hc,hd]
    refine ⟨z 0 1,hb,?_⟩
    convert hz using 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ha,hc,hd]
  · let t := z 0 0 / z 1 0
    let w := matrixAction (upper t,upper t) z
    have hw : w ∈ W := hW _ z hz
    have hw00 : w 0 0 = 0 := by
      simp [w,upper_action,t,div_mul_cancel₀ _ hc,CharTwo.add_self_eq_zero]
    have hw11 : w 1 1 = 0 := by
      simp [w,upper_action,t,div_mul_cancel₀ _ hc,←hzt,CharTwo.add_self_eq_zero]
    have hw10 : w 1 0 = z 1 0 := by simp [w,upper_action]
    have hw01 : w 0 1 = 0 := by
      have hd := (matrixAction_det (upper t,upper t) z).trans hzd
      change w.det = 0 at hd
      rw [det_fin_two,hw00,hw11,hw10,zero_mul,zero_sub,neg_eq_zero] at hd
      exact (mul_eq_zero.mp hd).resolve_right hc
    refine ⟨z 1 0,hc,?_⟩
    have hh := hW swap w hw
    rw [swap_action] at hh
    simpa [hw00,hw11,hw10,hw01] using hh

variable [Finite F]

private theorem all_upper_mem (W : AddSubgroup (Mat (F := F)))
    (hW : ∀ g : SpecialLinearGroup (Fin 2) F, ∀ M ∈ W, matrixAction (g,g) M ∈ W)
    (c : F) (hc : c ≠ 0) (hcW : !![0,c;0,0] ∈ W) (b : F) :
    !![0,b;0,0] ∈ W := by
  by_cases hb : b = 0
  · subst b
    convert W.zero_mem using 1
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  obtain ⟨t,ht⟩ := (Finite.surjective_of_injective (f := fun t : F => t^2)
    CharTwo.sq_injective) (b/c)
  change t^2 = b/c at ht
  have ht0 : t ≠ 0 := by
    intro he
    have he0 : (0:F)^2 = b/c := he ▸ ht
    exact (div_ne_zero hb hc) (by simpa using he0.symm)
  let g : SpecialLinearGroup (Fin 2) F :=
    ⟨!![t,0;0,t⁻¹],by simp [det_fin_two,ht0]⟩
  have hi : g⁻¹.val = !![t⁻¹,0;0,t] := by
    let h : SpecialLinearGroup (Fin 2) F :=
      ⟨!![t⁻¹,0;0,t],by simp [det_fin_two,ht0]⟩
    have hh : h*g = 1 := by
      apply Subtype.ext
      change !![t⁻¹,0;0,t]*!![t,0;0,t⁻¹] = (1 : Mat (F := F))
      ext i j
      fin_cases i <;> fin_cases j <;> simp [ht0]
    exact congrArg (fun a : SpecialLinearGroup (Fin 2) F => a.val)
      (show g⁻¹ = h from inv_eq_of_mul_eq_one_left hh)
  have he : matrixAction (g,g) !![0,c;0,0] = !![0,b;0,0] := by
    change g.val*!![0,c;0,0]*g⁻¹.val = _
    rw [hi]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [g]
    calc
      t*c*t = t^2*c := by ring
      _ = b := by rw [ht,div_mul_cancel₀ _ hc]
  exact he ▸ hW g _ hcW

/-- The additive orbit of any nonzero singular trace-zero matrix contains
all trace-zero matrices. The span here is additive, not a field span. -/
theorem traceZero_mem_of_singular (W : AddSubgroup (Mat (F := F)))
    (hW : ∀ g : SpecialLinearGroup (Fin 2) F, ∀ M ∈ W, matrixAction (g,g) M ∈ W)
    (z : Mat (F := F)) (hz : z ∈ W) (hz0 : z ≠ 0)
    (hzd : z.det = 0) (hzt : z 0 0 = z 1 1)
    (M : Mat (F := F)) (hM : M 0 0 = M 1 1) : M ∈ W := by
  obtain ⟨c,hc,hcW⟩ := exists_upper_mem W hW z hz hz0 hzd hzt
  have hu (b : F) : !![0,b;0,0] ∈ W := all_upper_mem W hW c hc hcW b
  have hl (b : F) : !![0,0;b,0] ∈ W := by
    have h := hW swap _ (hu b)
    rw [swap_action] at h
    exact h
  have hd (a : F) : !![a,0;0,a] ∈ W := by
    have he : !![a,0;0,a] = matrixAction (upper 1,upper 1) !![0,0;a,0] -
        !![0,a;0,0] - !![0,0;a,0] := by
      rw [upper_action]
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    rw [he]
    exact W.sub_mem (W.sub_mem (hW (upper 1) _ (hl a)) (hu a)) (hl a)
  have he : M = !![M 0 0,0;0,M 0 0] + !![0,M 0 1;0,0] + !![0,0;M 1 0,0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hM]
  rw [he]
  exact W.add_mem (W.add_mem (hd _) (hu _)) (hl _)

omit [CharP F 2] [Finite F] in
/-- Right multiplication by a nonsingular fixed matrix intertwines diagonal
conjugation with its literal left-right stabilizer. -/
theorem point_action_mul (v : Mat (F := F)) (g : pointStabilizer v)
    (M : Mat (F := F)) :
    matrixAction g.val (M*v) = matrixAction (g.val.1,g.val.1) M * v := by
  have hfix := (mem_pointStabilizer g.val v).mp g.property
  change g.val.1.val*v*g.val.2⁻¹.val = v at hfix
  have hrel : v*g.val.2⁻¹.val = g.val.1⁻¹.val*v := by
    have hh := congrArg (fun P : Mat (F := F) => g.val.1⁻¹.val*P) hfix
    simpa only [←mul_assoc,←SpecialLinearGroup.coe_mul,inv_mul_cancel,
      SpecialLinearGroup.coe_one,one_mul] using hh
  change g.val.1.val*(M*v)*g.val.2⁻¹.val = (g.val.1.val*M*g.val.1⁻¹.val)*v
  simp only [mul_assoc]
  rw [hrel]

/-- The hyperplane perpendicular to a nonsingular matrix, in literal coordinates. -/
def pointHyperplane (v : Mat (F := F)) : Submodule F (Mat (F := F)) :=
  LinearMap.ker ((Matrix.traceLinearMap (Fin 2) F F).comp (LinearMap.mulRight F v⁻¹))

omit [CharP F 2] [Finite F] in
theorem mem_pointHyperplane (v M : Mat (F := F)) :
    M ∈ pointHyperplane v ↔ (M*v⁻¹).trace = 0 := Iff.rfl

omit [Finite F] in
private theorem trace_zero_iff (M : Mat (F := F)) :
    M.trace = 0 ↔ M 0 0 = M 1 1 := by
  simp [Matrix.trace,Fin.sum_univ_two,CharTwo.add_eq_zero]

omit [CharP F 2] [Finite F] in
/-- Every stabilizer displacement belongs to the perpendicular hyperplane. -/
theorem point_displacement_mem (v : Mat (F := F)) (hv : v.det ≠ 0)
    (g : pointStabilizer v) (M : Mat (F := F)) :
    matrixAction g.val M - M ∈ pointHyperplane v := by
  have hi : v⁻¹*v = 1 := Matrix.nonsing_inv_mul v (isUnit_iff_ne_zero.mpr hv)
  have hi' : v*v⁻¹ = 1 := Matrix.mul_nonsing_inv v (isUnit_iff_ne_zero.mpr hv)
  have he := point_action_mul v g (M*v⁻¹)
  rw [mul_assoc,hi,mul_one] at he
  rw [mem_pointHyperplane,sub_mul,he,mul_assoc,hi',mul_one,Matrix.trace_sub]
  apply sub_eq_zero.mpr
  change (g.val.1.val*(M*v⁻¹)*g.val.1⁻¹.val).trace = (M*v⁻¹).trace
  rw [Matrix.trace_mul_cycle,←mul_assoc,←SpecialLinearGroup.coe_mul,
    inv_mul_cancel,SpecialLinearGroup.coe_one,one_mul]

/-- A nonzero singular vector in the perpendicular hyperplane additively
generates that entire hyperplane under the literal point stabilizer. -/
theorem pointHyperplane_le_of_singular (v : Mat (F := F)) (hv : v.det ≠ 0)
    (W : AddSubgroup (Mat (F := F)))
    (hW : ∀ g : pointStabilizer v, ∀ M ∈ W, matrixAction g.val M ∈ W)
    (z : Mat (F := F)) (hz : z ∈ W) (hz0 : z ≠ 0)
    (hzd : z.det = 0) (hzt : z ∈ pointHyperplane v) :
    (pointHyperplane v).toAddSubgroup ≤ W := by
  have hi : v⁻¹*v = 1 := Matrix.nonsing_inv_mul v (isUnit_iff_ne_zero.mpr hv)
  let W' := W.comap (LinearMap.mulRight F v).toAddMonoidHom
  have hW' (a : SpecialLinearGroup (Fin 2) F) (M : Mat (F := F)) (hM : M ∈ W') :
      matrixAction (a,a) M ∈ W' := by
    obtain ⟨g,hg⟩ := (pointProjection_bijective v hv).2 a
    change g.val.1 = a at hg
    change matrixAction (a,a) M*v ∈ W
    rw [←hg,←point_action_mul]
    exact hW g (M*v) hM
  have hz' : z*v⁻¹ ∈ W' := by
    change (z*v⁻¹)*v ∈ W
    rwa [mul_assoc,hi,mul_one]
  have hz0' : z*v⁻¹ ≠ 0 := by
    intro he
    apply hz0
    have hh := congrArg (fun M : Mat (F := F) => M*v) he
    simpa only [mul_assoc,hi,mul_one,zero_mul] using hh
  have hzd' : (z*v⁻¹).det = 0 := by rw [Matrix.det_mul,hzd,zero_mul]
  have hzt' : (z*v⁻¹) 0 0 = (z*v⁻¹) 1 1 :=
    (trace_zero_iff _).mp hzt
  intro M hM
  have hh := traceZero_mem_of_singular W' hW' (z*v⁻¹) hz' hz0' hzd' hzt'
    (M*v⁻¹) ((trace_zero_iff _).mp hM)
  change (M*v⁻¹)*v ∈ W at hh
  simpa only [mul_assoc,hi,mul_one] using hh

end ClassicalOrthogonal.FourPlusMatrix.PointOrbit
