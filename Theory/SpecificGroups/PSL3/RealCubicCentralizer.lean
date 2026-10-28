module
public import Theory.SpecificGroups.PSL3.EvenLocalNormalizers.AllFields
public import Theory.SpecificGroups.PSL3.EvenInnerCentralizers.Decomposition

/-!
# Real cubic elements in characteristic-two PSL₃

The repeated diagonal entry in a transvection centralizer detects the scalar
ambiguity in projective conjugacy. Reality forces its fourth power to be a
cube root, while projective order three forces its ninth power to be one.
Thus its cube is one and its projective image is unipotent, hence trivial.
This is the intrinsic cubic obstruction for a deleted-five block in PSL₃.
Source application: Aschbacher–Smith, 2.4.25, printed pp.542–543.
-/

public section
open Subgroup Matrix
open scoped MatrixGroups
namespace Matrix.PSL3.EvenInnerCentralizers.RealCubic
open Matrix.PSL3Even.UnipotentGeometry
variable {F : Type*} [Field F] [CharP F 2]

private theorem trace_eq (x : centralizerSL F) :
    Matrix.trace x.val.val = ((diagonalHom F x : F)⁻¹)^2 := by
  rw [centralizerSL_factorization F x]
  change Matrix.trace (Matrix.diagonal _ * matrix F _) = _
  simp [Matrix.trace, Fin.sum_univ_three, Matrix.diagonal_mul, matrix, add_comm]
  rw [←add_assoc,CharTwo.add_self_eq_zero,zero_add]

omit [CharP F 2] in
private theorem diagonal_central (x : centralizerSL F) (hx : x.val ∈ center SL(3,F)) :
    (diagonalHom F x)^3 = 1 := by
  obtain ⟨r,_,hr⟩ := SpecialLinearGroup.mem_center_iff.mp hx
  have h11 := congrArg (fun A : Matrix (Fin 3) (Fin 3) F => A 1 1) hr
  have h00 := congrArg (fun A : Matrix (Fin 3) (Fin 3) F => A 0 0) hr
  have hd := centralizerSL_diagonal_product F x
  have he : x.val.val 1 1 = x.val.val 0 0 := h11.symm.trans h00
  apply Units.ext
  change x.val.val 0 0 ^ 3 = 1
  rw [he] at hd
  simpa only [pow_succ, pow_zero, one_mul] using hd

omit [CharP F 2] in
private theorem trace_projectively_conjugate (x y : SL(3,F))
    (h : IsConj (projection F x) (projection F y)) :
    ∃ r : F, r ^ 3 = 1 ∧ Matrix.trace x.val = r * Matrix.trace y.val := by
  obtain ⟨g,hg⟩ := isConj_iff.mp h
  obtain ⟨s,rfl⟩ := projection_surjective F g
  have hp : projection F (s*x*s⁻¹) = projection F y := by
    simpa only [map_mul,map_inv] using hg
  have hc := (projection F).eq_iff.mp hp
  rw [projection_ker] at hc
  obtain ⟨r,_,hr⟩ := SpecialLinearGroup.mem_center_iff.mp hc
  have he : (s*x*s⁻¹).val = r • y.val := by
    calc
      (s*x*s⁻¹).val = (y*(y⁻¹*(s*x*s⁻¹))).val := by simp only [mul_inv_cancel_left]
      _ = y.val * Matrix.scalar (Fin 3) r := by rw [SpecialLinearGroup.coe_mul,←hr]
      _ = r • y.val := by ext i j; simp [Matrix.scalar,Matrix.mul_diagonal,mul_comm]
  have hr3 : r^3 = 1 := by
    have hd : (Matrix.scalar (Fin 3) r).det = 1 := hr ▸ (y⁻¹*(s*x*s⁻¹)).property
    simpa [Matrix.scalar, Matrix.det_diagonal, Fin.prod_univ_three, pow_succ] using hd
  refine ⟨r,hr3,?_⟩
  have ht : Matrix.trace (s*x*s⁻¹).val = Matrix.trace x.val := by
    change Matrix.trace (s.val*x.val*s⁻¹.val) = _
    rw [Matrix.trace_mul_cycle]
    have hi : s⁻¹.val*s.val=1 := congrArg Subtype.val (inv_mul_cancel s)
    rw [hi,one_mul]
  rw [he,Matrix.trace_smul,smul_eq_mul] at ht
  exact ht.symm

/-- A real cube root of one in the marked root centralizer is trivial. -/
theorem eq_one_of_root_centralizer (x : centralizerSL F)
    (hx3 : projection F x.val ^ 3 = 1)
    (hreal : IsConj (projection F x.val) (projection F x.val)⁻¹) :
    projection F x.val = 1 := by
  let a := diagonalHom F x
  have hc : (x^3).val ∈ center SL(3,F) := by
    rw [←projection_ker]
    change projection F (x.val^3)=1
    rw [map_pow,hx3]
  have ha9 : a^9=1 := by
    have h := diagonal_central (x^3) hc
    simpa only [map_pow,←pow_mul] using h
  obtain ⟨r,hr3,ht⟩ := trace_projectively_conjugate x.val x.val⁻¹ (by simpa only [map_inv] using hreal)
  have ht' : ((a:F)⁻¹)^2 = r*(a:F)^2 := by
    change Matrix.trace x.val.val = r*Matrix.trace (x⁻¹).val.val at ht
    rw [trace_eq,trace_eq,map_inv,Units.val_inv_eq_inv_val,inv_inv] at ht
    exact ht
  have ha12 : (a:F)^12=1 := by
    have hh := congrArg (fun z:F => z^3) ht'
    rw [mul_pow,hr3,one_mul] at hh
    have hn : (a:F)≠0 := a.ne_zero
    field_simp at hh
    exact hh.symm
  have ha3 : a^3=1 := by
    apply Units.ext
    have ha9' : (a:F)^9=1 := congrArg (fun z:Fˣ => (z:F)) ha9
    change (a:F)^3=1
    calc
      (a:F)^3 = (a:F)^9*(a:F)^3 := by rw [ha9',one_mul]
      _ = (a:F)^12 := by rw [←pow_add]
      _ = 1 := ha12
  let u := unipotentPart F x
  have hx : projection F x.val = projective F u := by
    rw [centralizerSL_factorization F x,map_mul]
    have ht0 := congrArg Subtype.val ((torus_eq_one_iff F a).mpr ha3)
    change projection F (torusSL F a)=1 at ht0
    rw [ht0,one_mul]
    rfl
  have hu3 : u^3=1 := by
    apply projective_injective F
    rw [map_pow,←hx,hx3,map_one]
  have hu4 : u^4=1 := by
    apply U.ext <;> simp only [pow_succ,pow_zero,mul_x,mul_y,mul_c,one_x,one_y,one_c,
      zero_add,zero_mul,add_zero,CharTwo.add_self_eq_zero]
    calc
      u.x*u.y + u.c + u.c + u.x*u.y = (u.x*u.y+u.x*u.y)+(u.c+u.c) := by ring
      _ = 0 := by rw [CharTwo.add_self_eq_zero,CharTwo.add_self_eq_zero,add_zero]
  rw [hx]
  have hu : u=1 := by
    calc u = u^3*u := by rw [hu3,one_mul]
         _ = u^4 := (pow_succ u 3).symm
         _ = 1 := hu4
  rw [hu,map_one]

/-- A real projective cube root cannot centralize a nonidentity involution. -/
theorem eq_one_of_centralizes_involution [Finite F] {n : ℕ}
    (hn : 0<n) (hF : Nat.card F=2^n) (x t : PSL(3,F))
    (hx3 : x^3=1) (hreal : IsConj x x⁻¹)
    (ht : t≠1) (ht2 : t^2=1) (hxt : Commute x t) : x=1 := by
  obtain ⟨g,hg⟩ := isConj_iff.mp (involution_isConj_root_of_positive F hn hF t ht ht2)
  let e := MulAut.conj g
  have he : e t = root F := hg
  have hxC : e x ∈ centralizer F := by
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    change e x * root F = root F * e x
    rw [←he,←map_mul,←map_mul,hxt.eq]
  obtain ⟨s,hs,hsx⟩ := (centralizer_map F).ge hxC
  have hs3 : projection F s^3=1 := by rw [hsx,←map_pow,hx3,map_one]
  have hsr : IsConj (projection F s) (projection F s)⁻¹ := by
    rw [hsx,←map_inv]
    exact e.toMonoidHom.map_isConj hreal
  have hh := eq_one_of_root_centralizer ⟨s,hs⟩ hs3 hsr
  apply e.injective
  rw [←hsx,hh,map_one]

end Matrix.PSL3.EvenInnerCentralizers.RealCubic
