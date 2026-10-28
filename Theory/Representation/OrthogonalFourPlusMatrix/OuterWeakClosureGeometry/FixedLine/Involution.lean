module

public import Theory.Representation.OrthogonalFourPlusMatrix.Binary
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Outer involutions fixing a singular determinant line

A determinant isometry fixing `E01` preserves its polar hyperplane. On the
quotient by that singular line, it either preserves the two isotropic axes
or interchanges them. The matrix-unit calculation shows that an involution
in the first case is an inner pair of upper root elements. In the second
case its displacement is a field line with a nonsingular upper triangular
center. Every commuting determinant isometry fixes that center pointwise:
its scalar on the center has square one, hence is one in characteristic two.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemma 9.4.5, printed pp.736–737. This is the outer-actor reduction after
the singular field line has been shown to be fixed pointwise.
-/

@[expose] public noncomputable section
open Matrix Module
namespace ClassicalOrthogonal.FourPlusMatrix.Binary.OuterWeakClosureGeometry.FixedLine
private def E (i j : Fin 2) : V := Matrix.single i j 1
@[simp] private lemma E_apply (i j k l : Fin 2) :
    E i j k l = if i = k ∧ j = l then 1 else 0 := rfl
private def polar (M N : V) : F :=
  M 0 0 * N 1 1 + M 1 1 * N 0 0 - M 0 1 * N 1 0 - M 1 0 * N 0 1
private lemma polar_preserved (t : V ≃ₗ[F] V) (ht : ∀ M, (t M).det = M.det)
    (M N : V) : polar (t M) (t N) = polar M N := by
  have h := ht (M + N)
  have hM := ht M
  have hN := ht N
  simp only [map_add, det_fin_two, Matrix.add_apply] at h hM hN
  unfold polar
  linear_combination h - hM - hN
private lemma map_matrix (t : V ≃ₗ[F] V) (M : V) :
    t M = M 0 0 • t (E 0 0) + M 0 1 • t (E 0 1) +
      M 1 0 • t (E 1 0) + M 1 1 • t (E 1 1) := by
  have hM : M = M 0 0 • E 0 0 + M 0 1 • E 0 1 +
      M 1 0 • E 1 0 + M 1 1 • E 1 1 := by
    funext i j
    fin_cases i <;> fin_cases j <;> simp [E_apply]
  conv_lhs => rw [hM]
  simp only [map_add, map_smul]

private lemma basic_shape (t : V ≃ₗ[F] V) (ht : ∀ M, (t M).det = M.det)
    (hN : t (E 0 1) = E 0 1) :
    t (E 0 0) 1 0 = 0 ∧ t (E 1 1) 1 0 = 0 ∧ t (E 1 0) 1 0 = 1 ∧
    t (E 0 0) 0 0 * t (E 0 0) 1 1 = 0 ∧
    t (E 1 1) 0 0 * t (E 1 1) 1 1 = 0 ∧
    t (E 0 0) 0 0 * t (E 1 1) 1 1 + t (E 0 0) 1 1 * t (E 1 1) 0 0 = 1 := by
  have hp := polar_preserved t ht
  have ha : t (E 0 0) 1 0 = 0 := by simpa [hN, polar] using hp (E 0 1) (E 0 0)
  have hd : t (E 1 1) 1 0 = 0 := by simpa [hN, polar] using hp (E 0 1) (E 1 1)
  have hc : t (E 1 0) 1 0 = 1 := by simpa [hN, polar] using hp (E 0 1) (E 1 0)
  refine ⟨ha, hd, hc, ?_, ?_, ?_⟩
  · simpa [det_fin_two, ha] using ht (E 0 0)
  · simpa [det_fin_two, hd] using ht (E 1 1)
  · simpa [polar, ha, hd] using hp (E 0 0) (E 1 1)

private lemma nonswapping_shape (t : V ≃ₗ[F] V) (ht : ∀ M, (t M).det = M.det)
    (hN : t (E 0 1) = E 0 1) (ht2 : ∀ M, t (t M) = M)
    (ha11 : t (E 0 0) 1 1 = 0) :
    ∃ x y : F, t (E 0 0) = !![1,y;0,0] ∧ t (E 1 1) = !![0,x;0,1] ∧
      t (E 1 0) = !![x,x*y;1,y] := by
  obtain ⟨ha10,hd10,hc10,_,hdq,had⟩ := basic_shape t ht hN
  have had' : t (E 0 0) 0 0 * t (E 1 1) 1 1 = 1 := by simpa [ha11] using had
  have ha00n : t (E 0 0) 0 0 ≠ 0 := (mul_ne_zero_iff.mp (had'.trans_ne one_ne_zero)).1
  have hd11n : t (E 1 1) 1 1 ≠ 0 := (mul_ne_zero_iff.mp (had'.trans_ne one_ne_zero)).2
  have hd00 : t (E 1 1) 0 0 = 0 := (mul_eq_zero.mp hdq).resolve_right hd11n
  have ha00 : t (E 0 0) 0 0 = 1 := by
    apply CharTwo.sq_injective
    have h := congrArg (fun M : V => M 0 0) (ht2 (E 0 0))
    rw [map_matrix t (t (E 0 0))] at h
    simpa [Matrix.add_apply,Matrix.smul_apply,hN,ha11,ha10,hd00,pow_two] using h
  have hd11 : t (E 1 1) 1 1 = 1 := by simpa [ha00] using had'
  have hp := polar_preserved t ht
  have hc11 : t (E 1 0) 1 1 = t (E 0 0) 0 1 := by
    have h := hp (E 0 0) (E 1 0)
    simpa [polar,ha00,ha11,ha10,hc10,sub_eq_zero] using h
  have hc00 : t (E 1 0) 0 0 = t (E 1 1) 0 1 := by
    have h := hp (E 1 1) (E 1 0)
    simpa [polar,hd00,hd11,hd10,hc10,sub_eq_zero] using h
  have hc01 : t (E 1 0) 0 1 = t (E 1 1) 0 1 * t (E 0 0) 0 1 := by
    have h := ht (E 1 0)
    exact (sub_eq_zero.mp (by simpa [det_fin_two,hc00,hc11,hc10] using h)).symm
  refine ⟨t (E 1 1) 0 1,t (E 0 0) 0 1,?_,?_,?_⟩ <;>
    funext i j <;> fin_cases i <;> fin_cases j <;>
      simp [ha00,ha10,ha11,hd00,hd10,hd11,hc00,hc10,hc11,hc01]

private lemma swapping_shape (t : V ≃ₗ[F] V) (ht : ∀ M, (t M).det = M.det)
    (hN : t (E 0 1) = E 0 1) (ht2 : ∀ M, t (t M) = M)
    (ha00 : t (E 0 0) 0 0 = 0) :
    ∃ q x : F, q ≠ 0 ∧
      t (E 0 0) = !![0,q*x;0,q] ∧ t (E 1 1) = !![q⁻¹,x;0,0] ∧
      t (E 1 0) = !![x,x*(q*x);1,q*x] := by
  obtain ⟨ha10,hd10,hc10,_,hdq,had⟩ := basic_shape t ht hN
  have had' : t (E 0 0) 1 1 * t (E 1 1) 0 0 = 1 := by simpa [ha00] using had
  have ha11n : t (E 0 0) 1 1 ≠ 0 := (mul_ne_zero_iff.mp (had'.trans_ne one_ne_zero)).1
  have hd00n : t (E 1 1) 0 0 ≠ 0 := (mul_ne_zero_iff.mp (had'.trans_ne one_ne_zero)).2
  have hd11 : t (E 1 1) 1 1 = 0 := (mul_eq_zero.mp hdq).resolve_left hd00n
  have hd00 : t (E 1 1) 0 0 = (t (E 0 0) 1 1)⁻¹ := by
    apply mul_left_cancel₀ ha11n
    rw [had',mul_inv_cancel₀ ha11n]
  have hp := polar_preserved t ht
  have ha01 : t (E 0 0) 0 1 = t (E 0 0) 1 1 * t (E 1 0) 0 0 := by
    have h := hp (E 0 0) (E 1 0)
    exact (sub_eq_zero.mp (by simpa [polar,ha00,ha10,hc10] using h)).symm
  have hd01 : t (E 1 1) 0 1 = (t (E 0 0) 1 1)⁻¹ * t (E 1 0) 1 1 := by
    have h := hp (E 1 1) (E 1 0)
    exact (sub_eq_zero.mp (by simpa [polar,hd00,hd10,hd11,hc10] using h)).symm
  have hc11 : t (E 1 0) 1 1 = t (E 0 0) 1 1 * t (E 1 0) 0 0 := by
    have h := congrArg (fun M : V => M 0 1) (ht2 (E 0 0))
    rw [map_matrix t (t (E 0 0))] at h
    have he : t (E 0 0) 1 1 * t (E 1 0) 0 0 + t (E 1 0) 1 1 = 0 := by
      simpa [Matrix.add_apply,Matrix.smul_apply,hN,ha00,ha10,ha01,hd01,
        ← mul_assoc,ha11n] using h
    exact (CharTwo.add_eq_zero.mp he).symm
  have hd01' : t (E 1 1) 0 1 = t (E 1 0) 0 0 := by
    rw [hd01,hc11,←mul_assoc,inv_mul_cancel₀ ha11n,one_mul]
  have hc01 : t (E 1 0) 0 1 = t (E 1 0) 0 0 *
      (t (E 0 0) 1 1 * t (E 1 0) 0 0) := by
    have h := ht (E 1 0)
    exact (sub_eq_zero.mp (by simpa [det_fin_two,hc11,hc10] using h)).symm
  refine ⟨t (E 0 0) 1 1,t (E 1 0) 0 0,ha11n,?_,?_,?_⟩ <;>
    funext i j <;> fin_cases i <;> fin_cases j <;>
      simp [ha00,ha01,ha10,hd00,hd01',hd10,hd11,hc10,hc11,hc01]

private def root (x : F) : SpecialLinearGroup (Fin 2) F :=
  SpecialLinearGroup.transvection zero_ne_one x
private lemma root_inv (x : F) : (root x)⁻¹ = root x := by
  apply inv_eq_of_mul_eq_one_left
  rw [root, ← SpecialLinearGroup.transvection_add, CharTwo.add_self_eq_zero,
    SpecialLinearGroup.transvection_coeff_zero]

private lemma nonswapping_inner (t : V ≃ₗ[F] V) (ht : ∀ M, (t M).det = M.det)
    (hN : t (E 0 1) = E 0 1) (ht2 : ∀ M, t (t M) = M)
    (ha11 : t (E 0 0) 1 1 = 0) : ∃ g : G, t = matrixHom g := by
  obtain ⟨x,y,ha,hd,hc⟩ := nonswapping_shape t ht hN ht2 ha11
  refine ⟨(root x,root y), ?_⟩
  apply LinearEquiv.ext
  intro M
  rw [map_matrix t M,ha,hd,hc,hN]
  change _ = (root x).val * M * (root y)⁻¹.val
  rw [root_inv]
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [root,SpecialLinearGroup.transvection_coe,Matrix.mul_apply,
      Fin.sum_univ_two,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul]
  all_goals ring

/-- An outer involution fixing the singular matrix unit is a field transvection. -/
theorem outer_involution_fixed_unit (t : V ≃ₗ[F] V)
    (ht : ∀ M, (t M).det = M.det) (hN : t (Matrix.single 0 1 1) = Matrix.single 0 1 1)
    (ht2 : ∀ M, t (t M) = M) (houter : ∀ g : G, t ≠ matrixHom g) :
    ∃ q x : F, q ≠ 0 ∧ ∀ M : V,
      t M - M = (q*M 0 0 + M 1 1 + q*x*M 1 0) • !![q⁻¹,x;0,1] := by
  change t (E 0 1) = E 0 1 at hN
  have ha00 : t (E 0 0) 0 0 = 0 := by
    rcases mul_eq_zero.mp (basic_shape t ht hN).2.2.2.1 with h | h
    · exact h
    · obtain ⟨g,hg⟩ := nonswapping_inner t ht hN ht2 h
      exact (houter g hg).elim
  obtain ⟨q,x,hq,ha,hd,hc⟩ := swapping_shape t ht hN ht2 ha00
  refine ⟨q,x,hq,?_⟩
  intro M
  rw [map_matrix t M,ha,hd,hc,hN]
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.add_apply,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,
      sub_eq_add_neg,CharTwo.neg_eq,CharTwo.add_self_eq_zero]
  all_goals field_simp [hq]
  all_goals ring_nf
  all_goals simp only [CharTwo.two_eq_zero, mul_zero, add_zero]


/-- Commutation with an outer involution fixes its nonsingular center pointwise. -/
theorem common_fixed_center_of_outer {H : Type*} [Group H]
    (f : H →* (V ≃ₗ[F] V)) (hdet : ∀ h M, (f h M).det = M.det)
    (hcomm : ∀ a b, f a * f b = f b * f a)
    (hinv : ∀ h M, f h (f h M) = M)
    (hN : ∀ h, f h (Matrix.single 0 1 1) = Matrix.single 0 1 1)
    (t : H) (houter : ∀ g : G, f t ≠ matrixHom g) :
    ∃ u : V, u.det ≠ 0 ∧ u 1 0 = 0 ∧ ∀ h, f h u = u := by
  obtain ⟨q,x,hq,hd⟩ := outer_involution_fixed_unit (f t) (hdet t) (hN t)
    (hinv t) houter
  let u : V := !![q⁻¹,x;0,1]
  have hud : u.det ≠ 0 := by simp [u,det_fin_two,hq]
  have hu : f t (E 1 1) - E 1 1 = u := by simpa using hd (E 1 1)
  refine ⟨u,hud,by simp [u],?_⟩
  intro h
  let c : F := q * f h (E 1 1) 0 0 + f h (E 1 1) 1 1 + q*x*f h (E 1 1) 1 0
  have hcu : f h u = c • u := by
    conv_lhs => rw [←hu,map_sub]
    have hh := LinearEquiv.congr_fun (hcomm h t) (E 1 1)
    change f h (f t (E 1 1)) = f t (f h (E 1 1)) at hh
    rw [hh]
    exact hd (f h (E 1 1))
  have hc : c = 1 := by
    apply CharTwo.sq_injective
    apply mul_right_cancel₀ hud
    have hh := hdet h u
    rw [hcu,Matrix.det_smul] at hh
    simpa using hh
  rw [hcu,hc,one_smul]
end ClassicalOrthogonal.FourPlusMatrix.Binary.OuterWeakClosureGeometry.FixedLine
