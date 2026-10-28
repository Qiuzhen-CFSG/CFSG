module
public import Theory.Representation.OrthogonalFourPlusMatrix.SmallActors
public import Theory.Representation.OrthogonalFourPlusMatrix.InvolutionResidual.Defs
public import Theory.Representation.OrthogonalFourPlusMatrix.OuterWeakClosureGeometry.FixedLine.Canonical
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Rank-two involutions move the marked tensor factor

A binary rank-two element of the determinant-action normalizer is linear
over the coefficient field and has field displacement rank one. An
involution therefore preserves the determinant. Its displacement line is
nonsingular; left multiplication by its center makes that line scalar.
The canonical determinant calculation then identifies the normalized actor
with adjugation.

Invertible left multiplication normalizes the marked first special linear
factor, while adjugation sends a nonidentity first-factor root to the second
factor. Consequently the original rank-two involution cannot normalize the
first factor. This keeps the actual operator and its rank, including after
inner conjugation in the point-Sylow application.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
9.1.2(4) and the nonsingular-point Sylow passage in 9.4, printed pp.729,734–736.
-/

public noncomputable section
open Matrix Module Subgroup
namespace ClassicalOrthogonal.FourPlusMatrix.Binary
namespace RankTwoFactorSwap
open InvolutionResidual
open OuterWeakClosureGeometry.FixedLine.Canonical

private theorem scalar_displacement_eq_swap (s : V ≃ₗ[F] V)
    (hdet : ∀ M, (s M).det = M.det) (hne : s ≠ 1)
    (hline : ∀ M : V, ∃ c : F, s M = M + c • (1 : V)) : s = swap := by
  have hI : s (1 : V) = 1 := by
    obtain ⟨c,hc⟩ := hline 1
    have hs : (1+c)^2 = (1:F)^2 := by
      simpa [hc,Matrix.det_fin_two,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,pow_two]
        using hdet 1
    have hc0 : c = 0 := add_left_cancel ((CharTwo.sq_injective hs).trans (add_zero 1).symm)
    simpa [hc0] using hc
  have hN : s N = N := by
    obtain ⟨c,hc⟩ := hline N
    have hs : c^2 = (0:F)^2 := by
      have hh := hdet N
      rw [hc] at hh
      simpa [N,E,Matrix.det_fin_two,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,pow_two]
        using hh
    have hc0 : c = 0 := CharTwo.sq_injective hs
    simpa [hc0] using hc
  obtain ⟨ha,hD,hC⟩ := diagonal_shape s hdet hI hN
  have hb : s (E 1 0) 0 0 = 0 := by
    obtain ⟨c,hc⟩ := hline (E 1 1)
    have hh := congrArg (fun M : V => M 0 1) hc
    rw [hD] at hh
    simpa using hh
  have ha1 : s (E 1 1) 0 0 = 1 := by
    rcases ha with ha | ha
    · exfalso
      apply hne
      apply LinearEquiv.ext
      intro M
      rw [matrix_formula_of_shape s _ _ hI hN hD hC,ha,hb]
      funext i j
      fin_cases i <;> fin_cases j <;> simp
    · exact ha
  apply LinearEquiv.ext
  intro M
  rw [matrix_formula_of_shape s _ _ hI hN hD hC,ha1,hb,swap_apply]
  funext i j
  fin_cases i <;> fin_cases j <;> simp
  all_goals ring_nf
  all_goals simp only [CharTwo.two_eq_zero,mul_zero,zero_add]

private theorem rank_one_conjugate_swap (s : V ≃ₗ[F] V)
    (hdet : ∀ M, (s M).det = M.det)
    (hr : finrank F (LinearMap.range (s.toLinearMap - LinearMap.id)) ≤ 1)
    (hne : s ≠ 1) :
    ∃ u : Vˣ, s = (u.mulLeftLinearEquiv F V) * swap * (u.mulLeftLinearEquiv F V)⁻¹ := by
  obtain ⟨f,d,he⟩ := LinearEquiv.mem_dilatransvections_iff_finrank.mpr hr
  have hform (M : V) : s M = M + f M • d :=
    congrArg (fun l : V →ₗ[F] V => l M) he
  have hd : d ≠ 0 := by
    intro hd
    apply hne
    apply LinearEquiv.ext
    intro M
    simpa [hd] using hform M
  obtain ⟨y,hy⟩ : ∃ y, f y ≠ 0 := by
    by_contra! hh
    apply hne
    apply LinearEquiv.ext
    intro M
    simpa [hh M] using hform M
  let z : V := (f y)⁻¹ • y
  have hz : f z = 1 := by simp [z,hy]
  have hdmem : d ∈ LinearMap.range (s.toLinearMap - LinearMap.id) := by
    refine ⟨z,?_⟩
    change s z-z=d
    rw [hform,hz,one_smul,add_sub_cancel_left]
  have hdd : d.det ≠ 0 := by
    intro hdd
    exact QuadraticForm.singular_not_mem_displacement determinantForm
      determinant_polar_separating s (by simpa only [determinantForm_apply] using hdet)
      hr d hd (by simpa only [determinantForm_apply] using hdd) hdmem
  let u : Vˣ := Matrix.nonsingInvUnit d (isUnit_iff_ne_zero.mpr hdd)
  let p : V ≃ₗ[F] V := u.mulLeftLinearEquiv F V
  have hp (M : V) : p M = d*M := rfl
  have hp1 : p 1 = d := by rw [hp,mul_one]
  have hpd : p.symm d = 1 := by rw [←hp1,p.symm_apply_apply]
  let q : V ≃ₗ[F] V := (MulAut.conj p.symm) s
  have hq (M : V) : q M = p.symm (s (p M)) := rfl
  have hqd (M : V) : (q M).det = M.det := by
    apply mul_left_cancel₀ hdd
    calc
      d.det * (q M).det = (p (q M)).det := by rw [hp,Matrix.det_mul]
      _ = (s (p M)).det := by rw [hq,p.apply_symm_apply]
      _ = (p M).det := hdet _
      _ = d.det * M.det := by rw [hp,Matrix.det_mul]
  have hqne : q ≠ 1 := by
    intro h
    apply hne
    apply (MulAut.conj p.symm).injective
    exact h.trans (map_one _).symm
  have hql (M : V) : ∃ c : F, q M = M+c • (1:V) := by
    refine ⟨f (p M),?_⟩
    rw [hq,hform,map_add,map_smul,p.symm_apply_apply,hpd]
  have hqs : q = swap := scalar_displacement_eq_swap q hqd hqne hql
  refine ⟨u,?_⟩
  change s = p*swap*p⁻¹
  have heq : p⁻¹*s*p=swap := hqs
  calc
    s = p*(p⁻¹*s*p)*p⁻¹ := by group
    _ = p*swap*p⁻¹ := by rw [heq]


private def leftMulBinary (u : Vˣ) : V ≃ₗ[ZMod 2] V :=
  (u.mulLeftLinearEquiv F V).restrictScalars (ZMod 2)

private theorem leftMul_preserves_left (u : Vˣ)
    (x : V ≃ₗ[ZMod 2] V) (hx : x ∈ leftFactor) :
    leftMulBinary u * x * (leftMulBinary u)⁻¹ ∈ leftFactor := by
  obtain ⟨a,rfl⟩ := hx
  have huu : (u : V) * (u⁻¹ : Vˣ) = 1 := u.val_inv
  let b : SL := ⟨(u : V) * a.val * (u⁻¹ : Vˣ), by
    rw [Matrix.det_mul,Matrix.det_mul,a.det_coe,mul_one,←Matrix.det_mul,huu,Matrix.det_one]⟩
  refine ⟨b,?_⟩
  apply LinearEquiv.ext
  intro M
  change b.val * M * (1:SL)⁻¹.val =
    (u : V) * (a.val * ((u⁻¹ : Vˣ) * M) * (1:SL)⁻¹.val)
  simp only [inv_one,SpecialLinearGroup.coe_one,mul_one]
  dsimp only [b]
  simp only [mul_assoc]

private theorem leftMul_normalizes_left (u : Vˣ) :
    leftMulBinary u ∈ normalizer (leftFactor : Set (V ≃ₗ[ZMod 2] V)) := by
  rw [mem_normalizer_iff]
  intro x
  constructor
  · exact leftMul_preserves_left u x
  · intro hx
    have hh := leftMul_preserves_left u⁻¹ _ hx
    have hi : leftMulBinary u⁻¹ = (leftMulBinary u)⁻¹ := rfl
    rw [hi] at hh
    have he : (leftMulBinary u)⁻¹ * (leftMulBinary u * x * (leftMulBinary u)⁻¹) *
        ((leftMulBinary u)⁻¹)⁻¹ = x := by group
    rwa [he] at hh

private def root : SL := SpecialLinearGroup.transvection zero_ne_one (1 : F)
private theorem root_inv : root⁻¹ = root := by
  apply inv_eq_of_mul_eq_one_left
  rw [root,←SpecialLinearGroup.transvection_add,CharTwo.add_self_eq_zero,
    SpecialLinearGroup.transvection_coeff_zero]
private theorem root_ne_one : root ≠ 1 := by
  intro h
  have hh := congrArg (fun a : SL => a.val 0 1) h
  simp [root,SpecialLinearGroup.transvection_coe] at hh

private def swapBinary : V ≃ₗ[ZMod 2] V := swap.restrictScalars (ZMod 2)

private theorem swap_conjugate_root :
    swapBinary * linearAction (root,1) * swapBinary⁻¹ = linearAction (1,root) := by
  apply LinearEquiv.ext
  intro M
  change swap (root.val * swap M * (1:SL)⁻¹.val) = (1:SL).val * M * root⁻¹.val
  simp only [inv_one,SpecialLinearGroup.coe_one,mul_one,one_mul,root_inv]
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [swap_apply,root,SpecialLinearGroup.transvection_coe,Matrix.mul_apply,
      Fin.sum_univ_two,add_comm]

private theorem swap_not_normalize_left :
    swapBinary ∉ normalizer (leftFactor : Set (V ≃ₗ[ZMod 2] V)) := by
  intro h
  have hm := (mem_normalizer_iff.mp h (linearAction (root,1))).mp
    (show linearAction (root,1) ∈ leftFactor from ⟨root,rfl⟩)
  rw [swap_conjugate_root] at hm
  obtain ⟨a,ha⟩ := hm
  have he : (a,1) = (1,root) :=
    action_injective (congrArg LinearEquiv.toLinearMap ha)
  exact root_ne_one (congrArg Prod.snd he).symm

end RankTwoFactorSwap

/-- A binary rank-two normalizer involution cannot preserve the marked first factor. -/
theorem rank_two_involution_not_normalize_leftFactor
    (t : V ≃ₗ[ZMod 2] V)
    (ht : t ∈ normalizer (linearAction.range : Set (V ≃ₗ[ZMod 2] V)))
    (ht2 : t ^ 2 = 1)
    (hr : finrank (ZMod 2) (LinearMap.range (t.toLinearMap - LinearMap.id)) = 2) :
    t ∉ normalizer (InvolutionResidual.leftFactor : Set (V ≃ₗ[ZMod 2] V)) := by
  have htne : t ≠ 1 := by
    intro h
    rw [h] at hr
    change finrank (ZMod 2) (LinearMap.range (LinearMap.id - LinearMap.id : Module.End (ZMod 2) V)) = 2 at hr
    rw [sub_self,LinearMap.range_zero,finrank_bot] at hr
    omega
  obtain ⟨s,hs,hsr,_⟩ := low_rank_nonidentity t ht hr.le htne
  have hs2 (M : V) : s (s M) = M := by
    have hh := LinearEquiv.congr_fun ht2 M
    change t (t M) = M at hh
    simpa only [←hs,LinearEquiv.restrictScalars_apply] using hh
  have hsd := field_involution_preserves_det s (by rwa [hs]) hs2
  have hsne : s ≠ 1 := by
    intro h
    apply htne
    rw [←hs,h]
    rfl
  obtain ⟨u,hu⟩ := RankTwoFactorSwap.rank_one_conjugate_swap s hsd hsr.le hsne
  let p := RankTwoFactorSwap.leftMulBinary u
  have he : t = p * RankTwoFactorSwap.swapBinary * p⁻¹ := by
    rw [←hs]
    apply LinearEquiv.ext
    intro M
    exact LinearEquiv.congr_fun hu M
  intro hnorm
  have hp := RankTwoFactorSwap.leftMul_normalizes_left u
  have hh := (normalizer (InvolutionResidual.leftFactor : Set (V ≃ₗ[ZMod 2] V))).mul_mem
    ((normalizer _).mul_mem ((normalizer _).inv_mem hp) hnorm) hp
  change p⁻¹ * t * p ∈ normalizer (InvolutionResidual.leftFactor : Set (V ≃ₗ[ZMod 2] V)) at hh
  rw [he] at hh
  have heq : p⁻¹ * (p * RankTwoFactorSwap.swapBinary * p⁻¹) * p =
      RankTwoFactorSwap.swapBinary := by group
  rw [heq] at hh
  exact RankTwoFactorSwap.swap_not_normalize_left hh

end ClassicalOrthogonal.FourPlusMatrix.Binary
