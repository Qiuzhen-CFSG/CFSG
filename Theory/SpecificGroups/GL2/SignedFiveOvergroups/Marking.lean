module
public import Theory.SpecificGroups.GL2.SignedFiveOvergroups
public import Theory.SpecificGroups.GL2.NoncommutativeCentralizer
public import Theory.LinearAlgebra.MatrixTwoCyclicIntertwiner
public import Mathlib.GroupTheory.SpecificGroups.Dihedral

/-!
# Signed coordinates for faithful dihedral-eight subgroups of GL₂(5)

The central square of a faithful rotation is scalar, since the image is
noncommutative. It is the scalar -I. A noncentral reflection has trace zero
and determinant -1, so the two-dimensional cyclic-intertwiner theorem
conjugates it to diag(-1,1). Anticommutation then makes the rotation
antidiagonal. A diagonal change of basis normalizes its off-diagonal
entries, placing both generators in the signed permutation subgroup.
The common order eight proves equality.

This marks the actual original Sylow image in the residual-normalizer
argument of Aschbacher--Smith 14.6.15, printed p.1034. The source consumer
is OddNormalizer.Quintic.ModuleGeometry.ResidualSigned.
-/

public section
open Subgroup Matrix
open scoped IsMulCommutative
namespace Matrix.GeneralLinearGroup.SignedFive
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
private theorem involution_trace_det (A : Matrix (Fin 2) (Fin 2) F)
    (hn : ¬ ∃ a : F, A = a • 1) (hh : A*A=1) : trace A=0 ∧ Matrix.det A = -1 := by
  have h00 := congrArg (fun B : Matrix (Fin 2) (Fin 2) F => B 0 0) hh
  have h01 := congrArg (fun B : Matrix (Fin 2) (Fin 2) F => B 0 1) hh
  have h10 := congrArg (fun B : Matrix (Fin 2) (Fin 2) F => B 1 0) hh
  have h11 := congrArg (fun B : Matrix (Fin 2) (Fin 2) F => B 1 1) hh
  simp [Matrix.mul_apply,Fin.sum_univ_two] at h00 h01 h10 h11
  have ht : A 0 0 + A 1 1 = 0 := by
    by_contra ht
    have hb : A 0 1 = 0 := (mul_eq_zero.mp (show A 0 1*(A 0 0+A 1 1)=0 by
      linear_combination h01)).resolve_right ht
    have hc : A 1 0 = 0 := (mul_eq_zero.mp (show A 1 0*(A 0 0+A 1 1)=0 by
      linear_combination h10)).resolve_right ht
    have hd : A 0 0 = A 1 1 := sub_eq_zero.mp ((mul_eq_zero.mp
      (show (A 0 0-A 1 1)*(A 0 0+A 1 1)=0 by linear_combination h00-h11)).resolve_right ht)
    apply hn
    refine ⟨A 0 0,?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hb,hc,hd]
  refine ⟨by simpa only [trace_fin_two] using ht,?_⟩
  rw [Matrix.det_fin_two]
  linear_combination -h00 + A 0 0 * ht

private theorem reflection_nonscalar :
    ¬ ∃ a : F, (diagonalPair F (-1,1)).val = a • 1 := by
  rintro ⟨a,ha⟩
  have h0 := congrArg (fun B : Matrix (Fin 2) (Fin 2) F => B 0 0) ha
  have h1 := congrArg (fun B : Matrix (Fin 2) (Fin 2) F => B 1 1) ha
  simp [diagonalPair_val] at h0 h1
  exact (by decide : (-1:F) ≠ 1) (h0.trans h1.symm)

private theorem conjugate_reflection (t : L) (ht : t^2=1)
    (hn : ¬ ∃ a : F, t.val=a•1) :
    ∃ g : L, g⁻¹*t*g = diagonalPair F (-1,1) := by
  have hsq : t.val*t.val=1 := congrArg Units.val (by simpa only [pow_two] using ht)
  obtain ⟨htr,hdet⟩ := involution_trace_det t.val hn hsq
  let d : L := diagonalPair F (-1,1)
  have htd : trace t.val=trace d.val := by
    rw [htr]
    norm_num [d,diagonalPair_val,trace_fin_two]
  have hdd : Matrix.det t.val=Matrix.det d.val := by
    rw [hdet]
    norm_num [d,diagonalPair_val,Matrix.det_fin_two]
  obtain ⟨P,hP,hcomm⟩ := exists_intertwiner_of_trace_eq_det_eq t.val d.val hn
    reflection_nonscalar htd hdd
  let g := mkOfDetNeZero P hP
  have he : t*g=g*d := Units.ext hcomm
  exact ⟨g,by rw [mul_assoc,he,inv_mul_cancel_left]⟩

/-- Every faithful dihedral-eight subgroup of GL₂(5) is conjugate to the
actual signed permutation matrices. -/
theorem exists_signed_conjugation_of_dihedral (φ : DihedralGroup 4 →* L)
    (hφ : Function.Injective φ) :
    ∃ g : L, φ.range.map (MulAut.conj g).toMonoidHom = signedSubgroup := by
  let r := φ (DihedralGroup.r 1)
  let t := φ (DihedralGroup.sr 0)
  have ht : t^2=1 := by
    change φ (DihedralGroup.sr 0)^2=1
    rw [←map_pow,show (DihedralGroup.sr 0 : DihedralGroup 4)^2=1 by decide,map_one]
  have hnr : t*r ≠ r*t := by
    intro he
    have hh : (DihedralGroup.sr 0 : DihedralGroup 4)*DihedralGroup.r 1 =
        DihedralGroup.r 1*DihedralGroup.sr 0 := hφ (by
      simpa only [map_mul] using he)
    exact (by decide : (DihedralGroup.sr 0 : DihedralGroup 4)*DihedralGroup.r 1 ≠
      DihedralGroup.r 1*DihedralGroup.sr 0) hh
  have hn : ¬ IsMulCommutative φ.range := by
    intro h
    let := h
    apply hnr
    exact congrArg Subtype.val (mul_comm
      (⟨t,⟨DihedralGroup.sr 0,rfl⟩⟩ : φ.range) ⟨r,⟨DihedralGroup.r 1,rfl⟩⟩)
  have hr2 : r^2 = -1 := by
    have hc : r^2 ∈ centralizer (φ.range : Set L) := by
      rintro y ⟨y,rfl⟩
      change φ y * φ (DihedralGroup.r 1)^2 = φ (DihedralGroup.r 1)^2 * φ y
      rw [←map_pow,←map_mul,←map_mul]
      apply congrArg φ
      exact (by decide : ∀ y : DihedralGroup 4,
        y*DihedralGroup.r 1^2=DihedralGroup.r 1^2*y) y
    obtain ⟨u,hu⟩ := centralizer_le_scalar_of_noncommutative φ.range hn hc
    have h4 : (r^2)^2=1 := by
      change (φ (DihedralGroup.r 1)^2)^2=1
      rw [←map_pow,←map_pow,show ((DihedralGroup.r 1 : DihedralGroup 4)^2)^2=1 by decide,map_one]
    have hu2 : (u:F)^2=1 := by
      have hh : GeneralLinearGroup.scalar (Fin 2) (u^2) = 1 := by
        rw [map_pow,hu]
        exact h4
      exact congrArg (fun A : L => A.val 0 0) hh
    rcases sq_eq_one_iff.mp hu2 with h1 | hm
    · have he : u=1 := Units.ext h1
      rw [he,map_one] at hu
      have hh : (DihedralGroup.r 1 : DihedralGroup 4)^2=1 := hφ (by
        rw [map_pow,map_one]
        exact hu.symm)
      exact (by decide : (DihedralGroup.r 1 : DihedralGroup 4)^2 ≠ 1) hh |>.elim
    · rw [←hu]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hm]
  have htns : ¬∃ a:F,t.val=a•1 := by
    rintro ⟨a,ha⟩
    apply hnr
    apply Units.ext
    change t.val*r.val=r.val*t.val
    rw [ha]
    simp
  obtain ⟨g,hg⟩ := conjugate_reflection t ht htns
  let ψ := (MulAut.conj g⁻¹).toMonoidHom.comp φ
  let r' := ψ (DihedralGroup.r 1)
  have ht' : ψ (DihedralGroup.sr 0) = diagonalPair F (-1,1) := by
    change g⁻¹*t*(g⁻¹)⁻¹ = _
    simpa only [inv_inv] using hg
  have hr' : r'^2 = -1 := by
    change (g⁻¹*r*(g⁻¹)⁻¹)^2 = -1
    rw [←MulAut.conj_apply,←map_pow,hr2]
    change g⁻¹ * (-1) * (g⁻¹)⁻¹ = -1
    simp
  have htr : diagonalPair F (-1,1)*r' = -r'*diagonalPair F (-1,1) := by
    have hgroup : ψ (DihedralGroup.sr 0)*ψ (DihedralGroup.r 1) =
        ψ (DihedralGroup.r 1)^3*ψ (DihedralGroup.sr 0) := by
      rw [←map_pow,←map_mul,←map_mul]
      congr 1
    rw [ht'] at hgroup
    change diagonalPair F (-1,1)*r' = r'^3*diagonalPair F (-1,1) at hgroup
    simpa only [show (3:ℕ)=2+1 by rfl,pow_succ,hr',neg_one_mul] using hgroup
  have hdiag : r'.val 0 0=0 ∧ r'.val 1 1=0 := by
    have h0 := congrArg (fun A:L => A.val 0 0) htr
    have h1 := congrArg (fun A:L => A.val 1 1) htr
    simp [diagonalPair_val,Matrix.mul_apply,Fin.sum_univ_two] at h0 h1
    constructor
    · have hh : (2:F)*r'.val 0 0=0 := by linear_combination -h0
      exact (mul_eq_zero.mp hh).resolve_left (by decide)
    · have hh : (2:F)*r'.val 1 1=0 := by linear_combination h1
      exact (mul_eq_zero.mp hh).resolve_left (by decide)
  have hprod : r'.val 0 1 * r'.val 1 0 = -1 := by
    have hh := congrArg (fun A:L => A.val 0 0) hr'
    simpa [pow_two,Matrix.mul_apply,Fin.sum_univ_two,hdiag.1] using hh
  have hb : r'.val 0 1 ≠ 0 := by intro hh; rw [hh,zero_mul] at hprod; norm_num at hprod
  let b : Fˣ := Units.mk0 (r'.val 0 1) hb
  let d : L := diagonalPair F (b,1)
  have hdi : d⁻¹ = diagonalPair F (b⁻¹,1) := by
    change (diagonalPair F (b,1))⁻¹ = _
    rw [←map_inv]
    rfl
  let χ := (MulAut.conj d⁻¹).toMonoidHom.comp ψ
  have hrχ : χ (DihedralGroup.r 1) = diagonalPair F (1,-1)*coordinateSwap F := by
    change d⁻¹*r'* (d⁻¹)⁻¹ = _
    rw [inv_inv,hdi]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [d,b,diagonalPair_val,coordinateSwap_val,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two,
        hdiag.1,hdiag.2,hb,hprod,mul_comm]
  have htχ : χ (DihedralGroup.sr 0) = diagonalPair F (-1,1) := by
    change d⁻¹*ψ (DihedralGroup.sr 0)*(d⁻¹)⁻¹ = _
    rw [ht',inv_inv,hdi]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [d,b,diagonalPair_val,Matrix.mul_apply,Fin.sum_univ_two,hb]
  have hle : χ.range ≤ signedSubgroup := by
    rintro z ⟨z,rfl⟩
    have hrm : χ (DihedralGroup.r 1) ∈ signedSubgroup := by
      rw [hrχ]
      exact signedSubgroup.mul_mem (subset_closure (by simp)) (subset_closure (by simp))
    have htm : χ (DihedralGroup.sr 0) ∈ signedSubgroup := by
      rw [htχ]
      exact subset_closure (by simp)
    cases z with
    | r i =>
      have he : (DihedralGroup.r i : DihedralGroup 4) = DihedralGroup.r 1 ^ i.val := by
        fin_cases i <;> decide
      rw [he,map_pow]
      exact signedSubgroup.pow_mem hrm _
    | sr i =>
      have he : (DihedralGroup.sr i : DihedralGroup 4) = DihedralGroup.sr 0 * DihedralGroup.r 1 ^ i.val := by
        fin_cases i <;> decide
      rw [he,map_mul,map_pow]
      exact signedSubgroup.mul_mem htm (signedSubgroup.pow_mem hrm _)
  have hinj : Function.Injective χ := (MulAut.conj d⁻¹).injective.comp
    ((MulAut.conj g⁻¹).injective.comp hφ)
  have he : χ.range=signedSubgroup := eq_of_le_of_card_ge hle (by
    rw [←Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv,DihedralGroup.nat_card]
    change Nat.card (diagonalSwapSubgroup F (-1)) ≤ 8
    rw [diagonalSwapSubgroup_card]
    have ho : orderOf (-1 : Fˣ)=2 := orderOf_eq_prime (p := 2) (by decide) (by decide)
    norm_num [ho])
  refine ⟨d⁻¹*g⁻¹,?_⟩
  rw [←he]
  ext z
  constructor
  · rintro ⟨x,⟨y,rfl⟩,rfl⟩
    refine ⟨y,?_⟩
    change d⁻¹*(g⁻¹*φ y*(g⁻¹)⁻¹)*(d⁻¹)⁻¹ =
      (d⁻¹*g⁻¹)*φ y*(d⁻¹*g⁻¹)⁻¹
    group
  · rintro ⟨y,rfl⟩
    refine ⟨φ y,⟨y,rfl⟩,?_⟩
    change (d⁻¹*g⁻¹)*φ y*(d⁻¹*g⁻¹)⁻¹ = d⁻¹*(g⁻¹*φ y*(g⁻¹)⁻¹)*(d⁻¹)⁻¹
    group
end Matrix.GeneralLinearGroup.SignedFive
