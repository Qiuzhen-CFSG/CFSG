module
public import Theory.Representation.HermitianTensorThree.ParabolicTorus.ActorFixed

/-!
# Determinant norm on a pointwise fixed Hermitian plane

Fixing the diagonal rank-one matrices of the Hermitian plane forces the first
two columns of a congruence matrix to be diagonal, with norm-one entries.
The determinant norm therefore measures the norm on the third coordinate.
Raising to the norm-one torus order leaves a unipotent matrix of square one.
Consequently a plane-fixing congruence of order 2^n - 1 has determinant norm
of that same order, and determinant norm one is impossible when n > 1.

This is the matrix calculation needed for the H.4.4(5) argument. It retains
the scalar part of a full binary normalizer; the source ambient argument
must still exclude that part.

Source: Aschbacher–Smith, H.4.4(5), printed p.381, and its use in 8.2.4,
printed p.716 (1 March 2004 manuscript, refs/quasithin.pdf).
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Matrix Subgroup Representation Representation.BinaryOffender
open Representation.HermitianTensorThree Representation.HermitianTensorThree.ImageOuter
open Representation.HermitianTensorThree.ImageOuter.FieldSections
namespace Representation.HermitianTensorThree.ParabolicTorus
variable (n : ℕ) [NeZero n]

private theorem column_of_fixed_diagonal
    (g : GeneralLinearGroup (Fin 3) (E n)) (j : Fin 3)
    (h : binaryCongruence n g (diagonalUnit n j) = diagonalUnit n j) :
    g.val j j * sigma n (g.val j j) = 1 ∧ ∀ i, i ≠ j → g.val i j = 0 := by
  have he (i : Fin 3) : g.val i j * sigma n (g.val i j) = if i = j then 1 else 0 := by
    have hh := congrArg (fun X : Space n => X.val i i) h
    change (g.val * (diagonalUnit n j).val * adjoint n g.val) i i = _ at hh
    simpa [diagonalUnit,Matrix.mul_apply,Matrix.single_apply,adjoint,ite_and,eq_comm] using hh
  refine ⟨by simpa using he j,?_⟩
  intro i hij
  have hz : g.val i j * sigma n (g.val i j) = 0 := by simpa [hij] using he i
  rcases mul_eq_zero.mp hz with h0 | h0
  · exact h0
  · exact (sigma n).injective (h0.trans (map_zero _).symm)

private theorem two_columns_pow {F : Type*} [Field F]
    (g : Matrix (Fin 3) (Fin 3) F)
    (h10 : g 1 0 = 0) (h20 : g 2 0 = 0) (h01 : g 0 1 = 0) (h21 : g 2 1 = 0)
    (m : ℕ) :
    (g^m) 1 0 = 0 ∧ (g^m) 2 0 = 0 ∧ (g^m) 0 1 = 0 ∧ (g^m) 2 1 = 0 ∧
      ∀ i : Fin 3, (g^m) i i = (g i i)^m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ]
    refine ⟨?_,?_,?_,?_,?_⟩
    all_goals simp only [Matrix.mul_apply,Fin.sum_univ_three,h10,h20,h01,h21,
      ih.1,ih.2.1,ih.2.2.1,ih.2.2.2.1,zero_mul,mul_zero,add_zero]
    intro i
    fin_cases i <;> simp [ih.2.2.2.2,pow_succ,h10,h20,h01,h21,ih.1,ih.2.1,ih.2.2.1,ih.2.2.2.1]

/-- A congruence fixing the Hermitian plane pointwise and having determinant
of norm one has order dividing twice the norm-one torus order. -/
theorem plane_fixed_order_dvd_of_det_norm_one
    (g : GeneralLinearGroup (Fin 3) (E n))
    (hfix : ∀ X ∈ fixedSpace (UnipotentRadicals.ambientAction n) (UnipotentRadicals.plane n),
      binaryCongruence n g X = X)
    (hdet : g.val.det * sigma n g.val.det = 1) :
    orderOf (binaryCongruence n g) ∣ 2 * (2^n+1) := by
  have hd (j : Fin 3) (hj : j = 0 ∨ j = 1) :
      binaryCongruence n g (diagonalUnit n j) = diagonalUnit n j := by
    apply hfix
    apply (UnipotentRadicals.mem_plane_fixed_iff n _).mpr
    rcases hj with rfl | rfl <;> simp [diagonalUnit]
  obtain ⟨hn0,hc0⟩ := column_of_fixed_diagonal n g 0 (hd 0 (Or.inl rfl))
  obtain ⟨hn1,hc1⟩ := column_of_fixed_diagonal n g 1 (hd 1 (Or.inr rfl))
  have h10 := hc0 1 (by decide)
  have h20 := hc0 2 (by decide)
  have h01 := hc1 0 (by decide)
  have h21 := hc1 2 (by decide)
  have hdet' : g.val.det = g.val 0 0 * g.val 1 1 * g.val 2 2 := by
    simp [Matrix.det_fin_three,h10,h20,h01,h21]
  have hn2 : g.val 2 2 * sigma n (g.val 2 2) = 1 := by
    rw [hdet',map_mul,map_mul] at hdet
    calc
      _ = (g.val 0 0 * sigma n (g.val 0 0)) *
          (g.val 1 1 * sigma n (g.val 1 1)) * (g.val 2 2 * sigma n (g.val 2 2)) := by
            rw [hn0,hn1,one_mul,one_mul]
      _ = 1 := by convert hdet using 1; ring
  have hp (i : Fin 3) : (g.val i i) ^ (2^n+1) = 1 := by
    have hh : g.val i i * sigma n (g.val i i) = 1 := by
      fin_cases i <;> assumption
    change g.val i i * iterateFrobeniusEquiv (E n) 2 n (g.val i i) = 1 at hh
    rw [iterateFrobeniusEquiv_def] at hh
    simpa only [pow_succ'] using hh
  let q := 2^n+1
  let a := g.val ^ q
  obtain ⟨ha10,ha20,ha01,ha21,hadiag⟩ := two_columns_pow g.val h10 h20 h01 h21 q
  have ha (i : Fin 3) : a i i = 1 := (hadiag i).trans (hp i)
  have hs : a^2 = 1 := by
    rw [pow_two]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply,Fin.sum_univ_three,show a 1 0 = 0 from ha10,
        show a 2 0 = 0 from ha20,show a 0 1 = 0 from ha01,
        show a 2 1 = 0 from ha21,ha,CharTwo.add_self_eq_zero]
  have hg : g^(2*q) = 1 := by
    apply Units.ext
    change g.val ^ (2*q) = 1
    rw [Nat.mul_comm 2 q,pow_mul]
    exact hs
  have hx : binaryCongruence n g ^ (2*q) = 1 := by
    rw [←map_pow,hg,map_one]
  exact orderOf_dvd_of_pow_eq_one hx

/-- The source split-torus order is incompatible with determinant norm one
when it fixes the literal Hermitian plane pointwise and n > 1. -/
theorem plane_no_split_torus_of_det_norm_one
    (g : GeneralLinearGroup (Fin 3) (E n))
    (hfix : ∀ X ∈ fixedSpace (UnipotentRadicals.ambientAction n) (UnipotentRadicals.plane n),
      binaryCongruence n g X = X)
    (hdet : g.val.det * sigma n g.val.det = 1)
    (ho : orderOf (binaryCongruence n g) = 2^n-1) (hn : 1 < n) : False := by
  have hdiv := plane_fixed_order_dvd_of_det_norm_one n g hfix hdet
  rw [ho] at hdiv
  have hodd : Odd (2^n-1) := Nat.Even.sub_odd (Nat.one_le_pow n 2 (by decide))
    (Nat.even_pow.mpr ⟨by decide,by omega⟩) odd_one
  have hd : 2^n-1 ∣ 2^n+1 := hodd.coprime_two_right.dvd_of_dvd_mul_left hdiv
  have hd2 : 2^n-1 ∣ 2 := by
    have hh := Nat.dvd_sub hd (dvd_refl (2^n-1))
    have hh' : (2^n+1)-(2^n-1) = 2 := by have hq := Nat.one_le_pow n 2 (by decide); omega
    rwa [hh'] at hh
  have hbound := Nat.le_of_dvd (by decide : 0 < 2) hd2
  have hq : 4 ≤ 2^n := by
    calc 4 = 2^2 := by decide
         _ ≤ 2^n := Nat.pow_le_pow_right (by decide) (by omega)
  omega

/-- The entire split-torus order survives in the determinant norm. This
retains the information needed for the ambient odd-rank obstruction, rather
than assuming that every odd scalar in a source overgroup is trivial. -/
theorem plane_fixed_det_norm_order
    (g : GeneralLinearGroup (Fin 3) (E n))
    (hfix : ∀ X ∈ fixedSpace (UnipotentRadicals.ambientAction n) (UnipotentRadicals.plane n),
      binaryCongruence n g X = X)
    (ho : orderOf (binaryCongruence n g) = 2^n-1) :
    orderOf (g.val.det * sigma n g.val.det) = 2^n-1 := by
  let a := g.val.det * sigma n g.val.det
  let d := orderOf a
  have hd (j : Fin 3) (hj : j = 0 ∨ j = 1) :
      binaryCongruence n g (diagonalUnit n j) = diagonalUnit n j := by
    apply hfix
    apply (UnipotentRadicals.mem_plane_fixed_iff n _).mpr
    rcases hj with rfl | rfl <;> simp [diagonalUnit]
  obtain ⟨hn0,hc0⟩ := column_of_fixed_diagonal n g 0 (hd 0 (Or.inl rfl))
  obtain ⟨hn1,hc1⟩ := column_of_fixed_diagonal n g 1 (hd 1 (Or.inr rfl))
  have h10 := hc0 1 (by decide)
  have h20 := hc0 2 (by decide)
  have h01 := hc1 0 (by decide)
  have h21 := hc1 2 (by decide)
  have hdet' : g.val.det = g.val 0 0 * g.val 1 1 * g.val 2 2 := by
    simp [Matrix.det_fin_three,h10,h20,h01,h21]
  have hn2 : g.val 2 2 * sigma n (g.val 2 2) = a := by
    dsimp only [a]
    rw [hdet',map_mul,map_mul]
    calc
      _ = (g.val 0 0 * sigma n (g.val 0 0)) *
          (g.val 1 1 * sigma n (g.val 1 1)) * (g.val 2 2 * sigma n (g.val 2 2)) := by
            rw [hn0,hn1,one_mul,one_mul]
      _ = _ := by ring
  have hp (i : Fin 3) : (g.val i i) ^ ((2^n+1)*d) = 1 := by
    have hpow (b : E n) : b^(2^n+1) = b * sigma n b := by
      change b^(2^n+1) = b * iterateFrobeniusEquiv (E n) 2 n b
      rw [iterateFrobeniusEquiv_def,pow_succ']
    rw [pow_mul,hpow]
    fin_cases i
    · change (g.val 0 0 * sigma n (g.val 0 0))^d = 1
      rw [hn0,one_pow]
    · change (g.val 1 1 * sigma n (g.val 1 1))^d = 1
      rw [hn1,one_pow]
    · change (g.val 2 2 * sigma n (g.val 2 2))^d = 1
      rw [hn2]
      exact pow_orderOf_eq_one a
  let q := (2^n+1)*d
  let b := g.val ^ q
  obtain ⟨hb10,hb20,hb01,hb21,hbdiag⟩ := two_columns_pow g.val h10 h20 h01 h21 q
  have hb (i : Fin 3) : b i i = 1 := (hbdiag i).trans (hp i)
  have hs : b^2 = 1 := by
    rw [pow_two]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply,Fin.sum_univ_three,show b 1 0 = 0 from hb10,
        show b 2 0 = 0 from hb20,show b 0 1 = 0 from hb01,
        show b 2 1 = 0 from hb21,hb,CharTwo.add_self_eq_zero]
  have hg : g^(2*q) = 1 := by
    apply Units.ext
    change g.val ^ (2*q) = 1
    rw [Nat.mul_comm 2 q,pow_mul]
    exact hs
  have hx : binaryCongruence n g ^ (2*q) = 1 := by rw [←map_pow,hg,map_one]
  have hdiv : 2^n-1 ∣ 2*((2^n+1)*d) := by
    rw [←ho]
    exact orderOf_dvd_of_pow_eq_one hx
  have hodd : Odd (2^n-1) := Nat.Even.sub_odd (Nat.one_le_pow n 2 (by decide))
    (Nat.even_pow.mpr ⟨by decide,NeZero.ne n⟩) odd_one
  have hcop : Nat.Coprime (2^n-1) (2^n+1) := by
    apply Nat.coprime_iff_gcd_eq_one.mpr
    have hd1 := Nat.gcd_dvd_left (2^n-1) (2^n+1)
    have hd2 := Nat.gcd_dvd_right (2^n-1) (2^n+1)
    have htwo : Nat.gcd (2^n-1) (2^n+1) ∣ 2 := by
      have hh := Nat.dvd_sub hd2 hd1
      have hh' : (2^n+1)-(2^n-1) = 2 := by
        have hq := Nat.one_le_pow n 2 (by decide)
        omega
      rwa [hh'] at hh
    exact Nat.eq_one_of_dvd_coprimes hodd.coprime_two_right hd1 htwo
  have hl : 2^n-1 ∣ d := hcop.dvd_of_dvd_mul_left
    (hodd.coprime_two_right.dvd_of_dvd_mul_left hdiv)
  have ha : sigma n a = a := by
    change sigma n (g.val.det * sigma n g.val.det) = g.val.det * sigma n g.val.det
    rw [map_mul,sigma_involutive,mul_comm]
  let aF : F n := ⟨a,ha⟩
  have ha0 : aF ≠ 0 := by
    intro he
    have hh : a = 0 := congrArg Subtype.val he
    exact mul_ne_zero g.det_ne_zero (fun hz => g.det_ne_zero ((sigma n).injective (hz.trans (map_zero _).symm))) hh
  have hpow : a^(2^n-1) = 1 := by
    let := Fintype.ofFinite (F n)
    have hh := FiniteField.pow_card_sub_one_eq_one aF ha0
    rw [←Nat.card_eq_fintype_card,card_F] at hh
    exact congrArg Subtype.val hh
  exact Nat.dvd_antisymm (orderOf_dvd_of_pow_eq_one hpow) hl

end Representation.HermitianTensorThree.ParabolicTorus
