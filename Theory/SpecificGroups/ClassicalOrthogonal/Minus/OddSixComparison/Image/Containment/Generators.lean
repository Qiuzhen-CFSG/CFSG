module
public import Theory.SpecificGroups.ClassicalOrthogonal.Minus.OddSixComparison.FieldModel
public import Mathlib.GroupTheory.IsPerfect

/-!
# Derived generators for odd special unitary four-space

For the antidiagonal Hermitian form, the plane Levi is the signed block
matrix diag(A, D σ(A) D), where D = diag(1,-1). The plane radical consists
of upper unipotents with off-diagonal block [[z,b],[c,-σ(z)]], where b and c
are skew under σ. These signs retain the literal odd-characteristic form.

The Levi lies in the derived subgroup because SL₂ over the quadratic
extension is perfect. A primitive extension-field scalar moves both root
characters, so every radical element is an explicit torus commutator.
Both arguments include fixed-field order three. Consequently the normal
closure of these two concrete families is contained in the derived subgroup.
Normal generation of the full SU₄ remains an independent input.

Source: GLS3 §2.7, classical unitary conventions; the twisted A₃/D₃
comparison used by Aschbacher–Smith A.2.17, printed pp.38–39.
-/

@[expose] public noncomputable section
namespace ClassicalOrthogonal.Minus.OddSixComparison.Image.Containment
open Matrix BenderSuzuki.MatrixGroups
open scoped commutatorElement
open Theory.SpecificGroups.ClassicalUnitary UnitaryFourFlag
variable (E : Type*) [Field E] (σ : E ≃+* E) (hσ : Function.Involutive σ)

def leviMatrix (A : SpecialLinearGroup (Fin 2) E) : Matrix (Fin 4) (Fin 4) E :=
  !![A 0 0,A 0 1,0,0; A 1 0,A 1 1,0,0;
     0,0,σ (A 0 0),-σ (A 0 1); 0,0,-σ (A 1 0),σ (A 1 1)]

theorem leviMatrix_one : leviMatrix E σ 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [leviMatrix]

theorem leviMatrix_mul (A B : SpecialLinearGroup (Fin 2) E) :
    leviMatrix E σ (A * B) = leviMatrix E σ A * leviMatrix E σ B := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [leviMatrix, SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_succ]
  all_goals ring

theorem leviMatrix_det (A : SpecialLinearGroup (Fin 2) E) :
    (leviMatrix E σ A).det = 1 := by
  have hd : A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using A.property
  calc
    (leviMatrix E σ A).det =
        (A 0 0 * A 1 1 - A 0 1 * A 1 0) *
          σ (A 0 0 * A 1 1 - A 0 1 * A 1 0) := by
      rw [Matrix.det_succ_row_zero]
      simp [leviMatrix, Fin.sum_univ_succ, Matrix.det_fin_three, Fin.succAbove]
      ring
    _ = 1 := by rw [hd, map_one, mul_one]

theorem leviMatrix_unitary (A : SpecialLinearGroup (Fin 2) E) :
    (form E σ hσ).conjTranspose (leviMatrix E σ A) * gram E *
      leviMatrix E σ A = gram E := by
  have hd : A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using A.property
  have hdc : σ (A 0 0) * σ (A 1 1) - σ (A 0 1) * σ (A 1 0) = 1 := by
    simpa only [map_sub, map_mul, map_one] using congrArg σ hd
  have hs (x : E) : σ (σ x) = x := hσ x
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [form, gram, leviMatrix, HermitianForm.conjTranspose,
      Matrix.mul_apply, Fin.sum_univ_succ, hs]
  all_goals first | linear_combination hd | linear_combination hdc | ring

def levi : SpecialLinearGroup (Fin 2) E →* (form E σ hσ).specialSubgroup where
  toFun A := ⟨GeneralLinearGroup.mkOfDetNeZero (leviMatrix E σ A)
    (by rw [leviMatrix_det]; exact one_ne_zero),
    leviMatrix_unitary E σ hσ A, Units.ext (leviMatrix_det E σ A)⟩
  map_one' := by
    apply Subtype.ext
    apply Units.ext
    exact leviMatrix_one E σ
  map_mul' A B := by
    apply Subtype.ext
    apply Units.ext
    exact leviMatrix_mul E σ A B

@[simp] theorem levi_val (A : SpecialLinearGroup (Fin 2) E) :
    (levi E σ hσ A).val.val = leviMatrix E σ A := rfl

variable {p n : ℕ} [Fact p.Prime] [NeZero n]

theorem extension_has_power_nontrivial {k : ℕ} (hk : k ≠ 0)
    (hbound : k < (p ^ n) ^ 2 - 1) :
    ∃ a : Extension p n, a ≠ 0 ∧ a ^ k ≠ 1 := by
  have hcard : Nat.card (Extension p n)ˣ = (p ^ n) ^ 2 - 1 := by
    rw [Nat.card_units, card_extension]
  obtain ⟨a, ha⟩ := exists_pow_ne_one_of_isCyclic (G := (Extension p n)ˣ) hk
    (hcard ▸ hbound)
  exact ⟨a, Units.ne_zero a, fun h => ha (Units.ext (by simpa using h))⟩

theorem fixed_card_ge_three (hp : p ≠ 2) : 3 ≤ p ^ n := by
  have hprime : p.Prime := Fact.out
  have hp3 : 3 ≤ p := by have := hprime.two_le; omega
  have h := Nat.pow_le_pow_right (n := p) (by omega) (show 1 ≤ n by have := NeZero.ne n; omega)
  exact le_trans hp3 (by simpa using h)

theorem extension_sl2_isPerfect (hp : p ≠ 2) :
    Group.IsPerfect (SpecialLinearGroup (Fin 2) (Extension p n)) := by
  have hq := fixed_card_ge_three (n := n) hp
  have hq2 : 9 ≤ (p ^ n) ^ 2 := by nlinarith
  obtain ⟨a, ha, ha2⟩ := extension_has_power_nontrivial (p := p) (n := n)
    (k := 2) (by decide) (by omega)
  exact ⟨Matrix.SL2.commutator_eq_top ha ha2⟩

theorem levi_mem_commutator (hp : p ≠ 2)
    (A : SpecialLinearGroup (Fin 2) (Extension p n)) :
    levi (Extension p n) (conjugation p n) (conjugation_involutive p n) A ∈
      commutator (unitaryForm p n).specialSubgroup := by
  let := extension_sl2_isPerfect (n := n) hp
  have hm := map_derivedSeries_le_derivedSeries
    (levi (Extension p n) (conjugation p n) (conjugation_involutive p n)) 1
  rw [derivedSeries_one, derivedSeries_one, Group.IsPerfect.commutator_eq_top] at hm
  exact hm ⟨A, Subgroup.mem_top _, rfl⟩

section Upper
variable (E : Type*) [Field E] (σ : E ≃+* E) (hσ : Function.Involutive σ)

/-- The abelian radical of the isotropic plane stabilizer, with odd signs. -/
def upperMatrix (z b c : E) : Matrix (Fin 4) (Fin 4) E :=
  !![1,0,z,b; 0,1,c,-σ z; 0,0,1,0; 0,0,0,1]

theorem upperMatrix_det (z b c : E) : (upperMatrix E σ z b c).det = 1 := by
  rw [Matrix.det_of_isUpperTriangular]
  · simp [upperMatrix, Fin.prod_univ_succ]
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [upperMatrix]

theorem upperMatrix_unitary (z b c : E) (hb : σ b = -b) (hc : σ c = -c) :
    (form E σ hσ).conjTranspose (upperMatrix E σ z b c) * gram E *
      upperMatrix E σ z b c = gram E := by
  have hs (x : E) : σ (σ x) = x := hσ x
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [form, gram, upperMatrix, HermitianForm.conjTranspose,
      Matrix.mul_apply, Fin.sum_univ_succ, hs, hb, hc]

def upper (z b c : E) (hb : σ b = -b) (hc : σ c = -c) :
    (form E σ hσ).specialSubgroup :=
  ⟨GeneralLinearGroup.mkOfDetNeZero (upperMatrix E σ z b c)
    (by rw [upperMatrix_det]; exact one_ne_zero),
    upperMatrix_unitary E σ hσ z b c hb hc, Units.ext (upperMatrix_det E σ z b c)⟩

@[simp] theorem upper_val (z b c : E) (hb : σ b = -b) (hc : σ c = -c) :
    (upper E σ hσ z b c hb hc).val.val = upperMatrix E σ z b c := rfl

/-- Conjugation by an extension-field torus moves every radical coordinate.
The two eigenvalue restrictions are compatible even when the fixed field has
three elements. -/
theorem upper_mem_commutator_of_torus (a : E) (ha : a ≠ 0)
    (hr : a / σ a ≠ 1) (hn : a * σ a ≠ 1)
    (z b c : E) (hb : σ b = -b) (hc : σ c = -c) :
    upper E σ hσ z b c hb hc ∈ commutator (form E σ hσ).specialSubgroup := by
  have hs (x : E) : σ (σ x) = x := hσ x
  have hsa : σ a ≠ 0 := by simpa using ha
  have hn0 : a * σ a ≠ 0 := mul_ne_zero ha hsa
  have hd0 : a * σ a - 1 ≠ 0 := sub_ne_zero.mpr hn
  have he0 : (a * σ a)⁻¹ - 1 ≠ 0 := sub_ne_zero.mpr (inv_ne_one.mpr hn)
  have hf0 : a / σ a - 1 ≠ 0 := sub_ne_zero.mpr hr
  have hf1 : a - σ a ≠ 0 := sub_ne_zero.mpr (fun he => hr ((div_eq_one_iff_eq hsa).mpr he))
  have hf2 : σ a - a ≠ 0 := sub_ne_zero.mpr (fun he => hf1 (sub_eq_zero.mpr he.symm))
  have hden : σ (a * σ a - 1) = a * σ a - 1 := by simp [hs, mul_comm]
  have hden' : σ ((a * σ a)⁻¹ - 1) = (a * σ a)⁻¹ - 1 := by
    simp [hs, mul_comm]
  have hbb : σ (b / (a * σ a - 1)) = -(b / (a * σ a - 1)) := by
    rw [map_div₀, hb, hden, neg_div]
  have hcc : σ (c / ((a * σ a)⁻¹ - 1)) = -(c / ((a * σ a)⁻¹ - 1)) := by
    rw [map_div₀, hc, hden', neg_div]
  let t := levi E σ hσ (SpecialLinearGroup.diag2 a ha)
  let u := upper E σ hσ (z / (a / σ a - 1))
    (b / (a * σ a - 1)) (c / ((a * σ a)⁻¹ - 1)) hbb hcc
  let v := upper E σ hσ z b c hb hc
  have hrel : t * u = v * u * t := by
    apply Subtype.ext
    apply Units.ext
    change leviMatrix E σ (SpecialLinearGroup.diag2 a ha) *
      upperMatrix E σ (z / (a / σ a - 1))
        (b / (a * σ a - 1)) (c / ((a * σ a)⁻¹ - 1)) =
      upperMatrix E σ z b c * upperMatrix E σ (z / (a / σ a - 1))
        (b / (a * σ a - 1)) (c / ((a * σ a)⁻¹ - 1)) *
        leviMatrix E σ (SpecialLinearGroup.diag2 a ha)
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [leviMatrix, upperMatrix, SpecialLinearGroup.diag2_coe',
        Matrix.mul_apply, Fin.sum_univ_succ, hs]
    all_goals field_simp [ha, hsa, hd0, he0, hf0, hf1, hf2]
    all_goals ring
  have hcomm : ⁅t, u⁆ = v := by
    rw [commutatorElement_def, hrel]
    simp [mul_assoc]
  change v ∈ _
  rw [← hcomm]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top t) (Subgroup.mem_top u)
end Upper


section FiniteField
variable {p n : ℕ} [Fact p.Prime] [NeZero n]

/-- A primitive extension-field scalar moves both the short and long roots. -/
theorem exists_moving_torus (hp : p ≠ 2) :
    ∃ a : Extension p n, a ≠ 0 ∧
      a / conjugation p n a ≠ 1 ∧ a * conjugation p n a ≠ 1 := by
  have hq : 3 ≤ p ^ n := fixed_card_ge_three hp
  obtain ⟨a, ha⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := (Extension p n)ˣ)
  have hcard : Nat.card (Extension p n)ˣ = (p ^ n) ^ 2 - 1 := by
    rw [Nat.card_units, card_extension]
  have hpow (k : ℕ) (hk : k ≠ 0) (hkq : k < (p ^ n) ^ 2 - 1) :
      (a : Extension p n) ^ k ≠ 1 := by
    intro h
    have he : a ^ k = 1 := Units.ext (by simpa using h)
    have ho := orderOf_le_of_pow_eq_one (Nat.pos_of_ne_zero hk) he
    rw [ha, hcard] at ho
    omega
  have hq2 : p ^ n + 2 < (p ^ n) ^ 2 := by nlinarith
  have hshort : (a : Extension p n) ^ (p ^ n - 1) ≠ 1 :=
    hpow _ (by omega) (by omega)
  have hlong : (a : Extension p n) ^ (p ^ n + 1) ≠ 1 :=
    hpow _ (by omega) (by omega)
  refine ⟨a, Units.ne_zero a, ?_, ?_⟩
  · intro he
    have he' : (a : Extension p n) = (a : Extension p n) ^ (p ^ n) := by
      apply (div_eq_one_iff_eq (by simp)).mp at he
      exact he
    apply hshort
    apply mul_right_cancel₀ (Units.ne_zero a)
    rw [one_mul, ← pow_succ, Nat.sub_add_cancel (by omega)]
    exact he'.symm
  · simpa only [conjugation, iterateFrobeniusEquiv_def, pow_succ, mul_comm] using hlong

theorem upper_mem_commutator (hp : p ≠ 2) (z b c : Extension p n)
    (hb : conjugation p n b = -b) (hc : conjugation p n c = -c) :
    upper (Extension p n) (conjugation p n) (conjugation_involutive p n) z b c hb hc ∈
      commutator (unitaryForm p n).specialSubgroup := by
  obtain ⟨a, ha, hr, hn⟩ := exists_moving_torus (n := n) hp
  exact upper_mem_commutator_of_torus _ _ _ a ha hr hn z b c hb hc
end FiniteField


section NormalGeneration
variable (p n : ℕ) [Fact p.Prime] [NeZero n]

/-- The concrete plane Levi and the entire signed plane radical. -/
def elementaryGenerators : Set (unitaryForm p n).specialSubgroup :=
  Set.range (levi (Extension p n) (conjugation p n) (conjugation_involutive p n)) ∪
    {g | ∃ (z b c : Extension p n) (hb : conjugation p n b = -b)
      (hc : conjugation p n c = -c),
      upper (Extension p n) (conjugation p n) (conjugation_involutive p n) z b c hb hc = g}

/-- Normal closure in the actual special unitary matrix group. -/
def elementaryNormal : Subgroup (unitaryForm p n).specialSubgroup :=
  Subgroup.normalClosure (elementaryGenerators p n)

instance elementaryNormal_normal : (elementaryNormal p n).Normal :=
  Subgroup.normalClosure_normal

/-- Every element in this concrete normal closure is already derived. -/
theorem elementaryNormal_le_commutator (hp : p ≠ 2) :
    elementaryNormal p n ≤ commutator (unitaryForm p n).specialSubgroup := by
  apply Subgroup.normalClosure_le_normal
  rintro _ (⟨A, rfl⟩ | ⟨z, b, c, hb, hc, rfl⟩)
  · exact levi_mem_commutator hp A
  · exact upper_mem_commutator hp z b c hb hc

/-- The remaining independent input is generation, rather than perfectness of
a fixed-field rank-one subgroup (which would fail at q = 3). -/
theorem su_isPerfect_of_normal_generation (hp : p ≠ 2)
    (hgen : elementaryNormal p n = ⊤) :
    Group.IsPerfect (unitaryForm p n).specialSubgroup := by
  refine ⟨top_unique ?_⟩
  rw [← hgen]
  exact elementaryNormal_le_commutator p n hp
end NormalGeneration

end ClassicalOrthogonal.Minus.OddSixComparison.Image.Containment
