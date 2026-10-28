module

public import Theory.SpecificGroups.SU3.OddPrimeSylowAutomorphisms.GraphComparison
public import Mathlib.FieldTheory.Finite.Basic

/-!
# The order of the split ternary special orthogonal group

The carrier is exactly `(splitOrthogonalForm F).specialSubgroup`, with Gram
matrix `!![0, 0, 1; 0, 1, 0; 1, 0, 0]`. Over a field with `2 ≠ 0`, we construct
a bijection from `(Fˣ × F) ⊕ (F × Fˣ × F)` onto this group. The two forms are
`torus a * upper t` and `upper s * weyl * torus a * upper t`.

The first column is nonzero and isotropic. Its last coordinate determines the
two cases, and its other coordinates determine the chosen representative.
Multiplying by the inverse representative leaves an element fixing the first
basis vector. The orthogonal equations and determinant one force this element
to be a unique `upper t`. Counting the two forms gives `q * (q² - 1)`.
This counts the full special orthogonal group, including both cosets of its
index-two elementary subgroup in odd characteristic.

This direct matrix calculation supplies the orthogonal order input for the
unitary graph-automorphism case of Aschbacher–Smith, *The Classification of
Quasithin Groups*, F.6.18(10)–(11), printed pp.309–310, as used in 15.4.18,
printed pp.1162–1163. It uses the carrier published in `GraphComparison`.
-/

open Matrix
namespace BenderSuzuki.MatrixGroups.HermitianForm.OddPrimeSylow
variable {F : Type*} [Field F]

private abbrev SO (F : Type*) [Field F] := (splitOrthogonalForm F).specialSubgroup
private abbrev gram : Matrix (Fin 3) (Fin 3) F := !![0, 0, 1; 0, 1, 0; 1, 0, 0]
private theorem orth (A : SO F) : A.val.val.transpose * gram * A.val.val = gram := by
  exact ((splitOrthogonalForm F).mem_specialSubgroup_iff _).mp A.property |>.1
private theorem det_one (A : SO F) : A.val.val.det = 1 := by
  exact congrArg Units.val (((splitOrthogonalForm F).mem_specialSubgroup_iff _).mp A.property).2
private def mkSO (M : Matrix (Fin 3) (Fin 3) F) (ho : M.transpose * gram * M = gram)
    (hd : M.det = 1) : SO F :=
  ⟨GeneralLinearGroup.mkOfDetNeZero M (hd ▸ one_ne_zero),
    ((splitOrthogonalForm F).mem_specialSubgroup_iff _).mpr ⟨ho, Units.ext hd⟩⟩
private def upper (h2 : (2 : F) ≠ 0) (t : F) : SO F :=
  mkSO !![1, t, -t ^ 2 / 2; 0, 1, -t; 0, 0, 1] (by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [gram, Matrix.mul_apply, Fin.sum_univ_succ]
    field_simp
    ring)
    (by simp [Matrix.det_fin_three])
private def torus (a : Fˣ) : SO F :=
  mkSO !![(a : F), 0, 0; 0, 1, 0; 0, 0, (↑a⁻¹ : F)] (by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [gram, Matrix.mul_apply, Fin.sum_univ_succ])
    (by simp [Matrix.det_fin_three])
private def weyl : SO F :=
  mkSO !![0, 0, 1; 0, -1, 0; 1, 0, 0] (by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [gram, Matrix.mul_apply, Fin.sum_univ_succ])
    (by simp [Matrix.det_fin_three])

private def col (A : SO F) : Fin 3 → F := fun i => A.val.val i 0

private theorem orth_entry (A : SO F) (i j : Fin 3) :
    A.val.val 2 i * A.val.val 0 j + A.val.val 1 i * A.val.val 1 j +
      A.val.val 0 i * A.val.val 2 j = gram i j := by
  have h := congrArg (fun M : Matrix (Fin 3) (Fin 3) F => M i j) (orth A)
  simpa [Matrix.mul_apply, Fin.sum_univ_succ, gram, add_assoc] using h

private theorem col_mul_congr (C : SO F) {A B : SO F} (h : col A = col B) :
    col (C * A) = col (C * B) := by
  funext i
  change ∑ j, C.val.val i j * col A j = ∑ j, C.val.val i j * col B j
  rw [h]

/-- The stabilizer of the first basis vector consists of the upper unipotents. -/
private theorem eq_upper_of_col (h2 : (2 : F) ≠ 0) (A : SO F)
    (hc : col A = col 1) : A = upper h2 (A.val.val 0 1) := by
  have h00 : A.val.val 0 0 = 1 := congrFun hc 0
  have h10 : A.val.val 1 0 = 0 := congrFun hc 1
  have h20 : A.val.val 2 0 = 0 := congrFun hc 2
  have h21 : A.val.val 2 1 = 0 := by
    simpa [h00, h10, h20, gram] using orth_entry A 0 1
  have h22 : A.val.val 2 2 = 1 := by
    simpa [h00, h10, h20, gram] using orth_entry A 0 2
  have h11 : A.val.val 1 1 = 1 := by
    simpa [Matrix.det_fin_three, h00, h10, h20, h21, h22] using det_one A
  have h12 : A.val.val 1 2 = -A.val.val 0 1 := by
    have h := orth_entry A 1 2
    simp [h11, h21, h22, gram] at h
    linear_combination h
  have h02 : A.val.val 0 2 = -(A.val.val 0 1) ^ 2 / 2 := by
    have h := orth_entry A 2 2
    simp only [h22, h12, one_mul, mul_one, neg_mul_neg] at h
    change _ = 0 at h
    apply (eq_div_iff h2).mpr
    linear_combination h
  apply Subtype.ext
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [upper, mkSO, h00, h10, h20, h21, h22, h11, h12, h02]

private theorem col_torus (a : Fˣ) : col (torus a) = ![(a : F), 0, 0] := by
  funext i
  fin_cases i <;> rfl
private theorem col_upper (h2 : (2 : F) ≠ 0) (t : F) :
    col (upper h2 t) = col 1 := by
  funext i
  fin_cases i <;> rfl
private theorem col_big (h2 : (2 : F) ≠ 0) (t : F) (a : Fˣ) :
    col (upper h2 t * weyl * torus a) = ![-t ^ 2 / 2 * a, -t * a, (a : F)] := by
  funext i
  fin_cases i <;>
    simp [col, upper, weyl, torus, mkSO, Matrix.mul_apply, Fin.sum_univ_succ]

/-- Representatives for every possible nonzero isotropic first column. -/
private theorem exists_col_representative (h2 : (2 : F) ≠ 0) (A : SO F) :
    (∃ a : Fˣ, col A = col (torus a)) ∨
      (∃ (t : F) (a : Fˣ), col A = col (upper h2 t * weyl * torus a)) := by
  have hq := orth_entry A 0 0
  change _ = 0 at hq
  by_cases hc : A.val.val 2 0 = 0
  · have hb : A.val.val 1 0 = 0 := by
      simpa [hc, mul_self_eq_zero] using hq
    have ha : A.val.val 0 0 ≠ 0 := by
      intro hz
      have hd := det_one A
      simp [Matrix.det_fin_three, hc, hb, hz] at hd
    left
    refine ⟨Units.mk0 _ ha, ?_⟩
    rw [col_torus]
    funext i
    fin_cases i <;> simp [col, hc, hb]
  · right
    refine ⟨-A.val.val 1 0 / A.val.val 2 0, Units.mk0 _ hc, ?_⟩
    rw [col_big]
    funext i
    fin_cases i
    · change A.val.val 0 0 = -(-A.val.val 1 0 / A.val.val 2 0) ^ 2 / 2 * A.val.val 2 0
      field_simp
      linear_combination hq
    · simp [col, hc]
    · rfl

private abbrev Params (F : Type*) [Field F] := (Fˣ × F) ⊕ (F × Fˣ × F)

private def normal (h2 : (2 : F) ≠ 0) : Params F → SO F
  | .inl (a, t) => torus a * upper h2 t
  | .inr (s, a, t) => upper h2 s * weyl * torus a * upper h2 t

private theorem col_normal_left (h2 : (2 : F) ≠ 0) (a : Fˣ) (t : F) :
    col (normal h2 (.inl (a, t))) = ![(a : F), 0, 0] := by
  have h := col_mul_congr (torus a) (col_upper h2 t)
  simpa only [normal, mul_one, col_torus] using h

private theorem col_normal_right (h2 : (2 : F) ≠ 0) (s : F) (a : Fˣ) (t : F) :
    col (normal h2 (.inr (s, a, t))) = ![-s ^ 2 / 2 * a, -s * a, (a : F)] := by
  have h := col_mul_congr (upper h2 s * weyl * torus a) (col_upper h2 t)
  simpa only [normal, mul_one, col_big] using h

private theorem upper_injective (h2 : (2 : F) ≠ 0) : Function.Injective (upper h2) := by
  intro s t h
  exact congrArg (fun A : SO F => A.val.val 0 1) h

private theorem normal_injective (h2 : (2 : F) ≠ 0) : Function.Injective (normal h2) := by
  rintro (⟨a, t⟩ | ⟨s, a, t⟩) (⟨b, u⟩ | ⟨r, b, u⟩) h
  · have hc := congrArg col h
    rw [col_normal_left, col_normal_left] at hc
    have hab : a = b := Units.ext (congrFun hc 0)
    subst b
    have htu := upper_injective h2 (mul_left_cancel (show
      torus a * upper h2 t = torus a * upper h2 u from h))
    subst u
    rfl
  · have hc := congrArg col h
    rw [col_normal_left, col_normal_right] at hc
    exact (b.ne_zero (congrFun hc 2).symm).elim
  · have hc := congrArg col h
    rw [col_normal_right, col_normal_left] at hc
    exact (a.ne_zero (congrFun hc 2)).elim
  · have hc := congrArg col h
    rw [col_normal_right, col_normal_right] at hc
    have hab : a = b := Units.ext (congrFun hc 2)
    subst b
    have hsr : s = r := by
      have hm : -s * (a : F) = -r * (a : F) := congrFun hc 1
      exact neg_injective ((mul_left_inj' a.ne_zero).mp hm)
    subst r
    have htu := upper_injective h2 (mul_left_cancel (show
      (upper h2 s * weyl * torus a) * upper h2 t =
        (upper h2 s * weyl * torus a) * upper h2 u from h))
    subst u
    rfl

private theorem normal_surjective (h2 : (2 : F) ≠ 0) : Function.Surjective (normal h2) := by
  intro A
  rcases exists_col_representative h2 A with ⟨a, ha⟩ | ⟨s, a, ha⟩
  · have hc : col ((torus a)⁻¹ * A) = col 1 := by
      simpa only [inv_mul_cancel] using col_mul_congr (torus a)⁻¹ ha
    have hu := eq_upper_of_col h2 _ hc
    refine ⟨.inl (a, ((torus a)⁻¹ * A).val.val 0 1), ?_⟩
    change torus a * upper h2 _ = A
    rw [← hu, mul_inv_cancel_left]
  · let B := upper h2 s * weyl * torus a
    have hc : col (B⁻¹ * A) = col 1 := by
      simpa only [B, inv_mul_cancel] using col_mul_congr B⁻¹ ha
    have hu := eq_upper_of_col h2 _ hc
    refine ⟨.inr (s, a, (B⁻¹ * A).val.val 0 1), ?_⟩
    change B * upper h2 _ = A
    rw [← hu, mul_inv_cancel_left]

/-- Exact order of the published split ternary special orthogonal group over
any finite field of characteristic different from two. -/
public theorem card_splitOrthogonal_specialSubgroup [Finite F] (h2 : (2 : F) ≠ 0) :
    Nat.card (splitOrthogonalForm F).specialSubgroup = Nat.card F * (Nat.card F ^ 2 - 1) := by
  have h := Nat.card_congr (Equiv.ofBijective (normal h2)
    ⟨normal_injective h2, normal_surjective h2⟩)
  rw [Nat.card_sum, Nat.card_prod, Nat.card_prod, Nat.card_prod, Nat.card_units] at h
  have hp : 0 < Nat.card F := Nat.card_pos
  have he : Nat.card F - 1 + 1 = Nat.card F := Nat.sub_add_cancel hp
  have hs : Nat.card F ^ 2 - 1 + 1 = Nat.card F ^ 2 :=
    Nat.sub_add_cancel (by nlinarith)
  nlinarith

/-- The orthogonal order bound needed for the odd-prime unitary case.
The congruence on the field order suffices; primality is not needed. -/
public theorem card_splitOrthogonal_specialSubgroup_dvd [Finite F] {p : ℕ} (hp : p % 8 = 3) (hc : Nat.card F = p) :
    Nat.card (splitOrthogonalForm F).specialSubgroup ∣ p * (p ^ 2 - 1) := by
  let := Fintype.ofFinite F
  have hchar : ringChar F ≠ 2 := by
    intro he
    have hh := FiniteField.even_card_of_char_two he
    rw [← Nat.card_eq_fintype_card, hc] at hh
    omega
  rw [card_splitOrthogonal_specialSubgroup (Ring.two_ne_zero hchar), hc]

end BenderSuzuki.MatrixGroups.HermitianForm.OddPrimeSylow
