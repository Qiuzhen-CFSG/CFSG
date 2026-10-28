module

public import Theory.Character.AbelianLinearCharacters
public import Theory.Character.Generalized
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Integer polynomials in cyclic linear characters

A cyclic generator can be sent to any complex root of its order, giving an
actual one-dimensional representation. Integer polynomials in its character
are generalized characters. The coefficient-list operations below permit
small exact polynomial certificates for values on generator powers; their
soundness is proved by evaluation, without a numerical Fourier oracle.

Source: the character ring of a cyclic group; Serre, *Linear Representations
of Finite Groups*, Chapters 2 and 3.
-/

public section
open scoped BigOperators
namespace CyclicCharacterPolynomial

@[expose] def eval (a : List ℤ) (z : ℂ) : ℂ :=
  match a with
  | [] => 0
  | c :: a => (c : ℂ) + z * eval a z

@[expose] def add : List ℤ → List ℤ → List ℤ
  | [], b => b
  | a, [] => a
  | a :: as, b :: bs => (a + b) :: add as bs

@[expose] def scale (c : ℤ) (a : List ℤ) : List ℤ := a.map (c * ·)

@[expose] def mul : List ℤ → List ℤ → List ℤ
  | [], _ => []
  | a :: as, b => add (scale a b) (0 :: mul as b)

@[expose] def monomial (n : ℕ) (c : ℤ) : List ℤ := List.replicate n 0 ++ [c]

@[expose] def powerImage (n k : ℕ) : ℕ → List ℤ → List ℤ
  | _, [] => []
  | e, c :: cs => add (monomial (e * k % n) c) (powerImage n k (e + 1) cs)

@[simp] theorem eval_add (a b : List ℤ) (z : ℂ) :
    eval (add a b) z = eval a z + eval b z := by
  induction a generalizing b with
  | nil => simp [add, eval]
  | cons c a ih =>
    cases b with
    | nil => simp [add, eval]
    | cons d b => simp only [add, eval, Int.cast_add, ih]; ring

@[simp] theorem eval_scale (c : ℤ) (a : List ℤ) (z : ℂ) :
    eval (scale c a) z = (c : ℂ) * eval a z := by
  induction a with
  | nil => simp [scale, eval]
  | cons d a ih =>
    change (↑(c * d) : ℂ) + z * eval (scale c a) z = _
    rw [ih, Int.cast_mul]
    simp only [eval]
    ring

@[simp] theorem eval_mul (a b : List ℤ) (z : ℂ) :
    eval (mul a b) z = eval a z * eval b z := by
  induction a with
  | nil => simp [mul, eval]
  | cons c a ih => simp only [mul, eval_add, eval_scale, eval, Int.cast_zero, zero_add, ih]; ring

@[simp] theorem eval_monomial (n : ℕ) (c : ℤ) (z : ℂ) :
    eval (monomial n c) z = (c : ℂ) * z ^ n := by
  induction n with
  | zero => simp [monomial, eval]
  | succ n ih =>
    simp only [monomial, List.replicate_succ, List.cons_append, eval, Int.cast_zero]
    change (0 : ℂ) + z * eval (monomial n c) z = _
    rw [ih, pow_succ]
    ring

theorem eval_powerImage (n k e : ℕ) (a : List ℤ) (z : ℂ) (hz : z ^ n = 1) :
    eval (powerImage n k e a) z = z ^ (e * k) * eval a (z ^ k) := by
  induction a generalizing e with
  | nil => simp [powerImage, eval]
  | cons c a ih =>
    simp only [powerImage, eval_add, eval_monomial, ih, ← pow_eq_pow_mod _ hz, eval,
      Nat.add_mul, one_mul, pow_add]
    ring

theorem eval_zero (a : List ℤ) (z : ℂ) (h : a.all (· == 0) = true) : eval a z = 0 := by
  induction a with
  | nil => rfl
  | cons c a ih =>
    have hc : c = 0 ∧ a.all (· == 0) = true := by simpa using h
    simp [eval, hc.1, ih hc.2]

theorem eval_eq_of_certificate (a b modulus q : List ℤ) (z : ℂ)
    (hm : eval modulus z = 0)
    (hc : (add a (add (scale (-1) b) (mul modulus q))).all (· == 0) = true) :
    eval a z = eval b z := by
  have he := eval_zero _ z hc
  simp only [eval_add, eval_scale, eval_mul, Int.cast_neg, Int.cast_one, hm, zero_mul,
    add_zero, neg_one_mul] at he
  exact sub_eq_zero.mp (by simpa only [sub_eq_add_neg] using he)

theorem generalized_eval {G : Type*} [Group G] (χ : G →* ℂ) (a : List ℤ) :
    IsGeneralizedCharacter (fun x => eval a (χ x)) := by
  have hχ : IsCharacter (χ : G → ℂ) := by
    obtain ⟨n, ρ, _, hρ⟩ := χ.isLinearCharacter.1
    exact ⟨n, ρ, hρ⟩
  induction a with
  | nil => exact isGeneralizedCharacter_zero
  | cons c a ih =>
    convert (isCharacter_one.isGeneralized.zsmul c).add (hχ.mul_generalized ih) using 1
    funext x
    simp [eval]

theorem cyclic_realization {G : Type*} [Group G] [Finite G]
    (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g)
    (z : ℂ) (hz : z ^ orderOf g = 1) (a : List ℤ) (f : G → ℂ)
    (hf : ∀ k : ℕ, f (g ^ k) = eval a (z ^ k)) : IsGeneralizedCharacter f := by
  have hz0 : z ≠ 0 := by
    intro he
    have ho : orderOf g ≠ 0 := orderOf_pos g |>.ne'
    simp [he, ho] at hz
  let u : ℂˣ := Units.mk0 z hz0
  have hu : orderOf u ∣ orderOf g := by
    rw [← orderOf_units]
    exact orderOf_dvd_of_pow_eq_one hz
  let χ := (Units.coeHom ℂ).comp (monoidHomOfForallMemZpowers hg hu)
  have hχ : χ g = z := by simp [χ, u]
  have he : f = fun x => eval a (χ x) := by
    funext x
    obtain ⟨k, rfl⟩ := (show x ∈ Submonoid.powers g ↔ ∃ k : ℕ, g ^ k = x from Iff.rfl).mp (mem_powers_iff_mem_zpowers.mpr (hg x))
    rw [map_pow, hχ, hf]
  rw [he]
  exact generalized_eval χ a

end CyclicCharacterPolynomial
