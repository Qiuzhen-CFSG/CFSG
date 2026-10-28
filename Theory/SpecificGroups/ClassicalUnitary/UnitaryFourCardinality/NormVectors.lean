module

public import Theory.SpecificGroups.ClassicalUnitary.OddFundamental.CentralizerResidual.Generation.Reduction
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Counting norm-one vectors over a quadratic finite field

For the identity Hermitian form over a field of order q² with conjugation
x ↦ x^q, a nonzero fixed scalar has q+1 norm preimages and zero has one.
The first assertion follows from the kernel of the (q+1)-power map on the
cyclic multiplicative group, together with norm surjectivity.

Splitting off one coordinate therefore gives
`a_(n+1) = a_n + (q^(2*n) - a_n) * (q+1)` for the number a_n of norm-one
vectors. In dimensions three and four this is respectively
`q² * (q³+1)` and `q³ * (q⁴-1)`.

These are the orbit counts used by `UnitaryFourCardinality` to count the
actual special unitary matrix group. Norm surjectivity is Huppert II.10.4;
the source application is Aschbacher–Smith I.1.4(3), printed p.408 of
`refs/quasithin.pdf`, and GLS3 §6.1.
-/

public section

open Matrix BenderSuzuki.MatrixGroups
open Theory.SpecificGroups.ClassicalUnitary.OddFundamental
open Theory.SpecificGroups.ClassicalUnitary.OddFundamental.Generation
namespace Theory.SpecificGroups.ClassicalUnitary.UnitaryFourCardinality
variable {F : Type*} [Field F] [Finite F] (σ : F ≃+* F)

private theorem scalar_card_one {q : ℕ} (hq : 1 < q)
    (hc : Nat.card F = q ^ 2) (hj : ∀ x, σ x = x ^ q) :
    Nat.card {x : F // σ x * x = 1} = q + 1 := by
  let e : (powMonoidHom (q + 1) : Fˣ →* Fˣ).ker ≃ {x : F // σ x * x = 1} :=
    { toFun := fun u => ⟨u.val.val, by
        rw [hj, ← pow_succ]
        exact congrArg Units.val u.property⟩
      invFun := fun x => ⟨Units.mk0 x.val (by
        intro hz
        have hx := x.property
        simp [hz] at hx), by
        apply Units.ext
        change x.val ^ (q+1) = 1
        simpa [pow_succ, ← hj] using x.property⟩
      left_inv := fun u => by apply Subtype.ext; apply Units.ext; rfl
      right_inv := fun x => rfl }
  rw [← Nat.card_congr e, IsCyclic.card_powMonoidHom_ker, Nat.card_units, hc]
  apply Nat.gcd_eq_right
  have hmul : q ^ 2 - 1 = (q-1)*(q+1) := by
    have := Nat.sub_add_cancel (show 1 ≤ q by omega)
    have := Nat.sub_add_cancel (show 1 ≤ q^2 by nlinarith)
    nlinarith
  rw [hmul]
  exact dvd_mul_left _ _

variable (hσ : Function.Involutive σ)

include hσ in
private theorem scalar_card_nonzero {q : ℕ} (hq : IsPrimePow q)
    (hc : Nat.card F = q ^ 2) (hj : ∀ x, σ x = x ^ q)
    (a : F) (ha : σ a = a) (ha0 : a ≠ 0) :
    Nat.card {x : F // σ x * x = a} = q + 1 := by
  obtain ⟨b, hb0, hb⟩ := BenderSuzuki.External.huppert_II_10_4_norm_surjective
    (form σ hσ 2) q hc ((form σ hσ 2).fixed_card_prime_power hq hc hj) a ha ha0
  have hb' : σ b * b = a := by simpa [form, mul_comm] using hb
  let e : {x : F // σ x * x = 1} ≃ {x : F // σ x * x = a} :=
    { toFun := fun x => ⟨b * x.val, by
        calc
          σ (b * x.val) * (b * x.val) = (σ b * b) * (σ x.val * x.val) := by
            rw [map_mul]; ring
          _ = a := by rw [hb', x.property, mul_one]⟩
      invFun := fun y => ⟨b⁻¹ * y.val, by
        calc
          σ (b⁻¹ * y.val) * (b⁻¹ * y.val) = (σ b * b)⁻¹ * (σ y.val * y.val) := by
            rw [map_mul, map_inv₀, _root_.mul_inv_rev]; ring
          _ = 1 := by rw [hb', y.property, inv_mul_cancel₀ ha0]⟩
      left_inv := fun x => by apply Subtype.ext; simp [hb0]
      right_inv := fun y => by apply Subtype.ext; simp [hb0] }
  rw [← Nat.card_congr e]
  exact scalar_card_one σ hq.one_lt hc hj

omit [Finite F] in
private theorem scalar_card_zero : Nat.card {x : F // σ x * x = 0} = 1 := by
  simp only [mul_eq_zero, map_eq_zero, or_self]
  simp

omit [Finite F] in
include hσ in
private theorem norm_fixed {n : ℕ} (x : Fin n → F) : σ (Generation.norm σ x) = Generation.norm σ x := by
  unfold Generation.norm
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_mul, hσ (x i)]
  exact mul_comm _ _

private def splitNormVector (n : ℕ) :
    {x : Fin (n+1) → F // Generation.norm σ x = 1} ≃
      (Σ y : Fin n → F, {z : F // σ z * z = 1 - Generation.norm σ y}) where
  toFun x := ⟨fun i => x.val i.succ, x.val 0, by
    have hx := x.property
    rw [Generation.norm, Fin.sum_univ_succ] at hx
    exact eq_sub_of_add_eq hx⟩
  invFun yz := ⟨Fin.cons yz.2.val yz.1, by
    change (∑ i, σ ((Fin.cons (α := fun _ => F) yz.2.val yz.1) i) * (Fin.cons (α := fun _ => F) yz.2.val yz.1) i) = 1
    rw [Fin.sum_univ_succ]
    change σ yz.2.val * yz.2.val + Generation.norm σ yz.1 = 1
    rw [yz.2.property, sub_add_cancel]⟩
  left_inv x := by
    apply Subtype.ext
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  right_inv yz := by cases yz; rfl

include hσ in
private theorem card_norm_one_succ {q : ℕ} (hq : IsPrimePow q)
    (hc : Nat.card F = q ^ 2) (hj : ∀ x, σ x = x ^ q) (n : ℕ) :
    Nat.card {x : Fin (n+1) → F // Generation.norm σ x = 1} =
      Nat.card {x : Fin n → F // Generation.norm σ x = 1} +
      (q ^ (2*n) - Nat.card {x : Fin n → F // Generation.norm σ x = 1}) * (q+1) := by
  classical
  let : Fintype F := Fintype.ofFinite F
  rw [Nat.card_congr (splitNormVector σ n), Nat.card_sigma]
  have hs (y : Fin n → F) :
      Nat.card {z : F // σ z * z = 1 - Generation.norm σ y} =
        if Generation.norm σ y = 1 then 1 else q+1 := by
    by_cases hy : Generation.norm σ y = 1
    · simp only [hy, sub_self, if_true]
      exact scalar_card_zero σ
    · rw [if_neg hy]
      exact scalar_card_nonzero σ hσ hq hc hj _
        (by rw [map_sub, map_one, norm_fixed σ hσ]) (sub_ne_zero.mpr (Ne.symm hy))
  simp_rw [hs]
  simp only [Finset.sum_ite, Finset.sum_const, smul_eq_mul, mul_one]
  rw [← Fintype.card_subtype, ← Fintype.card_subtype, Fintype.card_subtype_compl]
  simp only [← Nat.card_eq_fintype_card, Nat.card_fun, Nat.card_fin, hc, ← pow_mul]

include hσ in
private theorem card_norm_one_recurrence {q : ℕ} (hq : IsPrimePow q)
    (hc : Nat.card F = q ^ 2) (hj : ∀ x, σ x = x ^ q) (n : ℕ) :
    Nat.card {x : Fin (n+1) → F // Generation.norm σ x = 1} +
      q * Nat.card {x : Fin n → F // Generation.norm σ x = 1} = q ^ (2*n) * (q+1) := by
  have hle : Nat.card {x : Fin n → F // Generation.norm σ x = 1} ≤ q ^ (2*n) := by
    calc
      _ ≤ Nat.card (Fin n → F) := Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
      _ = q ^ (2*n) := by rw [Nat.card_fun, Nat.card_fin, hc, pow_mul]
  rw [card_norm_one_succ σ hσ hq hc hj]
  have := Nat.sub_add_cancel hle
  nlinarith

omit [Finite F] in
private theorem card_norm_one_zero : Nat.card {x : Fin 0 → F // Generation.norm σ x = 1} = 0 := by
  simp [Generation.norm]

include hσ in
private theorem card_norm_one_one {q : ℕ} (hq : IsPrimePow q)
    (hc : Nat.card F = q ^ 2) (hj : ∀ x, σ x = x ^ q) :
    Nat.card {x : Fin 1 → F // Generation.norm σ x = 1} = q+1 := by
  simpa [card_norm_one_zero σ] using card_norm_one_recurrence σ hσ hq hc hj 0

include hσ in
private theorem card_norm_one_two {q : ℕ} (hq : IsPrimePow q)
    (hc : Nat.card F = q ^ 2) (hj : ∀ x, σ x = x ^ q) :
    Nat.card {x : Fin 2 → F // Generation.norm σ x = 1} = q * (q^2-1) := by
  have h := card_norm_one_recurrence σ hσ hq hc hj 1
  rw [card_norm_one_one σ hσ hq hc hj] at h
  have := Nat.sub_add_cancel (show 1 ≤ q^2 from one_le_pow₀ (by have := hq.one_lt; omega))
  norm_num at h
  nlinarith

include hσ in
theorem card_norm_one_three {q : ℕ} (hq : IsPrimePow q)
    (hc : Nat.card F = q ^ 2) (hj : ∀ x, σ x = x ^ q) :
    Nat.card {x : Fin 3 → F // Generation.norm σ x = 1} = q^2 * (q^3+1) := by
  have h := card_norm_one_recurrence σ hσ hq hc hj 2
  rw [card_norm_one_two σ hσ hq hc hj] at h
  have := Nat.sub_add_cancel (show 1 ≤ q^2 from one_le_pow₀ (by have := hq.one_lt; omega))
  norm_num at h
  nlinarith

include hσ in
theorem card_norm_one_four {q : ℕ} (hq : IsPrimePow q)
    (hc : Nat.card F = q ^ 2) (hj : ∀ x, σ x = x ^ q) :
    Nat.card {x : Fin 4 → F // Generation.norm σ x = 1} = q^3 * (q^4-1) := by
  have h := card_norm_one_recurrence σ hσ hq hc hj 3
  rw [card_norm_one_three σ hσ hq hc hj] at h
  have := congrArg (fun a : ℕ => q^3 * a)
    (Nat.sub_add_cancel (show 1 ≤ q^4 from one_le_pow₀ (by have := hq.one_lt; omega)))
  norm_num at h
  nlinarith
end Theory.SpecificGroups.ClassicalUnitary.UnitaryFourCardinality
