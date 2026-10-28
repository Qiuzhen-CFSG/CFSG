module

public import Theory.SpecificGroups.Lyons.Atlas111Arithmetic
/-!
# Verified arithmetic for seven-column Lyons transport certificates

Seven base-2048 digits pack one row. A matrix row acts by a natural-number
linear combination of these packed rows. Each output digit is at most
111 * 4 * 4 = 1776, so there is no carry between coordinates. The finite
base-expansion equivalence proves that unpacking gives matrix multiplication
over `ZMod 5`. Numerical checks use only kernel reduction.

This extends the base-five format of `Atlas111Arithmetic`; source attribution
for the ATLAS matrices is in `Atlas111Source/README.md`.
-/

namespace Lyons.OrderCertificate.PlaneTransport
open Lyons.Atlas111Certificate
private theorem decode_encode {b n : ℕ} (f : Fin n → ℕ) (hf : ∀ i, f i < b)
    (i : Fin n) : (∑ j : Fin n, f j * b ^ j.val) / b ^ i.val % b = f i := by
  exact congrArg Fin.val (congrFun
    (finFunctionFinEquiv.symm_apply_apply (fun j => (⟨f j, hf j⟩ : Fin b))) i)
private theorem encode_decode {b n x : ℕ} (hx : x < b ^ n) :
    ∑ j : Fin n, (x / b ^ j.val % b) * b ^ j.val = x := by
  exact congrArg Fin.val (finFunctionFinEquiv.apply_symm_apply (⟨x, hx⟩ : Fin (b ^ n)))
@[expose] public def rowSum : ℕ → ℕ → (ℕ → ℕ) → ℕ
  | 0, _, _ => 0
  | n+1, a, u => rowSum n a u + (a / 5 ^ n % 5) * u n
private theorem rowSum_eq (n a : ℕ) (u : ℕ → ℕ) :
    rowSum n a u = ∑ k : Fin n, (a / 5 ^ k.val % 5) * u k.val := by
  induction n with
  | zero => simp [rowSum]
  | succ n ih => simp only [rowSum, ih, Fin.sum_univ_castSucc, Fin.val_castSucc, Fin.val_last]
@[expose] public def decode (u : Fin 111 → ℕ) : Matrix (Fin 111) (Fin 7) (ZMod 5) :=
  fun i j => (u i / 2048 ^ j.val % 2048 : ℕ)
@[expose] public def valid (u : Fin 111 → ℕ) : Bool :=
  allBelow 111 fun i => u (Fin.ofNat 111 i) < 2048 ^ 7 &&
    allBelow 7 fun j => u (Fin.ofNat 111 i) / 2048 ^ j % 2048 < 5
@[expose] public def rowCheck (x y : ℕ) : Bool :=
  match x with
  | 0 => allBelow 7 fun j => 0 == y / 2048 ^ j % 2048 % 5
  | x + 1 => allBelow 7 fun j => (x + 1) / 2048 ^ j % 2048 % 5 ==
      y / 2048 ^ j % 2048 % 5
private theorem rowCheck_eq (x y : ℕ) : rowCheck x y =
    allBelow 7 (fun j => x / 2048 ^ j % 2048 % 5 == y / 2048 ^ j % 2048 % 5) := by
  cases x <;> simp only [rowCheck, Nat.zero_div, Nat.zero_mod]
@[expose] public def check (r u v : Fin 111 → ℕ) : Bool :=
  allBelow 111 fun i => rowCheck
    (rowSum 111 (r (Fin.ofNat 111 i)) (fun k => u (Fin.ofNat 111 k)))
    (v (Fin.ofNat 111 i))
private theorem ofNat_val {n : ℕ} [NeZero n] (i : Fin n) : Fin.ofNat n i.val = i :=
  Fin.ext (Nat.mod_eq_of_lt i.isLt)
private theorem rowSum_digit (a : ℕ) (u : Fin 111 → ℕ) (hu : valid u = true) (j : Fin 7) :
    rowSum 111 a (fun k => u (Fin.ofNat 111 k)) / 2048 ^ j.val % 2048 =
      ∑ k : Fin 111, (a / 5 ^ k.val % 5) * (u k / 2048 ^ j.val % 2048) := by
  have hv (i : Fin 111) : u i < 2048 ^ 7 ∧
      ∀ j : Fin 7, u i / 2048 ^ j.val % 2048 < 5 := by
    have h := allBelow_sound hu i.val i.isLt
    simp only [ofNat_val, Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨h.1, fun j => by
      have hj := allBelow_sound h.2 j.val j.isLt
      simpa only [decide_eq_true_eq] using hj⟩
  let c : Fin 7 → ℕ := fun j =>
    ∑ k : Fin 111, (a / 5 ^ k.val % 5) * (u k / 2048 ^ j.val % 2048)
  have hc (j : Fin 7) : c j < 2048 := by
    have hle : c j ≤ ∑ _k : Fin 111, (16 : ℕ) := by
      apply Finset.sum_le_sum
      intro k _
      have h1 := Nat.mod_lt (a / 5 ^ k.val) (by decide : 0 < 5)
      have h2 := (hv k).2 j
      exact Nat.mul_le_mul (show a / 5 ^ k.val % 5 ≤ 4 by omega)
        (show u k / 2048 ^ j.val % 2048 ≤ 4 by omega)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hle
    omega
  have hs : rowSum 111 a (fun k => u (Fin.ofNat 111 k)) =
      ∑ j : Fin 7, c j * 2048 ^ j.val := by
    rw [rowSum_eq]
    simp only [ofNat_val]
    conv_lhs => arg 2; ext k; rw [← encode_decode (hv k).1]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    simp only [c, Finset.sum_mul, mul_assoc]
  rw [hs]
  exact decode_encode c hc j

@[expose] public def rowMatrix (r : Fin 111 → ℕ) : Matrix (Fin 111) (Fin 111) (ZMod 5) :=
  fun i j => (r i / 5 ^ j.val : ℕ)

public theorem sound (r u v : Fin 111 → ℕ) (hu : valid u = true) (h : check r u v = true) :
    rowMatrix r * decode u = decode v := by
  funext i j
  have hi := allBelow_sound h i.val i.isLt
  rw [rowCheck_eq] at hi
  have hij := allBelow_sound hi j.val j.isLt
  simp only [ofNat_val, beq_iff_eq] at hij
  rw [rowSum_digit (r i) u hu j] at hij
  have hh := congrArg (fun n : ℕ => (n : ZMod 5)) hij
  simpa only [ZMod.natCast_mod, Nat.cast_sum, Nat.cast_mul, Matrix.mul_apply, decode, rowMatrix] using hh
end Lyons.OrderCertificate.PlaneTransport
