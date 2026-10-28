module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.ProductOrder23.HighProducts.Core
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.ProductOrder23.Data
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.ProductOrder23.Arithmetic
/-!
# Soundness of literal digit certificates

A row is reconstructed from base-65536 digits. Multiplication XORs the selected
rows in each block of 16. The append and remainder lemmas identify this with
the existing sequential checker, including zero extension of short digit lists.
This prevents repeated division of the entire 1792-bit input during each product.
The concrete consumers are the two full checks in `HighProducts.lean`.

Source: word 2 of ATLAS M24G1-P1; see `source/README.md`.
-/

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.ProductOrder23.HighProducts
open Degree320Pair.MatrixCertificates

theorem small_eq (a : Nat) (bs : List Nat) : small a bs = skipRow a bs := by
  induction bs generalizing a with
  | nil => rfl
  | cons b bs ih =>
    have ha : a % 2 = 0 ∨ a % 2 = 1 := by omega
    rcases ha with ha | ha <;> simp [small, skipRow, ha, ih]

theorem small_append (a : Nat) (bs cs : List Nat) :
    small a (bs ++ cs) = small a bs ^^^ small (a / 2 ^ bs.length) cs := by
  induction bs generalizing a with
  | nil => simp [small]
  | cons b bs ih =>
    simp only [List.cons_append, small, ih, List.length_cons, Nat.pow_succ,
      Nat.div_div_eq_div_mul]
    rw [Nat.mul_comm (2 ^ bs.length) 2]
    exact (Nat.xor_assoc _ _ _).symm

theorem small_mod (a : Nat) (bs : List Nat) :
    small (a % 2 ^ bs.length) bs = small a bs := by
  induction bs generalizing a with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.length_cons, Nat.pow_succ, small,
      Nat.mod_mul_left_mod, Nat.mod_mul_left_div_self, ih]

theorem small_zero (bs : List Nat) : small 0 bs = 0 := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simpa [small] using ih

theorem masksRow_eq (ms : List Nat) (bs : List (List Nat))
    (hb : ∀ b ∈ bs, b.length = 16) :
    masksRow ms bs = skipRow (packMasks ms) bs.flatten := by
  rw [← small_eq]
  induction bs generalizing ms with
  | nil => cases ms <;> rfl
  | cons b bs ih =>
    have hlen := hb b (by simp)
    have htail : ∀ c ∈ bs, c.length = 16 := fun c hc => hb c (by simp [hc])
    cases ms with
    | nil => simp [masksRow, packMasks, small_zero]
    | cons m ms =>
      have hmod : packMasks (m :: ms) % 65536 = m % 65536 := by simp [packMasks]
      have hdiv : packMasks (m :: ms) / 65536 = packMasks ms := by
        simp [packMasks, Nat.add_div]
        exact Nat.mod_lt _ (by decide)
      rw [masksRow, List.flatten_cons, small_append, ← small_mod (packMasks (m :: ms)) b,
        hlen, show 2 ^ 16 = 65536 from rfl, hmod, hdiv, ih ms htail]

theorem masksCheck_eq (ms bs : List (List Nat)) (cs : List Nat)
    (hb : ∀ b ∈ bs, b.length = 16) :
    masksCheck ms bs cs = Certificate.check (ms.map packMasks) bs.flatten cs := by
  induction ms generalizing cs with
  | nil => cases cs <;> rfl
  | cons a as ih =>
    cases cs <;> simp [masksCheck, Certificate.check, checkSkip, masksRow_eq _ _ hb, ih]

/-- Convert a complete digit certificate into the original row checker. -/
theorem of_masks (xs zs : List Nat) (rs : List (List Nat))
    (hr : ∀ r ∈ rs, r.length = 16)
    (h : ∃ ms : List (List Nat), ms.map packMasks = xs ∧ masksCheck ms rs zs = true) :
    Certificate.check xs rs.flatten zs = true := by
  obtain ⟨ms, rfl, h⟩ := h
  rwa [masksCheck_eq _ _ _ hr] at h

theorem flattenChecks (xs zs : List (List Nat)) (ys : List Nat)
    (h : List.Forall₂ (fun x z => Certificate.check x ys z = true) xs zs) :
    Certificate.check xs.flatten ys zs.flatten = true := by
  induction h with
  | nil => rfl
  | cons hx hxs ih => exact Certificate.append _ _ _ _ _ hx ih

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.ProductOrder23.HighProducts
