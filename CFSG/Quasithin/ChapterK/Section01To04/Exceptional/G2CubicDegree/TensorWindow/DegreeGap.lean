module

public import CFSG.Quasithin.ChapterK.Section01To04.Exceptional.G2CubicDegree.Arithmetic
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.G2Recognition.Nonbinary.FrobeniusParameters

/-!
# The only G₂ Frobenius degree between eighteen and thirty-four

The actual Schur-field parameters give binary degree `s*b^t`, defining-field
degree `r=s*t`, and a nontrivial basic product `b` of 1, 6, 14 and 64.
In the interval `18*r ≤ dim V < 34*r`, the product gap forces `t=2`
and `b=6`; hence `r=2*s` and `dim V=18*r`. Three repeated nontrivial
blocks already exceed the interval, as does any full-period tensor product.

The representation corollary uses the proved, unconditional Frobenius
parameters, not an assumed tensor catalogue. This isolates the natural tensor
over the field of half the defining degree for the fixed-space calculation.

Source: Guralnick–Malle, Classification of 2F-modules II, §3.5 and Lemma 8.5,
manuscript pp.20,55–56. The coarse bound `34*r` comes from the actual join
of the component image with the chosen actor and is supplied separately.
-/

public section
namespace CFSG.Quasithin.ChapterK.Exceptional.G2CubicDegree.TensorWindow

private theorem thirtyFour_mul_le_six_pow {t : ℕ} (ht : 3 ≤ t) :
    34 * t ≤ 6 ^ t := by
  induction t, ht using Nat.le_induction with
  | base => norm_num
  | succ t ht ih =>
    rw [pow_succ]
    nlinarith

/-- The sole Frobenius degree in `[18*n,34*n)` repeats a natural block twice. -/
theorem parameters_in_tensor_window {n d s t : ℕ} (l : List ℕ)
    (hs : 0 < s) (ht : 0 < t)
    (hl : ∀ a ∈ l, a = 1 ∨ a = 6 ∨ a = 14 ∨ a = 64)
    (hne : l.prod ≠ 1) (hn : n = s * t) (hd : d = s * l.prod ^ t)
    (hlo : 18 * n ≤ d) (hhi : d < 34 * n) :
    t = 2 ∧ l.prod = 6 ∧ n = 2 * s ∧ d = 18 * n := by
  have hp := basic_product_gap l hl
  have hge : 6 ≤ l.prod := by omega
  have ht_le : t ≤ 2 := by
    by_contra h
    have hh := (thirtyFour_mul_le_six_pow (by omega : 3 ≤ t)).trans
      (Nat.pow_le_pow_left hge t)
    have hh' : 34 * n ≤ d := calc
      34 * n = s * (34 * t) := by rw [hn]; ring
      _ ≤ s * l.prod ^ t := Nat.mul_le_mul_left s hh
      _ = d := hd.symm
    omega
  have ht_ne : t ≠ 1 := by
    intro ht1
    rw [ht1, mul_one] at hn
    rw [ht1, pow_one] at hd
    rcases hp with hp | hp | hp | hp
    · exact hne hp
    · nlinarith
    · nlinarith
    · nlinarith
  have ht2 : t = 2 := by omega
  rw [ht2, pow_two] at hd
  rw [ht2] at hn
  have hp6 : l.prod = 6 := by
    rcases hp with hp | hp | hp | hp
    · exact (hne hp).elim
    · exact hp
    · rw [hp] at hd
      nlinarith
    · have hh : 68 ≤ l.prod * l.prod := by nlinarith
      have hh' := Nat.mul_le_mul_left s hh
      nlinarith
  refine ⟨ht2, hp6, by omega, ?_⟩
  rw [hp6] at hd
  omega

open Representation
open CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.G2Recognition

/-- Applied to the actual binary module and its genuine Schur/Frobenius parameters. -/
theorem degree_eq_eighteen_of_large_lt_thirtyFour
    {F V : Type*} [Field F] [Finite F] [CharP F 2]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (σ : Representation (ZMod 2) (Atlas.G2.Model F) V) [IsIrreducible σ]
    {r : ℕ} (hr : 2 ≤ r) (hF : Nat.card F = 2 ^ r) (hf : Function.Injective σ)
    (hlo : 18 * r ≤ Module.finrank (ZMod 2) V)
    (hhi : Module.finrank (ZMod 2) V < 34 * r) :
    Module.finrank (ZMod 2) V = 18 * r := by
  obtain ⟨hs, t, l, ht, _, hrt, hd, hne, hb⟩ :=
    Nonbinary.exists_basic_parameters σ hr hF hf
  exact (parameters_in_tensor_window l hs ht hb hne hrt hd hlo hhi).2.2.2

end CFSG.Quasithin.ChapterK.Exceptional.G2CubicDegree.TensorWindow
