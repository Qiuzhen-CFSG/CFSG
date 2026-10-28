module

public import Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime.LargeSections.OddNondefining.ProductTori
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Split-prime kernels of symplectic four-space covers

For an odd prime r dividing q−1, the diagonal product torus has index
q⁴(q+1)²(q²+1), prime to r. The determinant-one matrix
[[0,−1],[1,0]] on the first hyperbolic plane inverts just the first torus
factor. Thus an actual Sylow r-subgroup has abelian full preimage in every
central cover, and transfer excludes r from a perfect central kernel.

This calculation works in every characteristic. Source: Aschbacher–Smith
I.1.1–4, printed pp.407–408, and GLS3 §6.1, the C₂ row of Table 6.1.2.
-/

open Matrix Subgroup

namespace Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime.LargeSections.OddNondefining.Split
open ProductTori
variable {F : Type*} [Field F]
local notation "SL" => SpecialLinearGroup (Fin 2) F

private def diagonalHom : Fˣ →* SL where
  toFun a := ⟨!![(a : F), 0; 0, (↑a⁻¹ : F)], by simp [det_fin_two]⟩
  map_one' := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  map_mul' a b := by
    apply Subtype.ext
    change !![(↑(a*b) : F), 0; 0, (↑((a*b)⁻¹) : F)] =
      !![(a : F), 0; 0, (↑a⁻¹ : F)] * !![(b : F), 0; 0, (↑b⁻¹ : F)]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [mul_apply, Fin.sum_univ_two, mul_comm]

private theorem diagonalHom_injective : Function.Injective (diagonalHom (F := F)) := by
  intro a b h
  exact Units.ext (congrArg (fun g : SL => g 0 0) h)

private def reflection : SL := ⟨!![0, -1; 1, 0], by simp [det_fin_two]⟩

private theorem reflection_conjugate (a : Fˣ) :
    reflection * diagonalHom a * reflection⁻¹ = diagonalHom a⁻¹ := by
  apply (mul_inv_eq_iff_eq_mul).mpr
  apply Subtype.ext
  change !![0, -1; 1, 0] * !![(a : F), 0; 0, (↑a⁻¹ : F)] =
    !![(↑a⁻¹ : F), 0; 0, (↑((a⁻¹)⁻¹) : F)] * !![0, -1; 1, 0]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [mul_apply, Fin.sum_univ_two]

/-- The actual split torus and its independent Weyl inversion. -/
public theorem exists_split_product :
    ∃ (ι : Fˣ × Fˣ →* Sp F) (w : Sp F), Function.Injective ι ∧
      (∀ c : Fˣ, w * ι (c,1) * w⁻¹ = ι (c⁻¹,1)) ∧
      (∀ c : Fˣ, w * ι (1,c) * w⁻¹ = ι (1,c)) := by
  let ι : Fˣ × Fˣ →* Sp F := pairHom.comp (diagonalHom.prodMap diagonalHom)
  refine ⟨ι, pairHom (reflection,1),
    pairHom_injective.comp (Prod.map_injective.mpr
      ⟨diagonalHom_injective, diagonalHom_injective⟩), ?_, ?_⟩
  · intro c
    change pairHom (reflection,1) * pairHom (diagonalHom c,diagonalHom 1) *
      (pairHom (reflection,1))⁻¹ = pairHom (diagonalHom c⁻¹,diagonalHom 1)
    rw [← map_inv, ← map_mul, ← map_mul]
    apply congrArg pairHom
    apply Prod.ext
    · exact reflection_conjugate c
    · simp
  · intro c
    change pairHom (reflection,1) * pairHom (diagonalHom 1,diagonalHom c) *
      (pairHom (reflection,1))⁻¹ = pairHom (diagonalHom 1,diagonalHom c)
    rw [← map_inv, ← map_mul, ← map_mul]
    apply congrArg pairHom
    apply Prod.ext <;> simp

variable [Finite F]

private theorem split_index (ι : Fˣ × Fˣ →* Sp F) (hι : Function.Injective ι) :
    ι.range.index = (Nat.card F)^4 * (Nat.card F + 1)^2 * ((Nat.card F)^2 + 1) := by
  have hq : 1 < Nat.card F := Finite.one_lt_card
  have hc : Nat.card ι.range = (Nat.card F - 1)^2 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hι).toEquiv,
      Nat.card_prod, Nat.card_units, pow_two]
  have hf2 : (Nat.card F)^2 - 1 = (Nat.card F - 1) * (Nat.card F + 1) := by
    simpa [mul_comm] using Nat.sq_sub_sq (Nat.card F) 1
  have hf4 : (Nat.card F)^4 - 1 = ((Nat.card F)^2 - 1) * ((Nat.card F)^2 + 1) := by
    have h := Nat.sq_sub_sq ((Nat.card F)^2) 1
    simpa only [show ((Nat.card F)^2)^2 = (Nat.card F)^4 by ring,
      one_pow, mul_comm] using h
  apply Nat.eq_of_mul_eq_mul_left (pow_pos (show 0 < Nat.card F - 1 by omega) 2)
  rw [← hc, Subgroup.card_mul_index, Theory.SpecificGroups.SymplecticFour.card_sp,
    hf4, hf2, hc]
  ring

private theorem not_dvd_split_index {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hd : r ∣ Nat.card F - 1) (ι : Fˣ × Fˣ →* Sp F) (hι : Function.Injective ι) :
    ¬ r ∣ ι.range.index := by
  have hq : 1 ≤ Nat.card F := Nat.card_pos
  have hnot2 : ¬ r ∣ 2 := fun h =>
    hr2 ((Nat.dvd_prime Nat.prime_two).mp h |>.resolve_left hr.ne_one)
  have hnotq : ¬ r ∣ Nat.card F := by
    intro h
    have hh := Nat.dvd_sub h hd
    rw [Nat.sub_sub_self hq] at hh
    exact hr.not_dvd_one hh
  have hplus : ¬ r ∣ Nat.card F + 1 := by
    intro h
    have hh := Nat.dvd_sub h hd
    rw [show Nat.card F + 1 - (Nat.card F - 1) = 2 by omega] at hh
    exact hnot2 hh
  have hsq : r ∣ (Nat.card F)^2 - 1 := by
    rw [show (Nat.card F)^2 - 1 = (Nat.card F - 1) * (Nat.card F + 1) by
      simpa [mul_comm] using Nat.sq_sub_sq (Nat.card F) 1]
    exact dvd_mul_of_dvd_left hd _
  have hquad : ¬ r ∣ (Nat.card F)^2 + 1 := by
    intro h
    have hh := Nat.dvd_sub h hsq
    rw [show (Nat.card F)^2 + 1 - ((Nat.card F)^2 - 1) = 2 by
      have : 1 ≤ (Nat.card F)^2 := Nat.one_le_pow _ _ hq
      omega] at hh
    exact hnot2 hh
  rw [split_index ι hι]
  exact hr.not_dvd_mul
    (hr.not_dvd_mul (fun h => hnotq (hr.dvd_of_dvd_pow h))
      (fun h => hplus (hr.dvd_of_dvd_pow h))) hquad

/-- Every odd divisor of q−1 is excluded from a perfect central kernel. -/
public theorem not_dvd_card_kernel_of_dvd_sub_one
    {E : Type*} [Group E] [Finite E]
    {r : ℕ} [Fact r.Prime] (hr2 : r ≠ 2) (hd : r ∣ Nat.card F - 1)
    (f : PerfectCentralCovering.Cover E (Sp F)) :
    ¬ r ∣ Nat.card f.toMonoidHom.ker := by
  obtain ⟨ι, w, hι, hinv, hfix⟩ := exists_split_product (F := F)
  exact not_dvd_card_kernel_of_product_index hr2 ι hι
    (not_dvd_split_index Fact.out hr2 hd ι hι) w hinv hfix f

end Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime.LargeSections.OddNondefining.Split
