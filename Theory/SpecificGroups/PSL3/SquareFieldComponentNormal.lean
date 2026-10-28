module
public import Theory.SpecificGroups.PSL3.OrdinaryCenterRecognition
public import Theory.SpecificGroups.PSL3.SplitPrimeRank
public import Theory.NumberTheory.BinarySignedTorus
public import Theory.GroupTheory.CComponent.OddRankNormal

/-!
# Normality of C-components with a square-field degree-three quotient

For a coefficient field of order 2^(2n), n > 1, the ordinary cover has
center of order dividing three. A split-torus prime greater than three
has rank at least two in the projective quotient and hence in the cover.
The ambient odd-rank bound therefore forces the original C-component to
be normal. The exceptional field-four multiplier is not used here.

Source: Aschbacher--Smith A.2.12(I), A.3.8(3) and C.4.5, printed
pp.36,46,152--153 (refs/quasithin.pdf).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace Matrix.PSL3

/-- The square-field projective marking forces normality in an odd-rank-two ambient group. -/
theorem cComponent_normal_of_square_field_quotient
    {H E : Type*} [Group H] [Finite H] [Field E] [Finite E]
    (hH : ∀ p : ℕ, p.Prime → Odd p → primeRank p H ≤ 2)
    {n : ℕ} (hn : 1 < n) (hc : Nat.card E = 2^(2*n))
    (K : Subgroup H) (hK : K.IsCComponent) [IsQuasisimple (K ⧸ pCore 2 K)]
    (e : ((K ⧸ pCore 2 K) ⧸ center (K ⧸ pCore 2 K)) ≃* PSL(3,E)) : K.Normal := by
  have hlarge : 16 ≤ Nat.card E := by
    rw [hc]
    exact Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (by omega : 4 ≤ 2*n)
  have hz : Nat.card (center (K ⧸ pCore 2 K)) ∣ 3 :=
    (Matrix.PSL3.OrdinaryCenterRecognition.center_card_dvd (by omega) (by omega) e).trans
      (Nat.gcd_dvd_left _ _)
  obtain ⟨p,hp,hp3,hd⟩ := Nat.BinarySignedTorus.exists_prime_gt_three_dvd_sub
    (by omega : 3 < 2*n)
  let : Fact p.Prime := ⟨hp⟩
  have hcop : Nat.Coprime p (Nat.card (center (K ⧸ pCore 2 K))) :=
    (hp.coprime_iff_not_dvd.mpr (fun h => by
      have := Nat.le_of_dvd (by decide : 0 < 3) h
      omega)).of_dvd_right hz
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  have hr : 2 ≤ primeRank p (K ⧸ pCore 2 K) := by
    have hh := Matrix.PSL3.SplitPrimeRank.projective_rank E (by omega : p ≠ 3)
      (by simpa only [hc] using hd)
    rw [← primeRank_congr p e] at hh
    exact hh.trans (primeRank_quotient_le_of_coprime p _ hcop)
  exact hK.normal_of_coprime_core_center_primeRank hodd hcop hr
    (hH p hp hodd)

end Matrix.PSL3
