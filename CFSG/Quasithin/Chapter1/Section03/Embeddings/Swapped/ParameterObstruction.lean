module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.Statements
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support
public import BenderSuzuki.External.Huppert.II.theorem_6_14
public import BenderSuzuki.MatrixGroups.PSL2

/-!
# The order-504 obstruction to the unrestricted model conclusion

The exact PSL₂ order formula forces any rank-two projective special linear
model of a group of order 504 to have field order eight. Such a group cannot
satisfy `SwappedModel`: eight has odd binary degree and is not an odd prime.

This is a necessary-condition obstruction, not recognition from an order.
It supports the source audit of the unrestricted intrinsic version of
Proposition 1.3.4(1), printed p.510. No claim that its input hypotheses have
been instantiated in a counterexample is made by this module.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter1.XiEmbedding
universe u
variable {Q : Type u} [Group Q]

private theorem parameter_eq_eight {q : ℕ} (hq : 1 < q)
    (hc : 504 * Nat.gcd 2 (q - 1) = q * (q ^ 2 - 1)) : q = 8 := by
  have hgpos : 1 ≤ Nat.gcd 2 (q - 1) := Nat.gcd_pos_of_pos_left _ (by decide)
  have hgle : Nat.gcd 2 (q - 1) ≤ 2 := Nat.gcd_le_left _ (by decide)
  have hsq : 1 ≤ q ^ 2 := by nlinarith
  have hlo : 8 ≤ q := by
    by_contra h
    have hq7 : q ≤ 7 := by omega
    have hq2 : q ^ 2 ≤ 49 := by nlinarith
    have hmul : q * (q ^ 2 - 1) ≤ 7 * 48 := Nat.mul_le_mul hq7 (by omega)
    nlinarith
  have hhi : q ≤ 10 := by
    by_contra h
    have hq11 : 11 ≤ q := by omega
    have hq2 : 121 ≤ q ^ 2 := by nlinarith
    have hmul : 11 * 120 ≤ q * (q ^ 2 - 1) := Nat.mul_le_mul hq11 (by omega)
    nlinarith
  interval_cases q <;> norm_num at *

/-- An actual PSL₂ model of an order-504 group has field order eight. -/
theorem isPSL_parameter_of_card_504 {q : ℕ}
    (hcard : Nat.card Q = 504) (hmodel : ClassicalGroup.IsPSL Q 2 q) : q = 8 := by
  obtain ⟨F, hF, hfin, hq, ⟨e⟩⟩ := hmodel
  have hc := BenderSuzuki.External.huppert614_card_psl_mul_center (K := F)
  rw [← Nat.card_congr e.toEquiv, hcard,
    Atlas.ExceptionalSupport.card_sl_center, Fintype.card_fin, hq] at hc
  exact parameter_eq_eight (hq ▸ Finite.one_lt_card (α := F)) hc

/-- Neither parameter alternative in the swapped conclusion permits order 504. -/
theorem not_swappedModel_of_card_504 {p : ℕ} (hcard : Nat.card Q = 504) :
    ¬ SwappedModel p Q := by
  rintro (⟨n, hn, _, he⟩ | ⟨q, hq, _, he⟩)
  · have hpow := isPSL_parameter_of_card_504 hcard he
    have hn3 : n = 3 := Nat.pow_right_injective (by decide : 1 < 2) hpow
    norm_num [hn3] at hn
  · have heq := isPSL_parameter_of_card_504 hcard he
    norm_num [heq] at hq

/-- The concrete projective matrix group over GF(8) has order 504. -/
theorem pslTwoEight_card : Nat.card (BenderSuzuki.MatrixGroups.PSL2BinaryMatrixGroup 3) =
    504 := by
  have h := Atlas.ExceptionalSupport.card_psl_mul
    (F := BenderSuzuki.PFAppendixIII.BinaryGaloisField 3) 2
  have hfield : Nat.card (BenderSuzuki.PFAppendixIII.BinaryGaloisField 3) = 8 :=
    GaloisField.card 2 3 (by decide)
  norm_num [hfield, Fin.prod_univ_succ] at h
  change Nat.card (BenderSuzuki.MatrixGroups.PSL2BinaryMatrixGroup 3) * 7 = 3528 at h
  omega

/-- The actual PSL₂(8) carrier is excluded by the requested swapped-model predicate. -/
theorem pslTwoEight_not_swappedModel (p : ℕ) :
    ¬ SwappedModel p (BenderSuzuki.MatrixGroups.PSL2BinaryMatrixGroup 3) :=
  not_swappedModel_of_card_504 pslTwoEight_card

end CFSG.Quasithin.Chapter1.XiEmbedding
