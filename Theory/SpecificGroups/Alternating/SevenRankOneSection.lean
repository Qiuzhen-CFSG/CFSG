module
public import GorensteinWalter.PSL2Cardinality
public import Theory.AtlasPort.OtherSporadic.GroupTheory.SmallIndexSimple
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

/-!
# Binary rank-one sections of proper subgroups of A₇

If a proper subgroup has a quotient SL₂(2ⁿ), n > 1, its order divides 2520.
The two-part bounds n by three. At n = 3 the subgroup has index at most
five, contradicting the faithful coset action of A₇. Thus n = 2. No
classification of subgroups and no condition on the quotient kernel is needed.

Source application: Aschbacher–Smith 10.2.9, printed pp.751–752.
-/

public noncomputable section
open Subgroup
open scoped MatrixGroups
namespace alternatingGroup.SevenRankOneSection
/-- A proper subgroup of A₇ with a binary SL₂ quotient over a field larger than two
has field order four. Its kernel need not be a two-group. -/
theorem degree_eq_two {F : Type*} [Field F] [Finite F]
    {n : ℕ} (hF : Nat.card F = 2^n) (hn : 1 < n)
    (B : Subgroup (alternatingGroup (Fin 7))) (hp : B ≠ ⊤)
    (K : Subgroup B) [K.Normal] (e : (B ⧸ K) ≃* SL(2,F)) : n = 2 := by
  have hA : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
    rw [nat_card_alternatingGroup]; norm_num [Nat.factorial]
  have hd : 2^n ∣ 2520 := by
    have hq : Nat.card (B ⧸ K) ∣ Nat.card B :=
      card_dvd_of_surjective (QuotientGroup.mk' K) (QuotientGroup.mk'_surjective K)
    rw [Nat.card_congr e.toEquiv,GorensteinWalter.sl2_card_formula,hF] at hq
    exact (dvd_mul_right (2^n) _).trans (hq.trans (hA ▸ B.card_subgroup_dvd_card))
  have hn4 : n < 4 := by
    by_contra h
    have h16 := (pow_dvd_pow 2 (by omega : 4 ≤ n)).trans hd
    norm_num at h16
  by_contra hn2
  have hn3 : n = 3 := by omega
  have hQ : Nat.card (B ⧸ K) = 504 := by
    rw [Nat.card_congr e.toEquiv,GorensteinWalter.sl2_card_formula,hF,hn3]
    norm_num
  have hc := B.card_mul_index
  rw [hA] at hc
  have hb : 504 ≤ Nat.card B := by
    rw [←hQ]
    exact Nat.card_le_card_of_surjective (QuotientGroup.mk' K) (QuotientGroup.mk'_surjective K)
  have hi : B.index ≤ 5 := by nlinarith
  let : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
  apply hp
  apply Atlas.GroupTheory.subgroup_eq_top_of_index_factorial_lt
  have hh := Nat.factorial_le hi
  rw [hA]
  norm_num [Nat.factorial] at hh ⊢
  omega
end alternatingGroup.SevenRankOneSection
