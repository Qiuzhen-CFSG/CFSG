module
public import Theory.SpecificGroups.PSL3.SplitPrimeRank
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.DefiningSylow
public import Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrimary.Nonsplit
public import Theory.SpecificGroups.SymplecticFour.SplitTorusRank
public import Theory.AtlasPort.LinearGroups.G2.Order
public import Theory.AtlasPort.LinearGroups.G2.Torus

/-!
# Seventeen divisibility and five-rank in binary classical groups

In the SL₃, Sp₄ and G₂ rows, divisibility of the group order by 17 forces
five-rank at least two. Reduce the binary field degree modulo eight, then use
an actual split torus or, for Sp₄, the quadratic norm-one torus.

These are the concrete model comparisons used in the exchanged-factor branch
of Aschbacher–Smith, *The Classification of Quasithin Groups*, 14.6.15,
printed p. 1035. The G₂ carrier, torus and order formula are the existing ATLAS
ports imported above; this module adds only the prime-rank consequence.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace Theory.SpecificGroups.Classical.SeventeenFiveRank
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
private theorem split_three (n : ℕ) (h : 17 ∣ (2^n)^3 * ((2^n)^3-1) * ((2^n)^2-1)) :
    5 ∣ 2^n-1 := by
  have hq : 1 ≤ 2^n := Nat.one_le_pow _ _ (by decide)
  have h2 : 1 ≤ (2^n)^2 := Nat.one_le_pow _ _ hq
  have h3 : 1 ≤ (2^n)^3 := Nat.one_le_pow _ _ hq
  have hz := (ZMod.natCast_eq_zero_iff _ 17).mpr h
  push_cast [Nat.cast_sub h2,Nat.cast_sub h3] at hz
  have he : (2 : ZMod 17)^n = 2^(n%8) := pow_eq_pow_mod _ (by decide : (2 : ZMod 17)^8=1)
  rw [he] at hz
  have hm : n%8<8 := Nat.mod_lt _ (by decide)
  have hn : 4 ∣ n := by
    interval_cases hh : n%8
    all_goals first | omega | (exfalso; revert hz; decide)
  apply (ZMod.natCast_eq_zero_iff _ 5).mp
  rw [Nat.cast_sub hq,Nat.cast_pow,Nat.cast_ofNat,Nat.cast_one]
  have hp : (2 : ZMod 5)^n = 1 := by
    obtain ⟨k,rfl⟩ := hn
    rw [pow_mul,(by decide : (2 : ZMod 5)^4=1),one_pow]
  rw [hp,sub_self]

private theorem split_six (n : ℕ) (h : 17 ∣ (2^n)^6 * ((2^n)^6-1) * ((2^n)^2-1)) :
    5 ∣ 2^n-1 := by
  have hq : 1 ≤ 2^n := Nat.one_le_pow _ _ (by decide)
  have h2 : 1 ≤ (2^n)^2 := Nat.one_le_pow _ _ hq
  have h3 : 1 ≤ (2^n)^6 := Nat.one_le_pow _ _ hq
  have hz := (ZMod.natCast_eq_zero_iff _ 17).mpr h
  push_cast [Nat.cast_sub h2,Nat.cast_sub h3] at hz
  have he : (2 : ZMod 17)^n = 2^(n%8) := pow_eq_pow_mod _ (by decide : (2 : ZMod 17)^8=1)
  rw [he] at hz
  have hm : n%8<8 := Nat.mod_lt _ (by decide)
  have hn : 4 ∣ n := by
    interval_cases hh : n%8
    all_goals first | omega | (exfalso; revert hz; decide)
  apply (ZMod.natCast_eq_zero_iff _ 5).mp
  rw [Nat.cast_sub hq,Nat.cast_pow,Nat.cast_ofNat,Nat.cast_one]
  have hp : (2 : ZMod 5)^n = 1 := by
    obtain ⟨k,rfl⟩ := hn
    rw [pow_mul,(by decide : (2 : ZMod 5)^4=1),one_pow]
  rw [hp,sub_self]

private theorem split_four (n : ℕ) (h : 17 ∣ (2^n)^4 * ((2^n)^2-1) * ((2^n)^4-1)) :
    5 ∣ 2^n-1 ∨ 5 ∣ 2^n+1 := by
  have hq : 1 ≤ 2^n := Nat.one_le_pow _ _ (by decide)
  have h2 : 1 ≤ (2^n)^2 := Nat.one_le_pow _ _ hq
  have h4 : 1 ≤ (2^n)^4 := Nat.one_le_pow _ _ hq
  have hz := (ZMod.natCast_eq_zero_iff _ 17).mpr h
  push_cast [Nat.cast_sub h2,Nat.cast_sub h4] at hz
  have he : (2 : ZMod 17)^n = 2^(n%8) := pow_eq_pow_mod _ (by decide : (2 : ZMod 17)^8=1)
  rw [he] at hz
  have hm : n%8<8 := Nat.mod_lt _ (by decide)
  have hn : 2 ∣ n := by
    interval_cases hh : n%8
    all_goals first | omega | (exfalso; revert hz; decide)
  have hm4 : n%4=0 ∨ n%4=2 := by omega
  have he5 : (2 : ZMod 5)^n = 2^(n%4) := pow_eq_pow_mod _ (by decide : (2 : ZMod 5)^4=1)
  rcases hm4 with hh | hh
  · left
    apply (ZMod.natCast_eq_zero_iff _ 5).mp
    rw [Nat.cast_sub hq,Nat.cast_pow,Nat.cast_ofNat,Nat.cast_one,he5,hh]
    decide
  · right
    apply (ZMod.natCast_eq_zero_iff _ 5).mp
    rw [Nat.cast_add,Nat.cast_pow,Nat.cast_ofNat,Nat.cast_one,he5,hh]
    decide

variable {F : Type*} [Field F] [Finite F] {n : ℕ}

/-- Divisibility by seventeen forces a split elementary twenty-five in SL₃(2ⁿ). -/
theorem linearThree (hF : Nat.card F = 2^n) (h17 : 17 ∣ Nat.card SL(3,F)) :
    2 ≤ primeRank 5 SL(3,F) := by
  rw [Matrix.PSL3.LinearThree.DefiningSylow.card_specialLinear,hF] at h17
  exact Matrix.PSL3.SplitPrimeRank.special_rank F (hF ▸ split_three n h17)

private theorem rank_of_product_embedding {C A : Type*} [Group C] [Finite C]
    [Group A] [Finite A] (h5 : 5 ∣ Nat.card C)
    (f : C × C →* A) (hf : Function.Injective f) : 2 ≤ primeRank 5 A := by
  have hr : 1 ≤ primeRank 5 C := by
    by_contra hh
    exact PrimeRank.eq_zero_iff_not_dvd_card.mp (show primeRank 5 C = 0 by omega) h5
  have hi := Theory.GroupTheory.primeRank_le_of_injective 5 f hf
  rw [primeRank_prod_eq_add] at hi
  omega

/-- Divisibility by seventeen forces five-rank two in the actual G₂ carrier. -/
theorem g2 (hF : Nat.card F = 2^n) (h17 : 17 ∣ Nat.card (Atlas.G2.Model F)) :
    2 ≤ primeRank 5 (Atlas.G2.Model F) := by
  rw [Atlas.G2.card_Model,hF] at h17
  apply rank_of_product_embedding (C := Fˣ) _ Atlas.G2.torusHom Atlas.G2.torusHom_injective
  rw [Nat.card_units,hF]
  exact split_six n h17

/-- Either the split or the actual quadratic norm-one torus supplies
an elementary twenty-five in the symplectic model. -/
theorem symplectic [CharP F 2] (hF : Nat.card F = 2^n)
    (h17 : 17 ∣ Nat.card (Matrix.symplecticGroup (Fin 2) F)) :
    2 ≤ primeRank 5 (Matrix.symplecticGroup (Fin 2) F) := by
  rw [Theory.SpecificGroups.SymplecticFour.card_sp,hF] at h17
  rcases split_four n h17 with hm | hp
  · exact Theory.SpecificGroups.SymplecticFour.split_torus_prime_rank (by decide) (hF ▸ hm)
  · obtain ⟨f,_,hc,hf,_,_⟩ :=
      Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrimary.exists_nonsplit_product (F := F)
    exact rank_of_product_embedding (by rwa [hc,hF]) f hf

end Theory.SpecificGroups.Classical.SeventeenFiveRank
