module
public import Theory.GroupTheory.CentralActorRank
public import Theory.GroupTheory.PrimeRankInvolutionLift
public import Theory.SpecificGroups.PSL3Even.TwoRank
public import Theory.SpecificGroups.PSL4Two.SchurMultiplier
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order168
public import Theory.Alternating.PrimeRank
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.SourceCases

/-!
# Binary rank screens in the secondary alternating-five centralizer

The independent central involution raises the two-rank of every center-free
component by one. A binary PSL3 component therefore has field size two,
and the binary PSL4 component is excluded by its elementary sixteen subgroup.
The retained PSL3(2) row is identified with PSL2(7).

Source: Aschbacher--Smith, inspection in 2.4.29, printed pp.545--546.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter2.SmallBlocks.AlternatingSecondaryCensus
variable {H : Type*} [Group H] [Finite H]

private theorem central_actor_rank_bound (K : Subgroup H) (hZ : center K = ⊥)
    (u : H) (hu : u ∈ center H) (hu2 : orderOf u = 2) :
    primeRank 2 K + 1 ≤ primeRank 2 H := by
  obtain ⟨E,hE,hEc⟩ := exists_elementaryAbelian_card_primeRank (G := K) (p := 2)
  let := hE
  exact K.primeRank_ge_of_central_actor hZ E hEc u hu hu2

theorem binary_linear_three_row_of_rank_le_four (K : Subgroup H)
    (u : H) (hu : u ∈ center H) (hu2 : orderOf u = 2)
    (hr : primeRank 2 H ≤ 4) {n : ℕ} (hn : 1 ≤ n)
    (hm : ClassicalGroup.IsPSL K 3 (2 ^ n)) :
    Nonempty (K ≃* PSL(2,ZMod 7)) := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let : Group.IsPerfect SL(3,F) := Atlas.sl_perfect 3 (by decide)
  have hZ : center K = ⊥ := by
    apply eq_bot_iff.mpr
    intro x hx
    have hz : e x ∈ center PSL(3,F) := (centerCongr e ⟨x,hx⟩).property
    rw [show center PSL(3,F) = ⊥ from
      Group.IsPerfect.center_quotient_center_eq_bot SL(3,F)] at hz
    exact mem_bot.mpr (e.injective (by simpa using mem_bot.mp hz))
  have hb := (central_actor_rank_bound K hZ u hu hu2).trans hr
  rw [primeRank_equiv 2 e,Matrix.PSL3Even.two_rank F (by omega) hF] at hb
  have hn1 : n = 1 := by omega
  subst n
  let : Fintype F := Fintype.ofFinite F
  let eF : F ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
    simpa only [←Nat.card_eq_fintype_card,Nat.card_zmod,pow_one] using hF)
  exact ⟨e.trans ((Atlas.fieldEquivPSL 3 eF).trans
    Atlas.Comparisons.Exceptional.psl2SevenEquivPsl3Two.symm)⟩

theorem alternating_eight_row_false (K : Subgroup H)
    (u : H) (hu : u ∈ center H) (hu2 : orderOf u = 2)
    (hr : primeRank 2 H ≤ 4) (e : K ≃* alternatingGroup (Fin 8)) : False := by
  have hZ : center K = ⊥ := by
    apply eq_bot_iff.mpr
    intro x hx
    have hz : e x ∈ center (alternatingGroup (Fin 8)) := (centerCongr e ⟨x,hx⟩).property
    rw [alternatingGroup.center_eq_bot (by simp)] at hz
    exact mem_bot.mpr (e.injective (by simpa using mem_bot.mp hz))
  obtain ⟨A,hA,hAc⟩ := GLS3.Chapter5.PRank.alternating_hasPRank_two_lower_bound 8
  let : IsElementaryAbelian 2 A :=
    (GLS3.Chapter5.PRank.elementaryAbelian_iff_exponent (by decide)).mp hA
  have ha : 4 ≤ primeRank 2 (alternatingGroup (Fin 8)) :=
    IsElementaryAbelian.primeRank_ge_of_card A (by simpa using hAc)
  have hb := (central_actor_rank_bound K hZ u hu hu2).trans hr
  rw [primeRank_equiv 2 e] at hb
  omega

theorem binary_linear_four_row_false (K : Subgroup H)
    (u : H) (hu : u ∈ center H) (hu2 : orderOf u = 2)
    (hr : primeRank 2 H ≤ 4)
    (e : K ≃* ComponentRefinement.LieType.Binary.PSL 4) : False := by
  exact alternating_eight_row_false K u hu hu2 hr
    (e.trans (Matrix.PSL4Two.binaryEquivAlternatingEight (ZMod 2) (by simp)))

end CFSG.Quasithin.Chapter2.SmallBlocks.AlternatingSecondaryCensus
