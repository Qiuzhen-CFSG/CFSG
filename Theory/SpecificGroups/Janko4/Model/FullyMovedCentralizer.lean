module
public import Theory.SpecificGroups.Janko4.Model.IrreducibleCentralizer
public import Theory.GroupAction.PerfectMovedSmallCenter

/-!
# Odd centralizers of fully moved sections in J₄

An even centralizer supplies an involution centralized by the full Sylow.
The native involution-centralizer geometry gives a self-centralizing two-core
whose center has order at most two. The commuting fixed-point argument
excludes the original nonzero fully moved elementary section, without any
irreducibility assumption or choice of coordinates.

Source: Aschbacher--Smith A.3.12 and 10.2.9, pp.47--48,750--751.
The non-A₅ point-component comparison is the actual consumer.
-/

public section
namespace Janko4
open Subgroup Theory.GroupTheory
open InvolutionCentralizers
attribute [local irreducible] modelGroup matrixA matrixB

theorem centralizer_odd_of_fully_moved_section
    (S : Sylow 2 Model) (B E : Subgroup Model) [Group.IsPerfect B] (hB : IsPPerfect 2 B)
    (hSB : (S : Subgroup Model) ≤ normalizer (B : Set Model))
    (hSE : (S : Subgroup Model) ≤ normalizer (E : Set Model))
    (hE : IsElementaryAbelian 2 E) (hEB : E ≤ B) (hc : 2 < Nat.card E)
    (hcore : B.pCoreIn 2 ≤ centralizer (E : Set Model)) (hmove : ⁅E,B⁆ = E)
    :
    ¬ 2 ∣ Nat.card (centralizer (B : Set Model)) := by
  intro heven
  obtain ⟨z,hz,h⟩ := exists_involution_centralizing_normalizing_two_group
    B (S : Subgroup Model) S.isPGroup' hSB heven
  let K := centralizer ({z} : Set Model)
  have hBK : B ≤ K := le_sup_left.trans h
  have hSK : (S : Subgroup Model) ≤ K := le_sup_right.trans h
  rcases centralizer_equiv_first_or_second z hz with hfirst | hsecond
  · obtain ⟨e⟩ := hfirst
    have hbound := Theory.GroupAction.fully_moved_eq_bot_of_overgroup_small_core_center
      S B E K hB hSB hSE hE hEB hcore hmove hBK hSK
      (centralizer_characteristic_two z hz)
    let eP : pCore 2 K ≃* pCore 2 First.centralizer :=
      (e.subgroupMap _).trans (MulEquiv.subgroupCongr (pCore_map_iso 2 e))
    have hcc := Nat.card_congr (centerCongr eP).toEquiv
    let := First.centralizer_twoCore_extraspecial
    rw [IsExtraspecial.center_order_p 2 (pCore 2 First.centralizer)] at hcc
    have he := hbound (by omega)
    rw [he,card_bot] at hc
    omega
  · obtain ⟨e⟩ := hsecond
    have hdiv : 2^21 ∣ Nat.card S := by
      have hd : 2^21 ∣ Nat.card Model := by rw [Cardinality.model_card]; norm_num
      rw [←(S : Subgroup Model).card_mul_index] at hd
      exact ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr S.not_dvd_index).pow_left 21
        |>.dvd_of_dvd_mul_right hd
    have hd := hdiv.trans (card_dvd_of_le hSK)
    rw [Nat.card_congr e.toEquiv,Second.ambient_card] at hd
    norm_num at hd

end Janko4
