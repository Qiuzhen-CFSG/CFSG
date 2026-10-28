module

public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.AmbientFusion
public import Theory.Character.RealOrderFourIntegral
public import Theory.Character.ConstantRestriction

/-!
# Integer values and the elementary-eight degree congruence

Every ordinary character has integer values at involutions. In the actual
G₂(3) configuration all involutions are conjugate, so restriction to the
marked elementary eight gives degree congruent to that value modulo eight.
-/

public section
noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
open Chapter14.Section04.DimensionFour
namespace StrongThreeExclusion
variable {G : Type*} [Group G] [Finite G] (c : G2ThreeConfiguration G)
include c

theorem character_eight_dvd_degree_sub {χ : ClassFunction G} (hχ : IsCharacter χ)
    (a b : ℤ) (hdegree : χ 1 = (a : ℂ)) (t : G) (ht : orderOf t = 2)
    (hvalue : χ t = (b : ℂ)) : (8 : ℤ) ∣ a - b := by
  let E := c.V.map c.M.subtype
  have hE : Nat.card E = 8 :=
    (card_map_of_injective c.M.subtype_injective).trans (V_card c)
  have hclass : IsClassFunction χ := by
    obtain ⟨n, ρ, rfl⟩ := hχ
    exact ρ.char_conj
  have hd := hχ.card_dvd_degree_sub_of_constant E a b hdegree (by
    rintro _ ⟨v, hv, rfl⟩ hne
    have : IsElementaryAbelian 2 c.V := V_elementary c
    have hvpow : (v : G) ^ 2 = 1 := by
      simpa only [map_pow, map_one, Subgroup.subtype_apply] using
        congrArg c.M.subtype (elemPow_eq_one_of_isElementaryAbelian (p := 2) v hv)
    have hvorder : orderOf (v : G) = 2 := orderOf_eq_prime hvpow hne
    obtain ⟨g, hg⟩ := isConj_iff.mp (involutions_conjugate c (v : G) t hvorder ht)
    rw [← hg] at hvalue
    exact (hclass _ _).symm.trans hvalue)
  simpa only [hE, Nat.cast_ofNat] using hd

/-- The integer involution value and its actual elementary-eight congruence
are consequences of the source configuration and an ordinary character. -/
theorem exists_integer_involution_value_and_eight_dvd {χ : ClassFunction G}
    (hχ : IsCharacter χ) (a : ℤ) (hdegree : χ 1 = (a : ℂ))
    (t : G) (ht : orderOf t = 2) :
    ∃ b : ℤ, χ t = (b : ℂ) ∧ (8 : ℤ) ∣ a - b := by
  have ht2 : t ^ 2 = 1 := by simpa only [ht] using pow_orderOf_eq_one t
  have ht4 : t ^ 4 = 1 := by
    rw [show 4 = 2 * 2 from rfl, pow_mul, ht2, one_pow]
  have hti : IsConj t t⁻¹ := by
    rw [inv_eq_self_of_orderOf_eq_two ht]
  obtain ⟨b, hb⟩ := hχ.exists_int_of_fourth_power_of_isConj_inv t ht4 hti
  exact ⟨b, hb, character_eight_dvd_degree_sub c hχ a b hdegree t ht hb⟩

end StrongThreeExclusion
end CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
