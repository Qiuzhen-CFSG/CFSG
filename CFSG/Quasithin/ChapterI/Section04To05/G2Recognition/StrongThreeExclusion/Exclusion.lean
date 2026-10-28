module

public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.StrongThreeExclusion.OrderIdentity
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.StrongThreeExclusion.ConstituentDegrees
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.StrongThreeExclusion.CharacterColumns
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.StrongThreeExclusion.CharacterValues
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.StrongThreeExclusion.CharacterArithmetic
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.StrongThreeExclusion.OrderCandidates
public import Theory.Character.FiniteOrderTrace
public import Mathlib.RingTheory.Coprime.Basic

/-!
# Excluding the original strongly three-embedded branch

The original local configuration constructs five nonprincipal characters.
Their involution-pair identity, degree divisibility, column bound and
three-defect restriction give one of three group orders. The Sylow-normalizer
exclusions eliminate all three, so the original ambient order is divisible
by twenty-seven.
-/

public section
noncomputable section
attribute [local instance] Fintype.ofFinite
open scoped BigOperators
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
open Chapter14.Section04.DimensionFour LocalCharacters StrongThreeExclusion
variable {G : Type*} [Group G] [Finite G] (c : G2ThreeConfiguration G)

private theorem character_value_le_degree {χ : ClassFunction G}
    (hχ : IsIrreducibleCharacter χ) (e b : ℤ) (he : χ 1 = (e : ℂ))
    (t : G) (hb : χ t = (b : ℂ)) : b ≤ e := by
  obtain ⟨n,ρ,_,hr⟩ := hχ
  have hbound := finite_order_end_norm_trace_le_finrank (ρ t) (orderOf_pos t).ne'
    (by rw [←map_pow, pow_orderOf_eq_one, map_one])
  have hdeg : (n : ℂ) = (e : ℂ) := by simpa [hr, Representation.char_one] using he
  have hn : (n : ℤ) = e := by exact_mod_cast hdeg
  have hreal := (Complex.re_le_norm (χ t)).trans (by
    simpa [hr, Representation.character] using hbound)
  rw [hb, Complex.intCast_re] at hreal
  have hbe : b ≤ (n : ℤ) := by exact_mod_cast hreal
  exact hn ▸ hbe

include c in
/-- The genuine G₂(3) local configuration forces an ambient subgroup order
containing a factor twenty-seven. No recognition, character, or transporter
premise is assumed. -/
theorem cube_dvd_of_original_configuration : 3 ^ 3 ∣ Nat.card G := by
  by_contra hsmall
  obtain ⟨ε,ψ,μ,hε,hψ,hμ,hi,hd,hψ1,hμ1,hid⟩ := exists_original_ambient_characters c hsmall
  obtain ⟨t,ht,_⟩ := exists_involution_centralizer c
  let e : ℤ := hψ.degree
  have he : ψ 1 = (e : ℂ) := by exact_mod_cast hψ.degree_eq
  have hψchar : IsCharacter ψ := by obtain ⟨n,ρ,_,hr⟩ := hψ; exact ⟨n,ρ,hr⟩
  obtain ⟨b,hb,h8⟩ := exists_integer_involution_value_and_eight_dvd c hψchar e he t ht
  have hf : (hμ 0).degree = e + ε := by
    have h := localAlpha_identity_degree c 0 ε hε ψ (μ 0) (hid 0)
    rw [(hμ 0).degree_eq, he] at h
    exact_mod_cast h
  have hepos : 0 < e := by dsimp only [e]; exact_mod_cast hψ.degree_pos
  have hfpos : 0 < e + ε := by rw [←hf]; exact_mod_cast (hμ 0).degree_pos
  have hvalue (i : Fin 4) : μ i t = ((b + ε : ℤ) : ℂ) := by
    rw [localAlpha_identity_involution c i ε hε ψ (μ i) (hid i) t ht, hb, Int.cast_add]
  have horder : (Nat.card G : ℤ) * (e - b) ^ 2 = 5971968 * (e * (e + ε)) := by
    have h := original_character_order_identity c hsmall 0 ε hε ψ (μ 0) hψ (hμ 0) (hid 0) t ht
    rw [he, hb] at h
    exact_mod_cast h
  have hle : b ≤ e := character_value_le_degree hψ e b he t hb
  have hne : e - b ≠ 0 := by
    intro hz
    rw [hz] at horder
    have hp := mul_pos hepos hfpos
    nlinarith
  have hk : 0 < e - b := by omega
  have hcolumn : 1 + b ^ 2 + 4 * (b + ε) ^ 2 ≤ 576 := by
    have h := five_nonprincipal_column_bound ψ μ hψ hμ hi hd hψ1 hμ1 t
    rw [involution_centralizer_card c t ht, hb] at h
    simp only [hvalue, Complex.normSq_intCast, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul] at h
    norm_num only [pow_two] at ⊢
    exact_mod_cast h
  have hedvd : e ∣ (Nat.card G : ℤ) := by dsimp only [e]; exact_mod_cast hψ.degree_dvd_card
  have hfdvd : e + ε ∣ (Nat.card G : ℤ) := by
    rw [←hf]
    exact_mod_cast (hμ 0).degree_dvd_card
  have hcop : IsCoprime e (e + ε) := by
    rcases hε with rfl | rfl
    · exact IsCoprime.add_one_right_of_dvd dvd_rfl
    · simpa only [sub_eq_add_neg] using IsCoprime.sub_one_right_of_dvd (dvd_refl e)
  have hdegree := hcop.mul_dvd hedvd hfdvd
  have h128 : ¬ 128 ∣ Nat.card G := by
    intro hdvd
    let S : Sylow 2 G := default
    have h := S.pow_dvd_card_of_pow_dvd_card (n := 7) hdvd
    rw [ambient_sylow_card c S] at h
    norm_num at h
  obtain ⟨he9,hf9⟩ := original_constituent_degrees_not_nine c hsmall 0 ε hε ψ (μ 0)
    hψ (hμ 0) (hd 0) hψ1 (hμ1 0) (hid 0)
  have he9' : ¬ (9 : ℤ) ∣ e := by dsimp only [e]; exact_mod_cast he9
  have hf9' : ¬ (9 : ℤ) ∣ e + ε := by rw [←hf]; exact_mod_cast hf9
  have hcases := order_candidates_of_character_identities (Nat.card G) e b ε hε.symm
    hepos hfpos hk h8 hdegree horder hcolumn (ambient_order_divisible c) h128 hsmall he9' hf9'
  rcases hcases with h | h | h
  · exact card_ne_5664960_of_sylow_nine c hsmall h
  · exact card_ne_5132736_of_sylow_nine c hsmall h
  · exact card_ne_6874560_of_sylow_nine c hsmall h

end CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
