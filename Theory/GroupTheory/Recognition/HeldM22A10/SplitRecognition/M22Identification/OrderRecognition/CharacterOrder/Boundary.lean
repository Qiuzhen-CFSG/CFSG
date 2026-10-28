module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysisData
public import Theory.Character.IntegralRestriction
public import Theory.Character.IrreducibleDegrees
public import Theory.Character.DefectZeroVanishing

/-!
# Excluding the one-quarter boundary in Janko's order estimate

All nonidentity elements of the actual E16 are fused involutions. Restriction
therefore gives `16 ∣ χ(1) + 15 χ(z)`. If `χ(1) = 4 χ(z)^2`, reduction modulo
sixteen forces `16 ∣ χ(z)` and hence `128 ∣ χ(1)`. The supplied Sylow two-group
has order 128, so defect-zero vanishing gives `χ(z) = 0`, contradicting positive
degree. The integer value is explicit; the exceptional-character column formulas
supply it to the order argument.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), pp.14–15. The printed inequalities on p.15 are non-strict;
this argument justifies passing to strict inequalities in their small-ratio case.
-/

open scoped BigOperators
open Subgroup
namespace Theory.GroupTheory.HeldM22A10.M22Identification
open LocalModelDichotomy
namespace CharacterOrder
noncomputable section
attribute [local instance] Fintype.ofFinite

/-- Restricting an irreducible character to the actual E16 gives the
integral degree congruence used in Janko's arithmetic. -/
public theorem degree_congruence_mod_sixteen {G : Type*} [Group G] [Finite G] (D : LocalData G)
    (k : TwistedModel ≃* D.centralizer) (L : LocalAnalysisData D k)
    {χ : ClassFunction G} (hχ : IsIrreducibleCharacter χ) (t : ℤ)
    (ht : χ D.z = (t : ℂ)) :
    (16 : ℤ) ∣ (hχ.degree : ℤ) + 15 * t := by
  classical
  let E := CaseII.E D k
  let : IsElementaryAbelian 2 E := L.E_elementary
  have hc : IsCharacter χ := by
    obtain ⟨n, ρ, _, rfl⟩ := hχ
    exact ⟨n, ρ, rfl⟩
  have hf : IsClassFunction χ := by
    obtain ⟨n, ρ, _, rfl⟩ := hχ
    exact ρ.char_conj
  have he (a : E) : χ (a : G) = if a = 1 then χ 1 else χ D.z := by
    split_ifs with ha
    · simp [ha]
    · have hao : orderOf (a : G) = 2 := by
        apply orderOf_eq_prime
        · exact elemPow_eq_one_of_isElementaryAbelian (a : G) a.property
        · intro heq
          exact ha (Subtype.ext heq)
      obtain ⟨g, hg⟩ := isConj_iff.mp (L.involution_fusion a hao)
      rw [← hg]
      exact (hf a g).symm
  let : Fintype E := Fintype.ofFinite E
  have hs : (∑ a : E, χ (a : G)) = ((hχ.degree : ℤ) + 15 * t : ℤ) := by
    simp_rw [he]
    simp [Finset.sum_ite, Finset.filter_ne', Finset.filter_eq', ← Nat.card_eq_fintype_card,
      show Nat.card E = 16 from L.E_card, hχ.degree_eq, ht]
  have hd := hc.card_dvd_restriction_sum E.subtype _ hs
  simpa only [show Nat.card E = 16 from L.E_card, Nat.cast_ofNat] using hd

private theorem sixteen_dvd_of_quadratic_congruence (t : ℤ) (ht : 16 ∣ 4 * t ^ 2 + 15 * t) : 16 ∣ t := by
  have hm := Int.emod_eq_zero_of_dvd ht
  have he : (4 * (t % 16) ^ 2 + 15 * (t % 16)) % 16 = 0 := by
    simpa only [Int.add_emod, Int.mul_emod, pow_two, Int.emod_emod] using hm
  have h0 : 0 ≤ t % 16 := Int.emod_nonneg _ (by norm_num)
  have h16 : t % 16 < 16 := Int.emod_lt_of_pos _ (by norm_num)
  have hz : t % 16 = 0 := by
    interval_cases h : t % 16 <;> omega
  exact Int.dvd_of_emod_eq_zero hz


/-- The equation associated to a ratio of one quarter is incompatible
with the restriction congruence and ordinary defect-zero vanishing. -/
public theorem degree_ne_four_mul_square {G : Type*} [Group G] [Finite G] (D : LocalData G)
    (k : TwistedModel ≃* D.centralizer) (L : LocalAnalysisData D k)
    {χ : ClassFunction G} (hχ : IsIrreducibleCharacter χ) (t : ℤ)
    (ht : χ D.z = (t : ℂ)) :
    (hχ.degree : ℤ) ≠ 4 * t ^ 2 := by
  intro he
  have hr := degree_congruence_mod_sixteen D k L hχ t ht
  rw [he] at hr
  obtain ⟨s, hs⟩ := sixteen_dvd_of_quadratic_congruence t hr
  have hd : (128 : ℤ) ∣ (hχ.degree : ℤ) := by
    refine ⟨8 * s ^ 2, ?_⟩
    rw [he, hs]
    ring
  have hd' : Nat.card D.sylow ∣ hχ.degree := by
    rw [D.sylow_card]
    exact_mod_cast hd
  have hv := OrdinaryCharacter.value_eq_zero_of_sylow_card_dvd_degree
    D.sylow hχ hχ.degree_eq hd' D.z (by rw [D.z_order])
  have ht0 : t = 0 := by exact_mod_cast ht.symm.trans hv
  have hn := hχ.degree_pos
  simp only [ht0, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, mul_zero, Nat.cast_eq_zero] at he
  omega

/-- The equality boundary in Janko's three ratio inequalities is impossible. -/
public theorem ratio_ne_one_quarter {G : Type*} [Group G] [Finite G] (D : LocalData G)
    (k : TwistedModel ≃* D.centralizer) (L : LocalAnalysisData D k)
    {χ : ClassFunction G} (hχ : IsIrreducibleCharacter χ) (t : ℤ)
    (ht : χ D.z = (t : ℂ)) :
    (t : ℚ) ^ 2 / hχ.degree ≠ 1 / 4 := by
  intro he
  have hd : (hχ.degree : ℚ) ≠ 0 := by exact_mod_cast hχ.degree_pos.ne'
  have hh : (hχ.degree : ℚ) = 4 * (t : ℚ) ^ 2 := by
    field_simp at he
    linarith
  apply degree_ne_four_mul_square D k L hχ t ht
  exact_mod_cast hh

end
end CharacterOrder
end Theory.GroupTheory.HeldM22A10.M22Identification
