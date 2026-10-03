module

public import Stellmacher.Recognition.LyonsU3Four.LocalFiveQuarticData
public import Stellmacher.Recognition.LyonsU3Four.OrderFourFusionFromAutomizer
public import Theory.Character.SeparatingIrreducibles
public import Theory.Representation.Quotient

/-!
# The three degree-four Sylow characters

For each nonidentity central element `z` of Lyons's Sylow subgroup, there is a
genuine irreducible character with values four at `1` and `z`, minus four at
the other two central elements, and zero off the center.

Inflate an irreducible character of `S / ⟨z⟩` that distinguishes the image of
another central involution from the identity. Such a character exists by
completeness. Schur's lemma and the Klein-four center give its central signs.
The order-fifteen automorphism supplies central-coset fusion, which forces
vanishing off the center. The norm-one identity then gives `4 n² = 64`, so the
degree is four. No character table or extraspecial representation is assumed.

Source: Lyons, *A Characterization of the Group U₃(4)* (1972), pp. 373 and 381,
Lemma 4; `refs/original/n-group-global/odd-core-rank-two-source/
lyons-u3four-1972-ams-wayback.pdf`.
-/

open scoped BigOperators
noncomputable section
attribute [local instance] Fintype.ofFinite Classical.propDecidable
namespace Stellmacher.Recognition.LyonsU3Four

private theorem central_involution {G V : Type*} [Group G] [AddCommGroup V]
    [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) [Representation.IsIrreducible ρ]
    {z : G} (hz : z ∈ Subgroup.center G) (hz2 : z ^ 2 = 1) :
    ρ z = 1 ∨ ρ z = -1 := by
  let : Nontrivial V := Subrepresentation.irreducible_module_nontrivial ρ
  let f := Representation.IntertwiningMap.centralMul (ρ := ρ) z hz
  obtain ⟨a, ha⟩ :=
    (Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
      (ρ := ρ)).surjective f
  have hscalar : ρ z = a • (1 : Module.End ℂ V) :=
    (congrArg Representation.IntertwiningMap.toLinearMap ha).symm
  have hpow : a ^ 2 = 1 := by
    apply FaithfulSMul.algebraMap_injective ℂ (Module.End ℂ V)
    rw [map_one, Algebra.algebraMap_eq_smul_one]
    calc
      _ = (ρ z) ^ 2 := by rw [hscalar, smul_pow, one_pow]
      _ = 1 := by rw [← map_pow, hz2, map_one]
  rcases sq_eq_one_iff.mp hpow with ha | ha
  · left; simp [hscalar, ha]
  · right; simp [hscalar, ha]

/-- Every nonidentity central element indexes a genuine Sylow quartic character,
with its complete value formula. -/
public theorem exists_sylowQuarticCharacter {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (h : SylowStructure S) (β : MulAut S) (hβ : orderOf β = 15)
    (z : QuarticCentralIndex S) :
    ∃ θ : ConjClassFunction S, IsSylowQuarticCharacter S z θ := by
  classical
  let : Fintype S := Fintype.ofFinite S
  let : IsElementaryAbelian 2 (Subgroup.center S) := h.center_elementary
  let : Nontrivial (Subgroup.center S) :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [h.center_card]; omega)
  let : IsKleinFour (Subgroup.center S) :=
    ⟨h.center_card, IsElementaryAbelian.exponent_eq_prime⟩
  have hz1 : z.1.1 ≠ (1 : S) := fun he => z.2 (Subtype.ext he)
  have hz2 : orderOf z.1.1 = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian z.1.1 z.1.2) hz1
  let N : Subgroup S := Subgroup.zpowers z.1.1
  have hNZ : N ≤ Subgroup.center S := Subgroup.zpowers_le.mpr z.1.2
  let : N.Normal := ⟨by
    intro n hn g
    have hc := Subgroup.mem_center_iff.mp (hNZ hn) g
    simpa only [hc, mul_inv_cancel_right] using hn⟩
  have hNcard : Nat.card N = 2 := (Nat.card_zpowers _).trans hz2
  have hNmem (s : S) : s ∈ N ↔ s = 1 ∨ s = z.1.1 := by
    rw [mem_zpowers_iff_mem_range_orderOf, hz2]
    constructor
    · intro hs
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hs
      have hklt : k < 2 := Finset.mem_range.mp hk
      interval_cases k <;> simp
    · rintro (rfl | rfl)
      · exact Finset.mem_image.mpr ⟨0, by simp, by simp⟩
      · exact Finset.mem_image.mpr ⟨1, by simp, by simp⟩
  obtain ⟨w, hwZ, hwN⟩ : ∃ w : S, w ∈ Subgroup.center S ∧ w ∉ N := by
    by_contra! hall
    have heq := le_antisymm hNZ hall
    have hc := h.center_card
    rw [← heq, hNcard] at hc
    omega
  let q := QuotientGroup.mk' N
  have hqw : q w ≠ 1 := fun he => hwN ((QuotientGroup.eq_one_iff w).mp he)
  obtain ⟨χ, hχ, hχw⟩ := exists_irreducibleConjCharacter_ne_degree hqw
  obtain ⟨n, σ, rfl⟩ := hχ.1
  have hσ : Representation.IsIrreducible σ :=
    (irreducible_iff_character_norm_one σ).mpr hχ.2
  let ρ : Representation ℂ S (Fin n → ℂ) := σ.comp q
  have hρ : Representation.IsIrreducible ρ :=
    (Representation.irreducible_comp_surjective_iff q
      (QuotientGroup.mk'_surjective N) σ).mpr hσ
  let : Representation.IsIrreducible ρ := hρ
  have hρN (s : S) (hs : s ∈ N) : ρ s = 1 := by
    change σ (q s) = 1
    have hq : q s = 1 := (QuotientGroup.eq_one_iff s).mpr hs
    rw [hq, map_one]
  have hρz : ρ z.1.1 = 1 := hρN _ (Subgroup.mem_zpowers _)
  have hρw : ρ w = -1 := by
    apply (central_involution ρ hwZ
      (elemPow_eq_one_of_isElementaryAbelian w hwZ)).resolve_left
    intro he
    apply hχw
    change LinearMap.trace ℂ (Fin n → ℂ) (σ (q w)) =
      LinearMap.trace ℂ (Fin n → ℂ) (σ 1)
    rw [map_one]
    exact congrArg (LinearMap.trace ℂ (Fin n → ℂ)) he
  have hρcentral (s : S) (hsZ : s ∈ Subgroup.center S) (hsN : s ∉ N) :
      ρ s = -1 := by
    by_cases hsw : s = w
    · simpa [hsw] using hρw
    have hs := not_or.mp ((hNmem s).not.mp hsN)
    have hw := not_or.mp ((hNmem w).not.mp hwN)
    have he : (⟨s, hsZ⟩ : Subgroup.center S) = z.1 * ⟨w, hwZ⟩ :=
      IsKleinFour.eq_mul_of_ne_all z.2
        (fun he => hw.1 (congrArg Subtype.val he))
        (fun he => hw.2 (congrArg Subtype.val he).symm)
        (fun he => hs.1 (congrArg Subtype.val he))
        (fun he => hs.2 (congrArg Subtype.val he))
        (fun he => hsw (congrArg Subtype.val he))
    have he' := congrArg Subtype.val he
    change s = z.1.1 * w at he'
    rw [he', map_mul, hρz, hρw, one_mul]
  have hzero (s : S) (hs : s ∉ Subgroup.center S) : ρ.character s = 0 := by
    have hf := order_four_center_coset_isConj_of_order_fifteen S h β hβ s
      ((order_four_iff_not_mem_center S h s).mpr hs) ⟨w, hwZ⟩
    have he : ρ.character s = ρ.character (s * w) :=
      congrArg (characterClassFunction ρ) (ConjClasses.mk_eq_mk_iff_isConj.mpr hf)
    have hm : ρ.character (s * w) = -ρ.character s := by
      have hm : ρ (s * w) = -ρ s := by
        rw [map_mul, hρw]
        ext v i
        simp
      simp only [Representation.character, hm, map_neg]
    rw [hm] at he
    linear_combination (1 / 2 : ℂ) * he
  have hval (s : S) : ρ.character s =
      if s ∈ N then (n : ℂ) else if s ∈ Subgroup.center S then -(n : ℂ) else 0 := by
    by_cases hsN : s ∈ N
    · simp [hsN, Representation.character, hρN s hsN, LinearMap.trace_one]
    · by_cases hsZ : s ∈ Subgroup.center S
      · simp [hsN, hsZ, Representation.character, hρcentral s hsZ hsN,
          LinearMap.trace_one]
      · simp [hsN, hsZ, hzero s hsZ]
  have hnorm := (irreducible_iff_character_norm_one ρ).mp hρ
  unfold classFunctionInner at hnorm
  change (Nat.card S : ℂ)⁻¹ * ∑ s : S,
    ρ.character s * star (ρ.character s) = 1 at hnorm
  have hterm (s : S) : ρ.character s * star (ρ.character s) =
      if s ∈ Subgroup.center S then (n : ℂ) ^ 2 else 0 := by
    rw [hval]
    by_cases hsN : s ∈ N
    · simp [hsN, hNZ hsN, pow_two]
    · by_cases hsZ : s ∈ Subgroup.center S <;> simp [hsN, hsZ, pow_two]
  simp_rw [hterm] at hnorm
  have hsum : (∑ s : S, if s ∈ Subgroup.center S then (n : ℂ) ^ 2 else 0) =
      4 * (n : ℂ) ^ 2 := by
    have hc : (Finset.univ.filter (fun s : S => s ∈ Subgroup.center S)).card = 4 := by
      rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
      exact h.center_card
    simp only [Finset.sum_ite, Finset.sum_const, nsmul_eq_mul, mul_zero, add_zero]
    congr 1
    norm_cast
  rw [hsum, h.card] at hnorm
  have hn : n = 4 := by
    have he : (n : ℂ) ^ 2 = 16 := by linear_combination 16 * hnorm
    have he' : n ^ 2 = 16 := by exact_mod_cast he
    nlinarith
  refine ⟨characterClassFunction ρ, ⟨⟨n, ρ, rfl⟩,
    (irreducible_iff_character_norm_one ρ).mp hρ⟩, ?_⟩
  intro s
  change ρ.character s = _
  rw [hval]
  simp only [hNmem, hn, Nat.cast_ofNat]
  split_ifs <;> rfl

end Stellmacher.Recognition.LyonsU3Four
