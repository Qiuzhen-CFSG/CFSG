module

public import Stellmacher.Recognition.LyonsU3Four.LocalFiveQuarticExtensionValues
public import Theory.Character.PrimePowerTrace

/-!
# Odd-order values of rational local quartic extensions

Every rational degree-four extension of a Sylow quartic character takes value
minus one on nonidentity odd-order elements. Such elements have order five.
To exclude them from the representation kernel, split an element into its
Sylow and complement factors: their images have coprime periods, so both
images must be trivial. The complement generator would then act trivially on
the Sylow central quotient, contradicting its fixed-point-free action there.
Schur's rational trace spacing in dimension four completes the calculation.

Source: Lyons, *A Characterization of the Group U₃(4)* (1972), Lemma 4, p. 381.
-/

public section
namespace Stellmacher.Recognition.LyonsU3Four
noncomputable section
attribute [local instance] Fintype.ofFinite Classical.propDecidable
variable {G : Type*} [Group G] [Finite G] {S : Sylow 2 G}

private theorem sylow_kernel_central
    {z : QuarticCentralIndex S} {θ : ConjClassFunction S}
    (hθ : IsSylowQuarticCharacter S z θ)
    (α : FiveComplement →* MulAut S)
    (σ : Representation ℂ (LocalFiveGroup S α) (Fin 4 → ℂ))
    (hres : ∀ s : S, σ.character (SemidirectProduct.inl s) = θ (ConjClasses.mk s))
    (s : S) (hs : σ (SemidirectProduct.inl s) = 1) : s ∈ Subgroup.center S := by
  by_contra hc
  have hv := hres s
  rw [hθ.vanishes hc] at hv
  simp [Representation.character, hs] at hv

/-- No nonidentity odd-order element lies in the kernel of a degree-four extension.
Neither rationality nor irreducibility of the extension is needed here. -/
theorem IsSylowQuarticCharacter.extension_odd_ne_one
    {z : QuarticCentralIndex S} {θ : ConjClassFunction S}
    (hθ : IsSylowQuarticCharacter S z θ) (h : SylowStructure S)
    (β : MulAut S) (hβ : orderOf β = 15)
    (α : FiveComplement →* MulAut S)
    (hα : α (Multiplicative.ofAdd 1) = β ^ (3 : ℕ))
    (σ : Representation ℂ (LocalFiveGroup S α) (Fin 4 → ℂ))
    (hres : ∀ s : S, σ.character (SemidirectProduct.inl s) = θ (ConjClasses.mk s))
    (u : LocalFiveGroup S α) (hu : Odd (orderOf u)) (hu1 : u ≠ 1) : σ u ≠ 1 := by
  intro hku
  have hu5 := localFive_odd_order_eq_five h α u hu hu1
  have hS64 (s : S) : s ^ (64 : ℕ) = 1 := by
    rw [← h.card]
    exact pow_card_eq_one'
  have hC5 (t : FiveComplement) : t ^ (5 : ℕ) = 1 := by
    simpa [FiveComplement, Nat.card_eq_fintype_card] using (pow_card_eq_one' (x := t))
  have hr : u.right ≠ 1 := by
    intro hr
    have he : u = SemidirectProduct.inl u.left := by
      simpa [hr] using (SemidirectProduct.inl_left_mul_inr_right u).symm
    have hp : u ^ (64 : ℕ) = 1 := by rw [he, ← map_pow, hS64, map_one]
    have hd := orderOf_dvd_of_pow_eq_one hp
    rw [hu5] at hd
    norm_num at hd
  -- Work in the group of units to compare the two factor images.
  let f := σ.toHomUnits
  have hfu : f u = 1 := Units.ext hku
  have he : f (SemidirectProduct.inr u.right) = (f (SemidirectProduct.inl u.left))⁻¹ := by
    have hm : f (SemidirectProduct.inl u.left) * f (SemidirectProduct.inr u.right) = 1 := by
      rw [← map_mul, SemidirectProduct.inl_left_mul_inr_right, hfu]
    exact eq_inv_of_mul_eq_one_right hm
  have hp5 : f (SemidirectProduct.inr u.right) ^ (5 : ℕ) = 1 := by
    rw [← map_pow, ← map_pow, hC5, map_one, map_one]
  have hp64 : f (SemidirectProduct.inr u.right) ^ (64 : ℕ) = 1 := by
    rw [he, inv_pow, ← map_pow, ← map_pow, hS64, map_one, map_one, inv_one]
  have hfr : f (SemidirectProduct.inr u.right) = 1 := by
    have hh := pow_gcd_eq_one.mpr ⟨hp5, hp64⟩
    simpa using hh
  have hgen : f (SemidirectProduct.inr (Multiplicative.ofAdd (1 : ZMod 5))) = 1 := by
    let : Fact (Nat.Prime 5) := ⟨by decide⟩
    have hcard : Nat.card FiveComplement = 5 := by
      simp [FiveComplement, Nat.card_eq_fintype_card]
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp
      (mem_zpowers_of_prime_card hcard hr (g' := Multiplicative.ofAdd (1 : ZMod 5)))
    rw [← hk, map_zpow, map_zpow, hfr, one_zpow]
  -- Trivial complement image forces every displacement into the Sylow center.
  have hdisp (s : S) : (β ^ (3 : ℕ)) s * s⁻¹ ∈ Subgroup.center S := by
    apply sylow_kernel_central hθ α σ hres
    have hconj : f (SemidirectProduct.inl ((β ^ (3 : ℕ)) s)) =
        f (SemidirectProduct.inl s) := by
      rw [← hα, SemidirectProduct.inl_aut]
      simp only [map_mul, map_inv, hgen, one_mul, inv_one, mul_one]
    have hd : f (SemidirectProduct.inl ((β ^ (3 : ℕ)) s * s⁻¹)) = 1 := by
      rw [map_mul, map_mul, hconj, ← map_mul, ← map_mul, mul_inv_cancel, map_one, map_one]
    exact congrArg Units.val hd
  have hquot (x : S ⧸ Subgroup.center S) : x = 1 := by
    apply order_fifteen_cube_quotient_fixed_eq_one S h β hβ
    obtain ⟨s, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center S) x
    rw [← map_pow, Subgroup.quotientAut_apply_mk]
    apply mul_inv_eq_one.mp
    rw [← map_inv, ← map_mul]
    exact (QuotientGroup.eq_one_iff _).mpr (hdisp s)
  have hcard : Nat.card (S ⧸ Subgroup.center S) = 1 :=
    Nat.card_eq_one_iff_exists.mpr ⟨1, hquot⟩
  rw [center_quotient_card S h] at hcard
  norm_num at hcard

/-- A rational degree-four extension has value minus one at every nonidentity
odd-order element. -/
theorem IsSylowQuarticCharacter.extension_odd_value
    {z : QuarticCentralIndex S} {θ : ConjClassFunction S}
    (hθ : IsSylowQuarticCharacter S z θ) (h : SylowStructure S)
    (β : MulAut S) (hβ : orderOf β = 15)
    (α : FiveComplement →* MulAut S)
    (hα : α (Multiplicative.ofAdd 1) = β ^ (3 : ℕ))
    (σ : Representation ℂ (LocalFiveGroup S α) (Fin 4 → ℂ))
    (hres : ∀ s : S, σ.character (SemidirectProduct.inl s) = θ (ConjClasses.mk s))
    (hrat : ∀ x, ∃ q : ℚ, σ.character x = q)
    (u : LocalFiveGroup S α) (hu : Odd (orderOf u)) (hu1 : u ≠ 1) :
    σ.character u = -1 := by
  have hu5 := localFive_odd_order_eq_five h α u hu hu1
  have hpow : σ u ^ (5 ^ (1 : ℕ)) = 1 := by
    simp only [pow_one, ← hu5, ← map_pow, pow_orderOf_eq_one, map_one]
  obtain ⟨j, hj, hv⟩ := prime_power_trace_spacing_of_rational (σ u)
    (by decide : Nat.Prime 5) hpow
    (hθ.extension_odd_ne_one h β hβ α hα σ hres u hu hu1) (hrat u)
  have hj0 : j = 0 := by simpa using hj
  norm_num [hj0] at hv
  exact hv
end
end Stellmacher.Recognition.LyonsU3Four
