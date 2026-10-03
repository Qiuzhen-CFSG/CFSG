module

public import Stellmacher.Recognition.LyonsU3Four.LocalFiveQuarticData

/-!
# Local input for extending the Sylow quartic characters

The complement fixes the Sylow center pointwise, so the prescribed quartic
character is invariant under its entire action and is rational-valued.
In every degree-four extension, the central elements act by the prescribed
signs: an involutory operator of trace four is the identity, and one of trace
minus four is minus the identity. Thus the central multiplication formula
does not require a separate choice of extension. Nonidentity odd-order
elements of the local group have order five.

Source: Lyons, *A Characterization of the Group U₃(4)* (1972), Lemma 4,
p. 381; the central scalar calculation makes explicit the kernel argument.
-/

public section
namespace Stellmacher.Recognition.LyonsU3Four
noncomputable section
attribute [local instance] Fintype.ofFinite Classical.propDecidable

variable {G : Type*} [Group G] [Finite G] {S : Sylow 2 G}

/-- Every element of the complement fixes the center pointwise. -/
theorem localFive_action_fixes_center (h : SylowStructure S)
    (β : MulAut S) (hβ : orderOf β = 15)
    (α : FiveComplement →* MulAut S)
    (hα : α (Multiplicative.ofAdd 1) = β ^ (3 : ℕ))
    (t : FiveComplement) (c : Subgroup.center S) : α t c = c := by
  have ht : (Multiplicative.ofAdd (1 : ZMod 5)) ^ t.toAdd.val = t := by
    change Multiplicative.ofAdd (t.toAdd.val • (1 : ZMod 5)) = t
    simp
  rw [← ht, map_pow, hα]
  have hc := order_fifteen_cube_fixes_center S h β hβ c
  induction t.toAdd.val with
  | zero => rfl
  | succ n hn => rw [pow_succ, MulAut.mul_apply, hc, hn]

/-- The given Sylow character is invariant under the entire complement. -/
theorem IsSylowQuarticCharacter.invariant_under_complement
    {z : QuarticCentralIndex S} {θ : ConjClassFunction S}
    (hθ : IsSylowQuarticCharacter S z θ) (h : SylowStructure S)
    (β : MulAut S) (hβ : orderOf β = 15)
    (α : FiveComplement →* MulAut S)
    (hα : α (Multiplicative.ofAdd 1) = β ^ (3 : ℕ))
    (t : FiveComplement) (s : S) :
    θ (ConjClasses.mk (α t s)) = θ (ConjClasses.mk s) :=
  hθ.invariant_of_fixes_center (α t) (localFive_action_fixes_center h β hβ α hα t) s

/-- The prescribed Sylow value table is rational-valued. -/
theorem IsSylowQuarticCharacter.rational
    {z : QuarticCentralIndex S} {θ : ConjClassFunction S}
    (hθ : IsSylowQuarticCharacter S z θ) (s : S) :
    ∃ q : ℚ, θ (ConjClasses.mk s) = q := by
  rw [hθ.value]
  split_ifs
  · exact ⟨4, by norm_num⟩
  · exact ⟨-4, by norm_num⟩
  · exact ⟨0, by norm_num⟩

/-- An arbitrary degree-four extension has the required central scalar action. -/
theorem IsSylowQuarticCharacter.extension_central_scalar
    {z : QuarticCentralIndex S} {θ : ConjClassFunction S}
    (hθ : IsSylowQuarticCharacter S z θ) (h : SylowStructure S)
    (α : FiveComplement →* MulAut S)
    (σ : Representation ℂ (LocalFiveGroup S α) (Fin 4 → ℂ))
    (hres : ∀ s : S, σ.character (SemidirectProduct.inl s) = θ (ConjClasses.mk s))
    (w : QuarticCentralIndex S) :
    σ (SemidirectProduct.inl w.1.1) = quarticCentralSign z w • 1 := by
  have hw1 : w.1.1 ≠ (1 : S) := fun hh => w.2 (Subtype.ext hh)
  have hw2 : w.1.1 ^ 2 = (1 : S) := by
    let := h.center_elementary
    exact elemPow_eq_one_of_isElementaryAbelian w.1.1 w.1.2
  have hpow : σ (SemidirectProduct.inl w.1.1) ^ 2 = 1 := by
    rw [← map_pow, ← map_pow, hw2, map_one, map_one]
  by_cases hzw : z = w
  · subst w
    simp only [quarticCentralSign_self, one_smul]
    apply finite_order_end_eq_one_of_trace_eq_finrank _ (by decide : (2 : ℕ) ≠ 0) hpow
    change σ.character _ = _
    rw [hres, hθ.value]
    simp
  · have hwz : w.1.1 ≠ z.1.1 := by
      intro he
      exact hzw (Subtype.ext (Subtype.ext he.symm))
    have hv : σ.character (SemidirectProduct.inl w.1.1) = -4 := by
      rw [hres, hθ.value]
      simp [hw1, hwz, w.1.2]
    have hneg : -σ (SemidirectProduct.inl w.1.1) = 1 := by
      apply finite_order_end_eq_one_of_trace_eq_finrank _ (by decide : (2 : ℕ) ≠ 0)
      · exact (neg_mul_neg (σ (SemidirectProduct.inl w.1.1))
          (σ (SemidirectProduct.inl w.1.1))).trans (by simpa only [pow_two] using hpow)
      · rw [map_neg]
        change -σ.character _ = _
        rw [hv]
        norm_num
    have he := congrArg Neg.neg hneg
    rw [quarticCentralSign, if_neg hzw]
    change σ (SemidirectProduct.inl w.1.1) = (-1 : ℂ) • (1 : Module.End ℂ (Fin 4 → ℂ))
    rw [neg_one_smul ℂ (1 : Module.End ℂ (Fin 4 → ℂ))]
    exact (neg_neg _).symm.trans he

/-- Taking traces gives central multiplication on every element of the extension. -/
theorem IsSylowQuarticCharacter.extension_central_mul
    {z : QuarticCentralIndex S} {θ : ConjClassFunction S}
    (hθ : IsSylowQuarticCharacter S z θ) (h : SylowStructure S)
    (α : FiveComplement →* MulAut S)
    (σ : Representation ℂ (LocalFiveGroup S α) (Fin 4 → ℂ))
    (hres : ∀ s : S, σ.character (SemidirectProduct.inl s) = θ (ConjClasses.mk s))
    (w : QuarticCentralIndex S) (x : LocalFiveGroup S α) :
    σ.character (SemidirectProduct.inl w.1.1 * x) =
      quarticCentralSign z w * σ.character x := by
  unfold Representation.character
  rw [map_mul, hθ.extension_central_scalar h α σ hres w, smul_mul_assoc, one_mul,
    map_smul]
  rfl

omit [Finite G] in
/-- Every nonidentity odd-order element has order five. -/
theorem localFive_odd_order_eq_five (h : SylowStructure S)
    (α : FiveComplement →* MulAut S)
    (u : LocalFiveGroup S α) (hu : Odd (orderOf u)) (hu1 : u ≠ 1) : orderOf u = 5 := by
  have hd : orderOf u ∣ 64 * 5 := by
    have hd := orderOf_dvd_natCard u
    rw [localFiveGroup_card S h α] at hd
    exact hd
  have hc : (orderOf u).Coprime 64 := by
    simpa using hu.coprime_two_right.pow_right 6
  have hd5 : orderOf u ∣ 5 := hc.dvd_of_dvd_mul_left hd
  exact ((Nat.dvd_prime (by decide : Nat.Prime 5)).mp hd5).resolve_left
    (fun he => hu1 (orderOf_eq_one_iff.mp he))

end
end Stellmacher.Recognition.LyonsU3Four
