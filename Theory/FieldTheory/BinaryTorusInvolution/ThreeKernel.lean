module

public import Theory.FieldTheory.BinaryTorusInvolution

/-!
# Binary torus actions modulo a three-group kernel

A quadratic field involution has displacement image of order `2^n + 1`.
If it fixes the three-residual after a map with three-group kernel, the
image and kernel argument makes this whole displacement group a three-group.
For `n > 1` this is equivalent to `n = 3`. The converse is also proved.
Fixation modulo the kernel is preserved under every positive power of a
field automorphism, allowing arbitrary two-power actors to be treated.

Source: Aschbacher–Smith, proof of 13.8.20, printed p.954. This is a field
theorem; identifying the matrix Borel action is a separate obligation.
-/

@[expose] public section

open Subgroup
namespace FiniteField.BinaryTorusInvolution
variable {F T : Type*} [Field F] [Finite F] [Group T]

theorem displacement_isThreeGroup_of_fixed_residual_mod_kernel
    (σ : F ≃+* F) (f : Fˣ →* T) (hker : IsPGroup 3 f.ker)
    (hfix : ∀ u ∈ pResidual 3 Fˣ, f (Units.map σ.toMonoidHom u) = f u) :
    IsPGroup 3 (displacement σ).range := by
  let d := f.comp (displacement σ)
  have hk : pResidual 3 Fˣ ≤ d.rangeRestrict.ker := by
    intro u hu
    apply Subtype.ext
    change f (Units.map σ.toMonoidHom u * u⁻¹) = 1
    rw [map_mul, map_inv, hfix u hu, mul_inv_cancel]
  let g := QuotientGroup.lift (pResidual 3 Fˣ) d.rangeRestrict hk
  have hg : Function.Surjective g := by
    intro v
    obtain ⟨u, hu⟩ := d.rangeRestrict_surjective v
    exact ⟨QuotientGroup.mk u, hu⟩
  have hd : IsPGroup 3 d.range :=
    (isPGroup_quotient_pResidual 3).of_surjective g hg
  apply (hd.comap_of_ker_isPGroup f hker).to_le
  rintro _ ⟨u, rfl⟩
  exact ⟨u, rfl⟩

theorem degree_three_of_fixed_residual_mod_kernel
    (σ : F ≃+* F) {n : ℕ} (hn : 1 < n)
    (hF : Nat.card F = 2 ^ (2 * n))
    (hσ : ∀ x : F, σ x = x ^ (2 ^ n))
    (f : Fˣ →* T) (hker : IsPGroup 3 f.ker)
    (hfix : ∀ u ∈ pResidual 3 Fˣ, f (Units.map σ.toMonoidHom u) = f u) :
    n = 3 := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ :=
    (displacement_isThreeGroup_of_fixed_residual_mod_kernel σ f hker hfix).exists_card_eq
  rw [card_displacement σ (by omega) hF hσ] at hk
  rcases Nat.BinaryTorusParity.plus_three_power_degree (by omega : 0 < n) hk with h | h
  · omega
  · exact h

omit [Finite F] in
theorem fixed_residual_mod_kernel_pow (σ : F ≃+* F) (f : Fˣ →* T)
    (hfix : ∀ u ∈ pResidual 3 Fˣ, f (Units.map σ.toMonoidHom u) = f u)
    (k : ℕ) :
    ∀ u ∈ pResidual 3 Fˣ, f (Units.map (σ ^ k).toMonoidHom u) = f u := by
  induction k with
  | zero => intro u _; rfl
  | succ k ih =>
    intro u hu
    have hmem : Units.map (σ ^ k).toMonoidHom u ∈ pResidual 3 Fˣ :=
      map_pResidual_le 3 (Units.map (σ ^ k).toMonoidHom)
        (mem_map_of_mem _ hu)
    have he : Units.map (σ ^ (k + 1)).toMonoidHom u =
        Units.map σ.toMonoidHom (Units.map (σ ^ k).toMonoidHom u) := by
      apply Units.ext
      change (σ ^ (k + 1)) (u : F) = σ ((σ ^ k) (u : F))
      rw [pow_succ']
      rfl
    rw [he, hfix _ hmem, ih u hu]

theorem fixed_residual_of_degree_three (σ : F ≃+* F)
    (hF : Nat.card F = 2 ^ (2 * 3))
    (hσ : ∀ x : F, σ x = x ^ (2 ^ 3)) :
    ∀ u ∈ pResidual 3 Fˣ, Units.map σ.toMonoidHom u = u := by
  have hd : IsPGroup 3 (displacement σ).range := IsPGroup.of_card (n := 2) (by
    rw [card_displacement σ (by decide : 0 < 3) hF hσ]
    norm_num)
  have hq : IsPGroup 3 (Fˣ ⧸ (displacement σ).ker) :=
    hd.of_equiv (QuotientGroup.quotientKerEquivRange (displacement σ)).symm
  have hk : pResidual 3 Fˣ ≤ (displacement σ).ker := sInf_le ⟨inferInstance, hq⟩
  intro u hu
  exact mul_inv_eq_one.mp (hk hu)

theorem fixed_residual_mod_kernel_iff_degree_three
    (σ : F ≃+* F) {n : ℕ} (hn : 1 < n)
    (hF : Nat.card F = 2 ^ (2 * n))
    (hσ : ∀ x : F, σ x = x ^ (2 ^ n))
    (f : Fˣ →* T) (hker : IsPGroup 3 f.ker) :
    (∀ u ∈ pResidual 3 Fˣ, f (Units.map σ.toMonoidHom u) = f u) ↔ n = 3 := by
  refine ⟨degree_three_of_fixed_residual_mod_kernel σ hn hF hσ f hker, ?_⟩
  rintro rfl u hu
  exact congrArg f (fixed_residual_of_degree_three σ hF hσ u hu)

end FiniteField.BinaryTorusInvolution
