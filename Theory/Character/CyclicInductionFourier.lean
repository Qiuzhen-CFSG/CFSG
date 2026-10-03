module

public import Theory.Character.AbelianLinearCharacters
public import Theory.Character.Induction
public import Theory.Character.Integrality
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Cyclic Fourier sums of induced ordinary characters

A retraction from a subgroup of the centralizer of `s` onto its cyclic subgroup,
fixing prime-regular elements, supplies ordinary linear characters by inflation.
Weighting these characters by their inverse values at `s`, cyclic Fourier
orthogonality reduces the induction sum to the conjugators fixing `s`.
The resulting value is `orderOf s` times the relative centralizer index, and
all coefficients are algebraic integers.

This is the character-theoretic local construction in Serre,
*Linear Representations of Finite Groups*, Chapter 10.
-/

public section
noncomputable section
open scoped BigOperators IsMulCommutative
attribute [local instance] Fintype.ofFinite Classical.propDecidable

private theorem linear_character {A : Type*} [Group A] (χ : A →* ℂ) :
    IsCharacter (χ : A → ℂ) := by
  obtain ⟨n, ρ, _, hρ⟩ := χ.isLinearCharacter.1
  exact ⟨n, ρ, hρ⟩

private theorem linear_integral_inv {A : Type*} [Group A] [Finite A]
    (χ : A →* ℂ) (x : A) : IsIntegral ℤ (χ x)⁻¹ := by
  obtain ⟨n, ρ, hρ⟩ := linear_character χ
  have h := character_value_isIntegral ρ x⁻¹
  rw [← hρ] at h
  simpa using h

private theorem cyclic_fourier {G : Type*} [Group G] [Fintype G] (s : G)
    (y : Subgroup.zpowers s) :
    (∑ χ : Subgroup.zpowers s →* ℂ,
      (χ ⟨s, Subgroup.mem_zpowers s⟩)⁻¹ * χ y) =
      if (y : G) = s then (orderOf s : ℂ) else 0 := by
  let s' : Subgroup.zpowers s := ⟨s, Subgroup.mem_zpowers s⟩
  have he : s'⁻¹ * y = 1 ↔ (y : G) = s := by
    rw [inv_mul_eq_one]
    exact ⟨fun h => (congrArg Subtype.val h).symm, fun h => Subtype.ext h.symm⟩
  simpa only [map_mul, map_inv, he, Nat.card_zpowers] using
    (AbelianLinearCharacters.sum_apply (s'⁻¹ * y))

private theorem induced_fourier_sum {G : Type*} [Group G] [Fintype G]
    (p : ℕ) (s : G) (hs : ¬ p ∣ orderOf s)
    (H : Subgroup G) (hHC : H ≤ Subgroup.centralizer ({s} : Set G)) (hsH : s ∈ H)
    (r : H →* Subgroup.zpowers s)
    (hret : ∀ x : H, ¬ p ∣ orderOf (x : G) → (r x : G) = (x : G)) :
    (∑ χ : Subgroup.zpowers s →* ℂ,
      (χ ⟨s, Subgroup.mem_zpowers s⟩)⁻¹ * inducedClassFunction H (χ.comp r) s) =
      ((orderOf s * H.relIndex (Subgroup.centralizer ({s} : Set G)) : ℕ) : ℂ) := by
  let C := Subgroup.centralizer ({s} : Set G)
  have hconj (x : G) : orderOf (x⁻¹ * s * x) = orderOf s := by
    simpa using (MulEquiv.orderOf_eq (MulAut.conj x⁻¹) s)
  have hfix (x : G) : x⁻¹ * s * x = s ↔ x ∈ C := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      have := congrArg (fun y => x * y) h
      simpa [mul_assoc] using this.symm
    · intro h
      calc
        x⁻¹ * s * x = x⁻¹ * (s * x) := mul_assoc _ _ _
        _ = x⁻¹ * (x * s) := by rw [h]
        _ = s := by simp
  have hinner (x : G) :
      (∑ χ : Subgroup.zpowers s →* ℂ,
        (χ ⟨s, Subgroup.mem_zpowers s⟩)⁻¹ *
          (if hx : x⁻¹ * s * x ∈ H then χ (r ⟨_, hx⟩) else 0)) =
        if x ∈ C then (orderOf s : ℂ) else 0 := by
    by_cases hx : x⁻¹ * s * x ∈ H
    · simp only [dif_pos hx]
      rw [cyclic_fourier, hret ⟨_, hx⟩ (by simpa only [hconj] using hs), hfix]
    · have hc : x ∉ C := fun hc => hx (by rw [(hfix x).mpr hc]; exact hsH)
      simp [hx, hc]
  have hcard : Nat.card H * H.relIndex C = Nat.card C := by
    simpa only [Subgroup.relIndex_bot_left] using
      Subgroup.relIndex_mul_relIndex (⊥ : Subgroup G) H C bot_le hHC
  have hsum : (∑ x : G, if x ∈ C then (orderOf s : ℂ) else 0) =
      (Nat.card C : ℂ) * (orderOf s : ℂ) := by
    rw [← Finset.sum_filter]
    rw [Finset.sum_subtype (p := fun x => x ∈ C) (F := Fintype.ofFinite C) _ (by simp) (fun _ : G => (orderOf s : ℂ))]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      ← Nat.card_eq_fintype_card]
  have hH : (Nat.card H : ℂ) ≠ 0 := by
    exact_mod_cast Nat.card_pos (α := H) |>.ne'
  calc
    _ = (Nat.card H : ℂ)⁻¹ * ∑ x : G,
          ∑ χ : Subgroup.zpowers s →* ℂ,
            (χ ⟨s, Subgroup.mem_zpowers s⟩)⁻¹ *
              (if hx : x⁻¹ * s * x ∈ H then χ (r ⟨_, hx⟩) else 0) := by
      simp only [inducedClassFunction, MonoidHom.coe_comp, Function.comp_apply]
      simp_rw [mul_left_comm _ (Nat.card H : ℂ)⁻¹, Finset.mul_sum]
      rw [Finset.sum_comm]
    _ = (Nat.card H : ℂ)⁻¹ * ((Nat.card C : ℂ) * (orderOf s : ℂ)) := by
      simp_rw [hinner]
      rw [hsum]
    _ = _ := by
      rw [← hcard]
      simp only [Nat.cast_mul]
      simp only [← mul_assoc]
      rw [inv_mul_cancel₀ hH, one_mul]
      exact mul_comm _ _

/-- Inflated cyclic linear characters give an algebraic-integral combination of
induced values equal to the cyclic order times the relative centralizer index. -/
theorem cyclicInductionFourier {G : Type*} [Group G] [Fintype G]
    (p : ℕ) (_hp : p.Prime) (s : G) (hs : ¬ p ∣ orderOf s)
    (H : Subgroup G) (hHC : H ≤ Subgroup.centralizer ({s} : Set G)) (hsH : s ∈ H)
    (r : H →* Subgroup.zpowers s)
    (hret : ∀ x : H, ¬ p ∣ orderOf (x : G) → (r x : G) = (x : G)) :
    ∃ (n : ℕ) (φ : Fin n → ClassFunction H) (a : Fin n → ℂ),
      (∀ i, IsCharacter (φ i)) ∧ (∀ i, IsIntegral ℤ (a i)) ∧
      (∑ i, a i * inducedClassFunction H (φ i) s) =
        ((orderOf s * H.relIndex (Subgroup.centralizer ({s} : Set G)) : ℕ) : ℂ) := by
  let e := (Fintype.equivFin (Subgroup.zpowers s →* ℂ)).symm
  refine ⟨_, (fun i => (e i).comp r),
    (fun i => ((e i) ⟨s, Subgroup.mem_zpowers s⟩)⁻¹), ?_, ?_, ?_⟩
  · intro i
    exact linear_character _
  · intro i
    exact linear_integral_inv _ _
  · rw [e.sum_comp (fun χ => (χ ⟨s, Subgroup.mem_zpowers s⟩)⁻¹ *
        inducedClassFunction H (χ.comp r) s)]
    exact induced_fourier_sum p s hs H hHC hsH r hret
