module

public import Theory.Character.ModularBlock.RestrictionPairing
public import Glauberman.SuzukiCharacterization.NormalizerBasics
public import Glauberman.SuzukiCharacterization.ElementColumnNorm
public import Glauberman.SuzukiCharacterization.NormalizerConjugacyFibers

/-!
# The principal-block restriction pairing

Glauberman's Lemma 3.2 pairs principal-block restriction columns by averaging
over the normalizer. The nonidentity diagonal norm is |C_P(x)|, and the
normalizer conjugacy-fiber count converts the resulting column kernel into
this average. The degree-zero hypothesis removes the identity column.
The formula does not require irreducible character orbit representatives.

Source: Glauberman, *A Characterization of the Suzuki Groups* (1968),
equations (3.2)--(3.5), pp. 83--84.
-/

public section
noncomputable section
open scoped BigOperators
attribute [local instance] Fintype.ofFinite Classical.propDecidable
namespace Glauberman.SuzukiCharacterization
open Subgroup ModularBlock PrincipalBlockConstruction RestrictionColumn
variable {G : Type*} [Group G] [Finite G]

/-- Lemma 3.2 from its nonidentity column norm and normalizer fiber count. -/
theorem restriction_pairing_of_column_norm_of_fiber_card
    (P : Sylow 2 G) (d : PrincipalCongruenceBlockData G)
    (hnorm : ∀ x : P, x ≠ 1 →
      ∑ i ∈ d.block, d.chi i (ConjClasses.mk (x : G)) *
        star (d.chi i (ConjClasses.mk (x : G))) =
          (Nat.card (centralizer ({x} : Set P)) : ℂ))
    (hfibers : ∀ x : P, x ≠ 1 → ∀ y : P,
      Nat.card P * Nat.card {n : normalizer (P : Set G) //
        (P : Subgroup G).normalizerMonoidHom n x = y} =
      if IsConj (x : G) (y : G) then
        Nat.card (normalizerSylowCore P) * Nat.card (centralizer ({x} : Set P)) else 0)
    (θ η : ClassFunction P) (hθ : IsGeneralizedCharacter θ)
    (hη : IsGeneralizedCharacter η) (hzero : θ 1 = 0) :
    ∑ i ∈ d.block, (coefficient d P θ hθ i : ℂ) *
      (coefficient d P η hη i : ℂ) =
    (Nat.card (normalizerSylowCore P) : ℂ)⁻¹ *
      ∑ n : normalizer (P : Set G),
        scalarProduct P (fun x => η ((P : Subgroup G).normalizerMonoidHom n x)) θ := by
  classical
  have hP : (Nat.card P : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.card_pos (α := P)).ne'
  have hK : (Nat.card (normalizerSylowCore P) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.card_pos (α := normalizerSylowCore P)).ne'
  have havg (x : P) (hx : x ≠ 1) :
      (Nat.card P : ℂ)⁻¹ * (∑ y : P,
        if IsConj (x : G) (y : G) then
          η y * (Nat.card (centralizer ({x} : Set P)) : ℂ) else 0) =
      (Nat.card (normalizerSylowCore P) : ℂ)⁻¹ *
        ∑ n : normalizer (P : Set G), η ((P : Subgroup G).normalizerMonoidHom n x) := by
    have hs : (∑ n : normalizer (P : Set G),
        η ((P : Subgroup G).normalizerMonoidHom n x)) =
        ∑ y : P, (Nat.card {n : normalizer (P : Set G) //
          (P : Subgroup G).normalizerMonoidHom n x = y} : ℂ) * η y := by
      rw [← Fintype.sum_fiberwise' (fun n : normalizer (P : Set G) =>
        (P : Subgroup G).normalizerMonoidHom n x) η]
      simp [Nat.card_eq_fintype_card]
    rw [hs, Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _
    have hc : (Nat.card P : ℂ) *
        (Nat.card {n : normalizer (P : Set G) //
          (P : Subgroup G).normalizerMonoidHom n x = y} : ℂ) =
        if IsConj (x : G) (y : G) then
          (Nat.card (normalizerSylowCore P) : ℂ) *
            (Nat.card (centralizer ({x} : Set P)) : ℂ) else 0 := by
      exact_mod_cast hfibers x hx y
    by_cases hxy : IsConj (x : G) (y : G)
    · rw [if_pos hxy] at hc ⊢
      field_simp
      linear_combination -η y * hc
    · rw [if_neg hxy] at hc ⊢
      have hf := (mul_eq_zero.mp hc).resolve_left hP
      rw [hf]
      simp
  rw [coefficient_pairing_eq_of_column_norm d P P.isPGroup'
    (fun x => Nat.card (centralizer ({x} : Set P))) hnorm θ η hθ hη hzero]
  simp_rw [scalarProduct]
  rw [← Finset.mul_sum, Finset.sum_comm]
  rw [mul_left_comm]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : x = 1
  · simp [hx, hzero]
  rw [havg x hx, ← Finset.sum_mul]
  ring

/-- Lemma 3.2: principal-block restriction columns pair by normalizer averaging.
Fusion control and local normal complements supply the nonidentity column
norm and the conjugacy-fiber count. -/
theorem restriction_pairing
    (P : Sylow 2 G) (h : Hypotheses P) (d : PrincipalCongruenceBlockData G)
    (θ η : ClassFunction P) (hθ : IsGeneralizedCharacter θ)
    (hη : IsGeneralizedCharacter η) (hzero : θ 1 = 0) :
    ∑ i ∈ d.block, (coefficient d P θ hθ i : ℂ) *
      (coefficient d P η hη i : ℂ) =
    (Nat.card (normalizerSylowCore P) : ℂ)⁻¹ *
      ∑ n : normalizer (P : Set G),
        scalarProduct P (fun x => η ((P : Subgroup G).normalizerMonoidHom n x)) θ := by
  exact restriction_pairing_of_column_norm_of_fiber_card P d
    (h.principalBlock_column_norm P d)
    (fun x hx y => by
      by_cases hxy : IsConj (x : G) (y : G)
      · simpa only [if_pos hxy] using h.normalizer_conjugacy_fiber_card P x hx y
      · simpa only [if_neg hxy] using h.normalizer_conjugacy_fiber_card P x hx y)
    θ η hθ hη hzero

end Glauberman.SuzukiCharacterization
