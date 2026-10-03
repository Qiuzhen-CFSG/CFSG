module

public import Theory.GroupTheory.PGroup.NormalEightNormLifting
public import Theory.GroupTheory.SpecificGroups.UnequalCyclicFourNormControl
public import Mathlib.Data.ZMod.Basic

/-!
# Fourth-root action bounds for an unequal cyclic factor and C₄

A norm-control subgroup of the automorphism model is disjoint from every
ambient elementary conjugation image, by `NormalEightNormLifting`. Thus a
coordinate bound for elementary subgroups avoiding that subgroup gives the
required bound on fourth-root actions. This module transports the coordinate
certificate to the ambient group and proves both the full conjugation image
bound and its fourth-root restriction.

For `C_(2^n) × C₄`, the intended control subgroup consists of the eight maps
`(x,y) ↦ ((1 + 2^(n-1)s)x + 2^(n-1)b y, y + 2c x)` with binary `s,b,c`.
The imported coordinate certificate proves that elementary automorphism
subgroups fixing involutions and avoiding these maps have order at most four.

Source: MacWilliams, *On 2-groups with no normal abelian subgroups of rank 3*,
Trans. AMS 150 (1970), §1.2; the norm correction is proved in the imported
module and does not assume an abelian full ambient conjugation image.
-/

open Subgroup

namespace IsPGroup

/-- A norm-control certificate and a coordinate count bound the full
conjugation image in the smaller-factor-C₄ case. -/
public theorem conj_image_card_le_four_of_cyclic_four_norm_control
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hno : ¬ ∃ U : Subgroup P, U.Normal ∧ IsElementaryAbelian 2 U ∧ 8 ≤ Nat.card U)
    (hZ : Nat.card (omega₁ (center P) (p := 2)) = 4)
    (D : Subgroup P) [D.Normal] [IsMulCommutative D]
    (hD : centralizer (D : Set P) ≤ D)
    (n : ℕ)
    (e : D ≃* (Multiplicative (ZMod (2^n)) × Multiplicative (ZMod 4)))
    (T : InvolutionNormControl
      (Multiplicative (ZMod (2^n)) × Multiplicative (ZMod 4)))
    (hbound : ∀ B : Subgroup (MulAut
        (Multiplicative (ZMod (2^n)) × Multiplicative (ZMod 4))),
      IsElementaryAbelian 2 B →
      (∀ f ∈ B, ∀ x, x ^ 2 = 1 → f x = x) →
      B ⊓ T.subgroup = ⊥ → Nat.card B ≤ 4)
    (A : Subgroup P) [IsElementaryAbelian 2 A] :
    Nat.card ((MulAut.conjNormal : P →* MulAut D).comp A.subtype).range ≤ 4 := by
  let V := Multiplicative (ZMod (2^n)) × Multiplicative (ZMod 4)
  let c : P →* MulAut D := MulAut.conjNormal
  let F : P →* MulAut V := (MulAut.congr e).toMonoidHom.comp c
  let H := (F.comp A.subtype).range
  let : IsElementaryAbelian 2 H := {
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr fun x => by
      apply Subtype.ext
      obtain ⟨a, ha⟩ := x.property
      change (x : MulAut V) ^ 2 = 1
      rw [← ha]
      change F (a : P) ^ 2 = 1
      rw [← map_pow, elemPow_eq_one_of_isElementaryAbelian (a : P) a.property, map_one] }
  have hfix : ∀ f ∈ H, ∀ x : V, x ^ 2 = 1 → f x = x := by
    rintro f ⟨a, rfl⟩ x hx
    change e (c a (e.symm x)) = x
    have hs : (e.symm x) ^ 2 = 1 := by rw [← map_pow, hx, map_one]
    rw [conjNormal_fixed_of_square_eq_one_of_no_normal_eight hno hZ D hD a _ hs]
    exact e.apply_symm_apply x
  have hb := hbound H inferInstance hfix
    (conj_image_disjoint_norm_control hP hno hZ D hD e T A)
  change Nat.card (((MulAut.congr e).toMonoidHom.comp (c.comp A.subtype)).range) ≤ 4 at hb
  rw [MonoidHom.range_comp, card_map_of_injective (MulAut.congr e).injective] at hb
  exact hb

/-- The same certificate bounds restriction to fourth roots. -/
public theorem card_omegaTwo_image_le_four_of_cyclic_four_norm_control
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hno : ¬ ∃ U : Subgroup P, U.Normal ∧ IsElementaryAbelian 2 U ∧ 8 ≤ Nat.card U)
    (hZ : Nat.card (omega₁ (center P) (p := 2)) = 4)
    (D : Subgroup P) [D.Normal] [IsMulCommutative D]
    (hD : centralizer (D : Set P) ≤ D)
    (n : ℕ)
    (e : D ≃* (Multiplicative (ZMod (2^n)) × Multiplicative (ZMod 4)))
    (T : InvolutionNormControl
      (Multiplicative (ZMod (2^n)) × Multiplicative (ZMod 4)))
    (hbound : ∀ B : Subgroup (MulAut
        (Multiplicative (ZMod (2^n)) × Multiplicative (ZMod 4))),
      IsElementaryAbelian 2 B →
      (∀ f ∈ B, ∀ x, x ^ 2 = 1 → f x = x) →
      B ⊓ T.subgroup = ⊥ → Nat.card B ≤ 4)
    (A : Subgroup P) [IsElementaryAbelian 2 A] :
    Nat.card ((omegaTwoConjugation D).comp A.subtype).range ≤ 4 := by
  have hb := conj_image_card_le_four_of_cyclic_four_norm_control
    hP hno hZ D hD n e T hbound A
  let : (omega D (p := 2) 2).Characteristic := omega_characteristic D 2
  change Nat.card (((MulAut.characteristic (omega D (p := 2) 2)).comp
    ((MulAut.conjNormal : P →* MulAut D).comp A.subtype)).range) ≤ 4
  rw [MonoidHom.range_comp]
  exact (Nat.le_of_dvd Nat.card_pos (card_map_dvd _ _)).trans hb

/-- In the smaller-factor-C₄ case, every elementary subgroup has full
conjugation image of order at most four. The exclusion of normal elementary
subgroups of order eight forces disjointness from the norm-control subgroup. -/
public theorem conj_image_card_le_four_of_cyclic_four
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hno : ¬ ∃ U : Subgroup P, U.Normal ∧ IsElementaryAbelian 2 U ∧ 8 ≤ Nat.card U)
    (hZ : Nat.card (omega₁ (center P) (p := 2)) = 4)
    (D : Subgroup P) [D.Normal] [IsMulCommutative D]
    (hD : centralizer (D : Set P) ≤ D)
    (n : ℕ) (hn : 3 ≤ n)
    (e : D ≃* (Multiplicative (ZMod (2^n)) × Multiplicative (ZMod 4)))
    (A : Subgroup P) [IsElementaryAbelian 2 A] :
    Nat.card ((MulAut.conjNormal : P →* MulAut D).comp A.subtype).range ≤ 4 := by
  obtain ⟨T, hbound⟩ := UnequalCyclicFourNormControl.certificate n hn
  exact conj_image_card_le_four_of_cyclic_four_norm_control hP hno hZ D hD n e T hbound A

/-- In the smaller-factor-C₄ case, restriction of an elementary subgroup's
conjugation action to the fourth roots has image of order at most four. -/
public theorem card_omegaTwo_image_le_four_of_cyclic_four
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hno : ¬ ∃ U : Subgroup P, U.Normal ∧ IsElementaryAbelian 2 U ∧ 8 ≤ Nat.card U)
    (hZ : Nat.card (omega₁ (center P) (p := 2)) = 4)
    (D : Subgroup P) [D.Normal] [IsMulCommutative D]
    (hD : centralizer (D : Set P) ≤ D)
    (n : ℕ) (hn : 3 ≤ n)
    (e : D ≃* (Multiplicative (ZMod (2^n)) × Multiplicative (ZMod 4)))
    (A : Subgroup P) [IsElementaryAbelian 2 A] :
    Nat.card ((omegaTwoConjugation D).comp A.subtype).range ≤ 4 := by
  obtain ⟨T, hbound⟩ := UnequalCyclicFourNormControl.certificate n hn
  exact card_omegaTwo_image_le_four_of_cyclic_four_norm_control hP hno hZ D hD n e T hbound A

end IsPGroup
