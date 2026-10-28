module

public import Theory.GroupTheory.PGroup.NormalFourAbelianBase
public import Theory.GroupTheory.PGroup.HomocyclicElementaryFourTorsion
public import Theory.GroupTheory.PGroup.HomocyclicLargeBaseFourTorsionKernel
public import Theory.GroupTheory.NormalizingInvolutionCard
public import Theory.ElementaryAbelian.Join
public import Theory.GroupTheory.PGroup.NormalEightCenterTwoC4SquareAction

/-!
# Homocyclic action reductions over a normal four

An elementary subgroup containing the first omega of a normal abelian base
fixes every involution of that base. For a base of exponent two the action
is trivial. For exponent at least eight the homocyclic matrix theorem bounds
the action by four as soon as fourth roots detect the action.

The structural kernel theorem may be supplied only in the presence of an
elementary sixteen containing the four: an elementary actor of order at most
sixteen already has image of order at most four, while a larger actor contains
such a sixteen. This module supplies that extraction and the exact bridge.
The involution-only fourth-root kernel proves the large-exponent branch
unconditionally. No assertion about arbitrary elements of that kernel is needed.
The exponent-four branch is a separate structural problem.

Source context: Janko–Thompson, Math. Z. 113 (1970), Theorem 1.1, printed p.385,
`refs/original/n-group-global/odd-core-rank-two-source/janko-thompson-1970-gdz.pdf`.
-/

open Subgroup
namespace IsPGroup

/-- An elementary overgroup of the first omega fixes all involutions in the base. -/
public theorem conjNormal_fixed_of_elementary_overgroup_omega
    {P : Type*} [Group P] (W D B : Subgroup P) [D.Normal]
    [IsElementaryAbelian 2 B]
    (hO : (omega₁ D (p := 2)).map D.subtype = W) (hWB : W ≤ B)
    (b : B) (d : D) (hd : d ^ 2 = 1) : MulAut.conjNormal (b : P) d = d := by
  have hdW : (d : P) ∈ W := by
    rw [← hO]
    exact ⟨d, subset_closure (by simpa using hd), rfl⟩
  apply Subtype.ext
  change (b : P) * (d : P) * (b : P)⁻¹ = d
  rw [(B.le_centralizer b.property d (hWB hdW)).symm, mul_inv_cancel_right]

private theorem exists_double_inside_elementary
    {P : Type*} [Group P] [Finite P] (U B : Subgroup P)
    [IsElementaryAbelian 2 U] [IsElementaryAbelian 2 B]
    (hUB : U ≤ B) (hlt : Nat.card U < Nat.card B) :
    ∃ V : Subgroup P, IsElementaryAbelian 2 V ∧ U ≤ V ∧ V ≤ B ∧
      Nat.card V = 2 * Nat.card U := by
  have hnot : ¬ B ≤ U := by
    intro h
    have hc := card_le_of_le h
    omega
  obtain ⟨b, hb, hbU⟩ := SetLike.not_le_iff_exists.mp hnot
  have hb2 := elemPow_eq_one_of_isElementaryAbelian (p := 2) b hb
  have hbC : b ∈ centralizer (U : Set P) :=
    (B.le_centralizer.trans (centralizer_le hUB)) hb
  let : IsElementaryAbelian 2 (zpowers b) :=
    IsElementaryAbelian.zpowers_of_pow_eq_one hb2
  let V := U ⊔ zpowers b
  let : IsElementaryAbelian 2 V :=
    IsElementaryAbelian.sup_of_le_centralizer (zpowers_le.mpr hbC)
  exact ⟨V, inferInstance, le_sup_left, sup_le hUB (zpowers_le.mpr hb),
    card_sup_zpowers_of_normalizing_involution U b hb2 hbU
      ((centralizer_le_normalizer _) hbC)⟩

/-- A sufficiently large elementary overgroup of a four contains an elementary
sixteen over that same four. -/
public theorem exists_elementary_sixteen_between_four
    {P : Type*} [Group P] [Finite P] (W B : Subgroup P)
    [IsElementaryAbelian 2 W] [IsElementaryAbelian 2 B]
    (hW : Nat.card W = 4) (hWB : W ≤ B) (hB : 16 ≤ Nat.card B) :
    ∃ A : Subgroup P, IsElementaryAbelian 2 A ∧ Nat.card A = 16 ∧ W ≤ A ∧ A ≤ B := by
  obtain ⟨U, hUe, hWU, hUB, hUc⟩ :=
    exists_double_inside_elementary W B hWB (by omega)
  let : IsElementaryAbelian 2 U := hUe
  obtain ⟨A, hAe, hUA, hAB, hAc⟩ :=
    exists_double_inside_elementary U B hUB (by omega)
  exact ⟨A, hAe, by omega, hWU.trans hUA, hAB⟩

/-- If the elementary overgroup has order at most sixteen, its action has order
at most four, since the omega four belongs to the kernel. -/
public theorem conj_image_card_le_four_of_elementary_overgroup_card_le_sixteen
    {P : Type*} [Group P] [Finite P]
    (W D B : Subgroup P) [D.Normal] [IsMulCommutative D]
    [IsElementaryAbelian 2 B] (hW : Nat.card W = 4)
    (hO : (omega₁ D (p := 2)).map D.subtype = W) (hWB : W ≤ B)
    (hB : Nat.card B ≤ 16) :
    Nat.card ((MulAut.conjNormal : P →* MulAut D).comp B.subtype).range ≤ 4 := by
  let f := (MulAut.conjNormal : P →* MulAut D).comp B.subtype
  have hWD : W ≤ D := hO ▸ map_subtype_le _
  have hk : W.subgroupOf B ≤ f.ker := by
    intro b hb
    apply MonoidHom.mem_ker.mpr
    apply MulEquiv.ext
    intro d
    apply Subtype.ext
    change (b : P) * (d : P) * (b : P)⁻¹ = d
    rw [(D.le_centralizer (hWD (show (b : P) ∈ W from hb)) d d.property).symm, mul_inv_cancel_right]
  have hkc : 4 ≤ Nat.card f.ker := by
    have hh := card_le_of_le hk
    rwa [Nat.card_congr (subgroupOfEquivOfLe hWB).toEquiv, hW] at hh
  have hc := f.ker.card_mul_index
  rw [index_ker] at hc
  change Nat.card f.range ≤ 4
  nlinarith

/-- For cyclic factors of order two, an elementary overgroup acts trivially. -/
public theorem conj_image_card_eq_one_of_binary_base_overgroup
    {P : Type*} [Group P] [Finite P]
    (W D B : Subgroup P) [D.Normal] [IsElementaryAbelian 2 B]
    (hO : (omega₁ D (p := 2)).map D.subtype = W) (hWB : W ≤ B)
    (e : D ≃* (Multiplicative (ZMod (2 ^ 1)) × Multiplicative (ZMod (2 ^ 1)))) :
    Nat.card ((MulAut.conjNormal : P →* MulAut D).comp B.subtype).range = 1 := by
  have hs (d : D) : d ^ 2 = 1 := by
    apply e.injective
    rw [map_pow, map_one]
    apply Prod.ext
    · change Multiplicative.ofAdd (2 • (e d).1.toAdd) = 1
      simp only [nsmul_eq_mul, show ((2 : ℕ) : ZMod (2 ^ 1)) = 0 by decide, zero_mul]
      rfl
    · change Multiplicative.ofAdd (2 • (e d).2.toAdd) = 1
      simp only [nsmul_eq_mul, show ((2 : ℕ) : ZMod (2 ^ 1)) = 0 by decide, zero_mul]
      rfl
  have hf : ((MulAut.conjNormal : P →* MulAut D).comp B.subtype).range = ⊥ := by
    apply MonoidHom.range_eq_bot_iff.mpr
    apply MonoidHom.ext
    intro b
    apply MulEquiv.ext
    intro d
    exact conjNormal_fixed_of_elementary_overgroup_omega W D B hO hWB b d (hs d)
  rw [hf]
  exact Nat.card_unique

/-- The checked matrix count applies once fourth roots detect the action.
Only the acting elementary subgroup is required to fix the omega four. -/
public theorem conj_image_card_le_four_of_homocyclic_overgroup_of_fourth_root_kernel
    {P : Type*} [Group P] [Finite P]
    (W D B : Subgroup P) [D.Normal] [IsMulCommutative D] [IsElementaryAbelian 2 B]
    (hO : (omega₁ D (p := 2)).map D.subtype = W) (hWB : W ≤ B)
    (n : ℕ) (hn : 3 ≤ n)
    (e : D ≃* (Multiplicative (ZMod (2 ^ n)) × Multiplicative (ZMod (2 ^ n))))
    (hker : ∀ b : B, (∀ d : D, d ^ 4 = 1 → MulAut.conjNormal (b : P) d = d) →
      (b : P) ∈ D) :
    Nat.card ((MulAut.conjNormal : P →* MulAut D).comp B.subtype).range ≤ 4 := by
  let f := (MulAut.conjNormal : P →* MulAut D).comp B.subtype
  let : IsElementaryAbelian 2 f.range := {
    toIsMulCommutative := by infer_instance
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (by
      intro a
      apply Subtype.ext
      obtain ⟨b, hb⟩ := a.property
      change (a : MulAut D) ^ 2 = 1
      rw [← hb, ← map_pow]
      have hb2 : b ^ 2 = 1 := Subtype.ext
        (elemPow_eq_one_of_isElementaryAbelian (b : P) b.property)
      rw [hb2, map_one]) }
  apply HomocyclicFourTorsion.card_le_four_of_homocyclic_elementary_four_torsion n hn e f.range
  · rintro a ⟨b, rfl⟩ d hd
    exact conjNormal_fixed_of_elementary_overgroup_omega W D B hO hWB b d hd
  · rintro a ⟨b, rfl⟩ hfix
    have hbD := hker b hfix
    apply MulEquiv.ext
    intro d
    apply Subtype.ext
    change (b : P) * (d : P) * (b : P)⁻¹ = d
    rw [(D.le_centralizer hbD d d.property).symm, mul_inv_cancel_right]

/-- It suffices to know the fourth-root kernel whenever an elementary sixteen
containing the four exists. This removes the size restriction on the actor. -/
public theorem conj_image_card_le_four_of_homocyclic_overgroup_of_sixteen_kernel
    {P : Type*} [Group P] [Finite P]
    (W D : Subgroup P) [IsElementaryAbelian 2 W] [D.Normal] [IsMulCommutative D]
    (hW : Nat.card W = 4) (hO : (omega₁ D (p := 2)).map D.subtype = W)
    (n : ℕ) (hn : 3 ≤ n)
    (e : D ≃* (Multiplicative (ZMod (2 ^ n)) × Multiplicative (ZMod (2 ^ n))))
    (hker : ∀ A : Subgroup P, IsElementaryAbelian 2 A → Nat.card A = 16 → W ≤ A →
      ∀ g ∈ centralizer (W : Set P),
        (∀ d : D, d ^ 4 = 1 → MulAut.conjNormal g d = d) → g ∈ D)
    (B : Subgroup P) [IsElementaryAbelian 2 B] (hWB : W ≤ B) :
    Nat.card ((MulAut.conjNormal : P →* MulAut D).comp B.subtype).range ≤ 4 := by
  by_cases hB : Nat.card B ≤ 16
  · exact conj_image_card_le_four_of_elementary_overgroup_card_le_sixteen W D B hW hO hWB hB
  obtain ⟨A, hAe, hA, hWA, -⟩ :=
    exists_elementary_sixteen_between_four W B hW hWB (by omega)
  apply conj_image_card_le_four_of_homocyclic_overgroup_of_fourth_root_kernel W D B hO hWB n hn e
  intro b hfix
  exact hker A hAe hA hWA b ((B.le_centralizer.trans (centralizer_le hWB)) b.property) hfix

/-- For cyclic factors of order at least eight, the involution-only kernel
theorem suffices to bound every elementary overgroup's action by four. -/
public theorem conj_image_card_le_four_of_large_homocyclic_overgroup
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hZ : Nat.card (omega₁ (center P) (p := 2)) = 2)
    (hno : ¬ ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W : Subgroup P) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (D : Subgroup P) [D.Normal] [IsMulCommutative D]
    (hDC : centralizer (D : Set P) ≤ D)
    (hO : (omega₁ D (p := 2)).map D.subtype = W)
    (n : ℕ) (hn : 3 ≤ n)
    (e : D ≃* (Multiplicative (ZMod (2 ^ n)) × Multiplicative (ZMod (2 ^ n))))
    (B : Subgroup P) [IsElementaryAbelian 2 B] (hWB : W ≤ B) :
    Nat.card ((MulAut.conjNormal : P →* MulAut D).comp B.subtype).range ≤ 4 := by
  apply conj_image_card_le_four_of_homocyclic_overgroup_of_fourth_root_kernel
    W D B hO hWB n hn e
  intro b hfix
  exact involution_mem_of_homocyclic_fixing_four_torsion hP hZ hno W hW D hDC hO
    n hn e b (elemPow_eq_one_of_isElementaryAbelian (b : P) b.property) hfix

/-- All equal-factor exponents other than four satisfy the action bound.
Uniqueness of the normal four is not needed for these branches. -/
public theorem conj_image_card_le_four_of_homocyclic_overgroup_of_exponent_ne_four
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hZ : Nat.card (omega₁ (center P) (p := 2)) = 2)
    (hno : ¬ ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W : Subgroup P) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (D : Subgroup P) [D.Normal] [IsMulCommutative D]
    (hDC : centralizer (D : Set P) ≤ D)
    (hO : (omega₁ D (p := 2)).map D.subtype = W)
    (n : ℕ) (hn : 1 ≤ n) (hne : n ≠ 2)
    (e : D ≃* (Multiplicative (ZMod (2 ^ n)) × Multiplicative (ZMod (2 ^ n))))
    (B : Subgroup P) [IsElementaryAbelian 2 B] (hWB : W ≤ B) :
    Nat.card ((MulAut.conjNormal : P →* MulAut D).comp B.subtype).range ≤ 4 := by
  by_cases h : n = 1
  · subst n
    rw [conj_image_card_eq_one_of_binary_base_overgroup W D B hO hWB e]
    decide
  · exact conj_image_card_le_four_of_large_homocyclic_overgroup hP hZ hno W hW
      D hDC hO n (by omega) e B hWB

/-- Final equal-factor assembly has just one remaining structural premise:
the action bound when this base is a C₄-square. -/
public theorem conj_image_card_le_four_of_homocyclic_overgroup_of_c4_square_bound
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hZ : Nat.card (omega₁ (center P) (p := 2)) = 2)
    (hno : ¬ ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W : Subgroup P) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (D : Subgroup P) [D.Normal] [IsMulCommutative D]
    (hDC : centralizer (D : Set P) ≤ D)
    (hO : (omega₁ D (p := 2)).map D.subtype = W)
    (n : ℕ) (hn : 1 ≤ n)
    (e : D ≃* (Multiplicative (ZMod (2 ^ n)) × Multiplicative (ZMod (2 ^ n))))
    (B : Subgroup P) [IsElementaryAbelian 2 B] (hWB : W ≤ B)
    (hC4 : (D ≃* (Multiplicative (ZMod 4) × Multiplicative (ZMod 4))) →
      Nat.card ((MulAut.conjNormal : P →* MulAut D).comp B.subtype).range ≤ 4) :
    Nat.card ((MulAut.conjNormal : P →* MulAut D).comp B.subtype).range ≤ 4 := by
  by_cases h : n = 2
  · subst n
    exact hC4 e
  · exact conj_image_card_le_four_of_homocyclic_overgroup_of_exponent_ne_four
      hP hZ hno W hW D hDC hO n hn h e B hWB

/-- Equal cyclic factors always give an action image of order at most four.

The exponent-four case is discharged by the C₄-square extension theorem; all
other exponents are handled by the binary or large-homocyclic branches above.
The uniqueness hypothesis on the normal four is retained at this interface for
the surrounding Thompson reduction, although the local action argument does
not need it.
-/
public theorem conj_image_card_le_four_of_homocyclic_overgroup
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hZ : Nat.card (omega₁ (center P) (p := 2)) = 2)
    (hno : ¬ ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W : Subgroup P) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (_hunique : ∀ F : Subgroup P, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = W)
    (D : Subgroup P) [D.Normal] [IsMulCommutative D]
    (hDC : centralizer (D : Set P) ≤ D)
    (hO : (omega₁ D (p := 2)).map D.subtype = W)
    (n : ℕ) (hn : 1 ≤ n)
    (e : D ≃* (Multiplicative (ZMod (2 ^ n)) × Multiplicative (ZMod (2 ^ n))))
    (B : Subgroup P) [IsElementaryAbelian 2 B] (hWB : W ≤ B) :
    Nat.card ((MulAut.conjNormal : P →* MulAut D).comp B.subtype).range ≤ 4 := by
  by_cases h : n = 2
  · subst n
    exact conj_image_card_le_four_of_c4_square_overgroup hP hZ hno W hW D hDC hO e B hWB
  · exact conj_image_card_le_four_of_homocyclic_overgroup_of_exponent_ne_four
      hP hZ hno W hW D hDC hO n hn h e B hWB

end IsPGroup
