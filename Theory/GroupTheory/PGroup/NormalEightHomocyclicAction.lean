module

public import Theory.GroupTheory.PGroup.NormalEightCentralAction
public import Theory.GroupTheory.PGroup.HomocyclicDeepInvolution
public import Theory.GroupTheory.PGroup.HomocyclicElementaryFourTorsion
public import Theory.GroupTheory.PGroup.NormalEightC4SquareAction

/-!
# Homocyclic conjugation under the normal elementary eight obstruction

The central omega-four equality implies that ambient conjugation fixes every
involution in a self-centralizing normal abelian subgroup D. If D itself has
exponent two, its entire conjugation image is trivial. This closes the first
case of the equal-cyclic-factor action bound. For exponent four the matrix
calculation excludes the five actions that would generate a normal elementary
eight. For larger exponents, the involution calculation reduces the bound to
actions faithful on four-torsion, where the binary matrix argument gives order
at most four.

Source: the normal-abelian reduction of MacWilliams–Sah, quoted by
Janko–Thompson, Math. Z. 113 (1970), 1.1, printed p.385, in
`refs/original/n-group-global/odd-core-rank-two-source/janko-thompson-1970-gdz.pdf`.
-/

open Subgroup

namespace IsPGroup

private theorem square_eq_one_of_equiv_binary_pair {D : Type*} [Group D]
    (e : D ≃* (Multiplicative (ZMod (2 ^ 1)) × Multiplicative (ZMod (2 ^ 1)))) :
    ∀ d : D, d ^ 2 = 1 := by
  intro d
  apply e.injective
  rw [map_pow, map_one]
  apply Prod.ext
  · change Multiplicative.ofAdd (2 • (e d).1.toAdd) = 1
    simp only [nsmul_eq_mul, show ((2 : ℕ) : ZMod (2 ^ 1)) = 0 by decide, zero_mul]
    rfl
  · change Multiplicative.ofAdd (2 • (e d).2.toAdd) = 1
    simp only [nsmul_eq_mul, show ((2 : ℕ) : ZMod (2 ^ 1)) = 0 by decide, zero_mul]
    rfl

/-- The exponent-two homocyclic case has trivial action image. -/
public theorem conj_image_card_eq_one_of_homocyclic_exponent_one
    {P : Type*} [Group P] [Finite P]
    (hno : ¬ ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (hZ : Nat.card (omega₁ (center P) (p := 2)) = 4)
    (D : Subgroup P) [D.Normal] [IsMulCommutative D]
    (e : D ≃* (Multiplicative (ZMod (2 ^ 1)) × Multiplicative (ZMod (2 ^ 1))))
    (A : Subgroup P) :
    Nat.card ((MulAut.conjNormal : P →* MulAut D).comp A.subtype).range = 1 := by
  let : IsElementaryAbelian 2 D := {
    toIsMulCommutative := inferInstance
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
      (square_eq_one_of_equiv_binary_pair e) }
  exact conj_image_card_eq_one_of_elementary_normal_of_no_normal_eight hno hZ D A

end IsPGroup

namespace IsPGroup

/-- Equal cyclic factors have conjugation image of order at most four when
normal elementary eights are absent. -/
public theorem conj_image_card_le_four_of_homocyclic_factors_of_no_normal_eight
    {P : Type*} [Group P] [Finite P]
    (hP : IsPGroup 2 P)
    (hno : ¬ ∃ U : Subgroup P, U.Normal ∧ IsElementaryAbelian 2 U ∧ 8 ≤ Nat.card U)
    (hZ : Nat.card (omega₁ (Subgroup.center P) (p := 2)) = 4)
    (D : Subgroup P) [D.Normal] [IsMulCommutative D]
    (hD : Subgroup.centralizer (D : Set P) ≤ D)
    (n : ℕ) (hn : 1 ≤ n)
    (e : D ≃* (Multiplicative (ZMod (2 ^ n)) × Multiplicative (ZMod (2 ^ n))))
    (A : Subgroup P) [IsElementaryAbelian 2 A] :
    Nat.card ((MulAut.conjNormal : P →* MulAut D).comp A.subtype).range ≤ 4 := by
  by_cases hn1 : n = 1
  · subst n
    rw [conj_image_card_eq_one_of_homocyclic_exponent_one hno hZ D e A]
    decide
  by_cases hn2 : n = 2
  · subst n
    simpa using conj_image_card_le_four_of_c4_square_of_no_normal_eight
      hP hno hZ D hD e A
  have hn3 : 3 ≤ n := by omega
  let c : P →* MulAut D := MulAut.conjNormal
  let f := c.comp A.subtype
  let B := f.range
  let : IsElementaryAbelian 2 B := {
    toIsMulCommutative := by
      change IsMulCommutative ↥(f.range)
      exact (MonoidHom.range_eq_map f).symm ▸
        Subgroup.map_isMulCommutative (H := (⊤ : Subgroup A)) (f := f)
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (by
      intro b
      apply Subtype.ext
      rcases b.property with ⟨a, hmem⟩
      have hpow : (a : P) ^ 2 = 1 :=
        elemPow_eq_one_of_isElementaryAbelian (a : P) a.property
      have hpowA : a ^ 2 = 1 := Subtype.ext hpow
      change ((b : B) : MulAut D) ^ 2 = 1
      rw [← hmem, ← map_pow, hpowA, map_one]) }
  have hfix : ∀ b ∈ B, ∀ d : D, d ^ 2 = 1 → b d = d := by
    intro b hb d hd
    obtain ⟨a, rfl⟩ := hb
    exact conjNormal_fixed_of_square_eq_one_of_no_normal_eight hno hZ D hD (a : P) d hd
  have hfaith : ∀ b ∈ B, (∀ d : D, d ^ 4 = 1 → b d = d) → b = 1 := by
    intro b hb hfour
    obtain ⟨a, rfl⟩ := hb
    have hA : ((a : A) : P) ^ 2 = 1 :=
      elemPow_eq_one_of_isElementaryAbelian (a : P) a.property
    have ha : (c (a : P)) ^ 2 = 1 := by
      rw [← map_pow, hA, map_one]
    have hdeep := deep_involution_of_homocyclic_fixing_four_torsion n hn3 e
      (c (a : P)) ha hfour
    have hcomm (g : P) : Commute (c g) (c (a : P)) := by
      apply (hdeep.1 (c g) ?_)
      intro d hd
      exact conjNormal_fixed_of_square_eq_one_of_no_normal_eight hno hZ D hD g d hd
    have hinv (d : P) (hd : d ∈ D)
        (hinvd : (a : P) * d * (a : P)⁻¹ = d⁻¹) : d ^ 2 = 1 := by
      let dD : D := ⟨d, hd⟩
      have hact : c (a : P) dD = dD⁻¹ := by
        apply Subtype.ext
        exact hinvd
      exact congrArg Subtype.val (hdeep.2 dD hact)
    have haD := involution_mem_normal_abelian_of_central_action_of_no_normal_eight
      hno hZ D hD (a : P) hA hcomm hinv
    have htriv : c (a : P) = 1 := by
      apply MulEquiv.ext
      intro d
      apply Subtype.ext
      change (a : P) * (d : P) * (a : P)⁻¹ = d
      have hc := ((@IsMulCommutative.is_comm D _ _).comm ⟨a, haD⟩ d)
      have hc' := congrArg Subtype.val hc
      change (a : P) * (d : P) = (d : P) * (a : P) at hc'
      rw [hc', mul_inv_cancel_right]
    change c (a : P) = 1
    exact htriv
  exact HomocyclicFourTorsion.card_le_four_of_homocyclic_elementary_four_torsion
    n hn3 e B hfix hfaith

end IsPGroup
