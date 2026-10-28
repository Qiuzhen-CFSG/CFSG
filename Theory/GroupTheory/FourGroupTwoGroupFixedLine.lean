module

public import Theory.GroupTheory.FourGroupTwoGroupAction
public import Theory.GroupTheory.InvolutionCentralizerControl
public import Theory.GroupTheory.CharacteristicCentralizerFusion

/-!
# Fixed lines of a two-group on a four-group

A nontrivial two-group action on a four-group has precisely two fixed
elements. Every group normalizing both the four-group and the acting group
therefore fixes this line pointwise. Orbit counting gives a nonidentity
fixed point, and Lagrange's theorem determines the order of the fixed group.

This is the elementary action argument used with the original radical and
the fixed component factor in Aschbacher--Smith, 15.3.23.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

/-- A nontrivial two-group action on a four-group has a fixed line. -/
theorem four_twoGroup_fixed_card_two (H P : Subgroup G) [IsKleinFour H]
    (hp : IsPGroup 2 P) (hn : P ≤ normalizer (H : Set G))
    (hmove : ¬ P ≤ centralizer (H : Set G)) :
    Nat.card (H ⊓ centralizer (P : Set G) : Subgroup G) = 2 := by
  let ρ := H.normalizerMonoidHom.comp (inclusion hn)
  let : MulDistribMulAction P H := MulDistribMulAction.compHom H ρ
  have hdiv : 2 ∣ Nat.card H := by rw [IsKleinFour.card_four]; decide
  obtain ⟨h, hfix, hne⟩ :=
    hp.exists_fixed_point_of_prime_dvd_card_of_fixed_point (α := H) hdiv
      (show (1 : H) ∈ MulAction.fixedPoints P H by simp [MulAction.mem_fixedPoints])
  have hmem : (h : G) ∈ H ⊓ centralizer (P : Set G) := by
    refine ⟨h.property, ?_⟩
    intro p hp
    have he := congrArg Subtype.val (hfix ⟨p, hp⟩)
    change p * (h : G) * p⁻¹ = h at he
    exact mul_inv_eq_iff_eq_mul.mp he
  have hnz : H ⊓ centralizer (P : Set G) ≠ ⊥ := by
    intro he
    rw [he, mem_bot] at hmem
    exact hne (Subtype.ext hmem.symm)
  have hd : Nat.card (H ⊓ centralizer (P : Set G) : Subgroup G) ∣ 4 := by
    simpa only [IsKleinFour.card_four] using
      card_dvd_of_le (show H ⊓ centralizer (P : Set G) ≤ H from inf_le_left)
  have hnefour : Nat.card (H ⊓ centralizer (P : Set G) : Subgroup G) ≠ 4 := by
    intro hc
    have he : H ⊓ centralizer (P : Set G) = H :=
      eq_of_le_of_card_ge inf_le_left (by simpa only [IsKleinFour.card_four] using hc.ge)
    exact hmove (le_centralizer_iff.mp (he ▸ inf_le_right))
  have hpos : 0 < Nat.card (H ⊓ centralizer (P : Set G) : Subgroup G) := Nat.card_pos
  have hneone : Nat.card (H ⊓ centralizer (P : Set G) : Subgroup G) ≠ 1 :=
    fun he => hnz (card_eq_one.mp he)
  have hle := Nat.le_of_dvd (by decide : 0 < 4) hd
  have hne3 : Nat.card (H ⊓ centralizer (P : Set G) : Subgroup G) ≠ 3 := by
    intro he
    rw [he] at hd
    norm_num at hd
  omega

/-- The common normalizer fixes the line arising from the nontrivial action. -/
theorem four_twoGroup_common_normalizer_fixes (H P : Subgroup G) [IsKleinFour H]
    (hp : IsPGroup 2 P) (hn : P ≤ normalizer (H : Set G))
    (hmove : ¬ P ≤ centralizer (H : Set G)) :
    normalizer (H : Set G) ⊓ normalizer (P : Set G) ≤
      centralizer ((H ⊓ centralizer (P : Set G) : Subgroup G) : Set G) := by
  have hnorm : normalizer (H : Set G) ⊓ normalizer (P : Set G) ≤
      normalizer ((H ⊓ centralizer (P : Set G) : Subgroup G) : Set G) :=
    (le_inf inf_le_left (inf_le_right.trans (normalizer_le_normalizer_centralizer P))).trans
      inf_normalizer_le_normalizer_inf
  exact hnorm.trans (normalizer_le_centralizer_of_card_two _
    (four_twoGroup_fixed_card_two H P hp hn hmove))

end Theory.GroupTheory
