module

public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.Tactic

/-!
# Normalizers of subgroups of order three

Every nonidentity element of a subgroup of order three generates it. A
normalizing element conjugates a generator either to itself or to its
inverse, since those are the two nonidentity elements. If an order-two
subgroup has full commutator with the order-three subgroup, its nonidentity
element must act by inversion: the other choice would centralize both
cyclic generators and make the commutator trivial.

The proof uses prime-order element formulas and a three-element power
range, without a classification of groups of order six. These are the
group-theoretic operator relations used in the sixteen-point action
calculation of Stellmacher (1.6), journal p.18;
see `refs/latex/stellmacher-n-group.tex`.
-/

namespace Subgroup

open scoped commutatorElement

private theorem orderOf_eq_three_of_mem_card_three
    {G : Type*} [Group G] (F : Subgroup G) (hFcard : Nat.card F = 3)
    (f : G) (hf : f ∈ F) (hfne : f ≠ 1) : orderOf f = 3 := by
  let fF : F := ⟨f, hf⟩
  have hpow : fF ^ 3 = 1 := by rw [← hFcard]; exact pow_card_eq_one'
  have hfFne : fF ≠ 1 := fun h => hfne (congrArg Subtype.val h)
  have ho : orderOf fF = 3 := orderOf_eq_prime hpow hfFne
  change orderOf (fF : G) = 3
  rw [Subgroup.orderOf_coe]
  exact ho

public theorem cyclicThree_generator
    {G : Type*} [Group G] [Finite G]
    (F : Subgroup G) (hFcard : Nat.card F = 3)
    (f : G) (hf : f ∈ F) (hfne : f ≠ 1) :
    Subgroup.zpowers f = F ∧ f ^ 3 = 1 := by
  have ho := orderOf_eq_three_of_mem_card_three F hFcard f hf hfne
  constructor
  · apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hf)
    rw [Nat.card_zpowers, ho, hFcard]
  · exact orderOf_dvd_iff_pow_eq_one.mp (by rw [ho])

public theorem cyclicThree_normalizer_conjugates
    {G : Type*} [Group G] [Finite G]
    (F : Subgroup G) (hFcard : Nat.card F = 3)
    (f : G) (hf : f ∈ F) (hfne : f ≠ 1)
    (g : G) (hg : g ∈ Subgroup.normalizer (F : Set G)) :
    g * f * g⁻¹ = f ∨ g * f * g⁻¹ = f⁻¹ := by
  classical
  obtain ⟨hgen, hpow⟩ := cyclicThree_generator F hFcard f hf hfne
  have ho := orderOf_eq_three_of_mem_card_three F hFcard f hf hfne
  have hconj : g * f * g⁻¹ ∈ F := (Subgroup.mem_normalizer_iff.mp hg f).mp hf
  rw [← hgen, mem_zpowers_iff_mem_range_orderOf, ho] at hconj
  obtain ⟨n, hn, hnconj⟩ := Finset.mem_image.mp hconj
  have hnlt : n < 3 := Finset.mem_range.mp hn
  interval_cases n
  · have hbad : g * f * g⁻¹ = 1 := by simpa using hnconj.symm
    have hbad' := congrArg (fun z : G => g⁻¹ * z * g) hbad
    exact (hfne (by simpa [mul_assoc] using hbad')).elim
  · exact Or.inl (by simpa using hnconj.symm)
  · right
    have hf2 : f ^ 2 = f⁻¹ := by
      have h := congrArg (fun z : G => z * f⁻¹) hpow
      simpa [pow_succ, mul_assoc] using h
    simpa only [hf2] using hnconj.symm

public theorem cyclicThree_full_commutator_inverts
    {G : Type*} [Group G] [Finite G]
    (F B : Subgroup G) (hFcard : Nat.card F = 3) (hBcard : Nat.card B = 2)
    (hBnorm : B ≤ Subgroup.normalizer (F : Set G))
    (hcomm : ⁅F, B⁆ = F)
    (f b : G) (hf : f ∈ F) (hfne : f ≠ 1) (hb : b ∈ B) (hbne : b ≠ 1) :
    b * f * b⁻¹ = f⁻¹ := by
  rcases cyclicThree_normalizer_conjugates F hFcard f hf hfne b (hBnorm hb) with hfix | hinv
  · exfalso
    obtain ⟨hFgen, _⟩ := cyclicThree_generator F hFcard f hf hfne
    have hBpow : b ^ 2 = 1 := by
      have hpow : (⟨b, hb⟩ : B) ^ Nat.card B = 1 := pow_card_eq_one'
      rw [hBcard] at hpow
      exact congrArg Subtype.val hpow
    have hbOrder : orderOf b = 2 := orderOf_eq_prime hBpow hbne
    have hBgen : Subgroup.zpowers b = B := by
      apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hb)
      rw [Nat.card_zpowers, hbOrder, hBcard]
    have hbf : b * f = f * b := by
      have h := congrArg (fun z : G => z * b) hfix
      simpa [mul_assoc] using h
    have hbot : ⁅F, B⁆ = ⊥ := by
      apply Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
      rw [← hFgen]
      apply Subgroup.zpowers_le.mpr
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [← hBgen] at hy
      change y ∈ Subgroup.zpowers b at hy
      rw [Subgroup.mem_zpowers_iff] at hy
      obtain ⟨n, rfl⟩ := hy
      exact (Commute.zpow_left (show Commute b f from hbf) n).eq
    have hFbot : F = ⊥ := hcomm.symm.trans hbot
    have hfbot : f ∈ (⊥ : Subgroup G) := hFbot ▸ hf
    exact hfne hfbot
  · exact hinv

end Subgroup

