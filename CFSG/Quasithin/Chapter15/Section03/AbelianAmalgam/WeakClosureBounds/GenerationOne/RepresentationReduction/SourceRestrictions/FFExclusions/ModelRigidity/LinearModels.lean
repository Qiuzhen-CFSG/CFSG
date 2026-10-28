module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.RepresentationReduction.SourceRestrictions.FFExclusions.ModelRigidity.Invariants

/-!
# Rigidity of the linear and symplectic entries

An isomorphism preserves both the two-part of the order and the elementary
two-rank. Their different ratios separate PSL₂, PSL₃, Sp₄ and G₂; equality
within one family recovers the field exponent. The six small orders are
checked separately, including the two derived endpoints and the quotient of
the exceptional triple cover. The source assumptions f > 1 and Odd f remove
the familiar binary and alternating coincidences.

Source: Aschbacher--Smith, B.4.2--4, printed pp.86--87, and the E.2.2
model comparison in 15.3.65, printed p.1152.
-/

public section
open Subgroup Matrix Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.FFExclusions.ModelRigidity

/-- Two-parts of the six actual exceptional orders. -/
theorem SmallOrder.two_part {c : ℕ} (h : SmallOrder c) :
    c.factorization 2 = 2 ∨ c.factorization 2 = 3 ∨ c.factorization 2 = 5 ∨
      c.factorization 2 = 6 ∨ c.factorization 2 = 10 := by
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

/-- An odd ternary field exponent above one rules out every small order. -/
theorem not_smallOrder_of_ternary_part {c f : ℕ} (hf : 1 < f) (ho : Odd f)
    (hp : c.factorization 2 = 3 * f) : ¬ SmallOrder c := by
  intro h
  obtain ⟨k, hk⟩ := ho
  rcases h.two_part with h | h | h | h | h <;> omega

/-- The symplectic two-part alone exceeds every small endpoint in the source range. -/
theorem not_smallOrder_of_quaternary_part {c f : ℕ} (hf : 1 < f) (ho : Odd f)
    (hp : c.factorization 2 = 4 * f) : ¬ SmallOrder c := by
  intro h
  obtain ⟨k, hk⟩ := ho
  rcases h.two_part with h | h | h | h | h <;> omega

private theorem not_smallOrder_of_binary_order {c f : ℕ} (ho : Odd f)
    (hp : c.factorization 2 = f) (hc : c = 2 ^ f * ((2 ^ f) ^ 2 - 1)) :
    ¬ SmallOrder c := by
  intro h
  rcases h with h | h | h | h | h | h
  · rw [h, show Nat.factorization 60 2 = 2 by decide +kernel] at hp
    have hf : f = 2 := hp.symm
    subst f
    norm_num at ho
  · rw [h, show Nat.factorization 360 2 = 3 by decide +kernel] at hp
    have hf : f = 3 := hp.symm
    rw [h, hf] at hc
    norm_num at hc
  · rw [h, show Nat.factorization 2520 2 = 3 by decide +kernel] at hp
    have hf : f = 3 := hp.symm
    rw [h, hf] at hc
    norm_num at hc
  · rw [h, show Nat.factorization 6048 2 = 5 by decide +kernel] at hp
    have hf : f = 5 := hp.symm
    rw [h, hf] at hc
    norm_num at hc
  · rw [h, show Nat.factorization 20160 2 = 6 by decide +kernel] at hp
    have hf : f = 6 := hp.symm
    subst f
    norm_num at ho
  · rw [h, show Nat.factorization 9999360 2 = 10 by decide +kernel] at hp
    have hf : f = 10 := hp.symm
    subst f
    norm_num at ho

variable {F : Type} [Field F] [Finite F] {f : ℕ} {family : Family} {q : ℕ}

/-- Binary PSL₂ can match only PSL₂ with the same defining field cardinality. -/
theorem pslTwo_componentModel (hf : 1 < f) (ho : Odd f) (hF : Nat.card F = 2 ^ f)
    (h : ComponentModel PSL(2,F) family q) : family = .linearTwo ∧ q = 2 ^ f := by
  obtain ⟨hr, hp⟩ := pslTwo_invariants (by omega) hF
  rcases h.invariant_cases with ⟨n, hn, ht, hq, hr', hp'⟩ |
    ⟨n, hn, ht, hq, hr', hp'⟩ | ⟨n, hn, ht, hq, hr', hp'⟩ |
    ⟨n, hn, ht, hq, hr', hp'⟩ | hs
  · have he : n = f := by omega
    exact ⟨ht, he ▸ hq⟩
  · omega
  · omega
  · omega
  · exact (not_smallOrder_of_binary_order ho hp (pslTwo_card hF) hs).elim

/-- Binary PSL₃ at odd source exponent matches only its own family and field. -/
theorem pslThree_componentModel (hf : 1 < f) (ho : Odd f) (hF : Nat.card F = 2 ^ f)
    (h : ComponentModel PSL(3,F) family q) : family = .linearThree ∧ q = 2 ^ f := by
  obtain ⟨hr, hp⟩ := pslThree_invariants (by omega) hF
  rcases h.invariant_cases with ⟨n, hn, ht, hq, hr', hp'⟩ |
    ⟨n, hn, ht, hq, hr', hp'⟩ | ⟨n, hn, ht, hq, hr', hp'⟩ |
    ⟨n, hn, ht, hq, hr', hp'⟩ | hs
  · omega
  · have he : n = f := by omega
    exact ⟨ht, he ▸ hq⟩
  · omega
  · omega
  · exact (not_smallOrder_of_ternary_part hf ho hp hs).elim

/-- The central simple symplectic quotient matches only Sp₄ with the same field. -/
theorem spFour_componentModel (hf : 1 < f) (ho : Odd f) (hF : Nat.card F = 2 ^ f)
    (h : ComponentModel (Theory.SpecificGroups.SymplecticFour.Sp F ⧸
      center (Theory.SpecificGroups.SymplecticFour.Sp F)) family q) :
    family = .symplecticFour ∧ q = 2 ^ f := by
  obtain ⟨hr, hp⟩ := spFour_invariants (by omega) hF
  rcases h.invariant_cases with ⟨n, hn, ht, hq, hr', hp'⟩ |
    ⟨n, hn, ht, hq, hr', hp'⟩ | ⟨n, hn, ht, hq, hr', hp'⟩ |
    ⟨n, hn, ht, hq, hr', hp'⟩ | hs
  · omega
  · omega
  · have he : n = f := by omega
    exact ⟨ht, he ▸ hq⟩
  · omega
  · exact (not_smallOrder_of_quaternary_part hf ho hp hs).elim

/-- The surviving PSL₂ entry really is realized on this carrier. -/
theorem pslTwo_componentModel_iff (hf : 1 < f) (ho : Odd f) (hF : Nat.card F = 2 ^ f) :
    ComponentModel PSL(2,F) family q ↔ family = .linearTwo ∧ q = 2 ^ f := by
  constructor
  · exact pslTwo_componentModel hf ho hF
  · rintro ⟨rfl, rfl⟩
    exact .linearTwo F (by omega) hF (MulEquiv.refl _)

/-- The surviving PSL₃ entry really is realized on this carrier. -/
theorem pslThree_componentModel_iff (hf : 1 < f) (ho : Odd f) (hF : Nat.card F = 2 ^ f) :
    ComponentModel PSL(3,F) family q ↔ family = .linearThree ∧ q = 2 ^ f := by
  constructor
  · exact pslThree_componentModel hf ho hF
  · rintro ⟨rfl, rfl⟩
    exact .linearThree F (by omega) hF (MulEquiv.refl _)

/-- The surviving Sp₄ entry really is realized on this actual center quotient. -/
theorem spFour_componentModel_iff (hf : 1 < f) (ho : Odd f) (hF : Nat.card F = 2 ^ f) :
    ComponentModel (Theory.SpecificGroups.SymplecticFour.Sp F ⧸
      center (Theory.SpecificGroups.SymplecticFour.Sp F)) family q ↔
    family = .symplecticFour ∧ q = 2 ^ f := by
  constructor
  · exact spFour_componentModel hf ho hF
  · rintro ⟨rfl, rfl⟩
    exact .symplecticFour F hf hF (MulEquiv.refl _)

/-- The literal derived symplectic model uses the canonical inclusion from E.2.2. -/
theorem spFourDerived_componentModel_iff
    (hf : 1 < f) (ho : Odd f) (hF : Nat.card F = 2 ^ f) :
    ComponentModel (BorelReduction.SourceCases.Sp4Derived F ⧸
      center (BorelReduction.SourceCases.Sp4Derived F)) family q ↔
    family = .symplecticFour ∧ q = 2 ^ f := by
  let e := centralQuotientCongr (spFourDerivedEquiv hF hf)
  exact (show ComponentModel _ family q ↔ ComponentModel _ family q from
    ⟨fun h => h.transport e.symm, fun h => h.transport e⟩).trans
      (spFour_componentModel_iff hf ho hF)

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.FFExclusions.ModelRigidity
