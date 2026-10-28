module

public import Theory.SpecificGroups.AlternatingSeven.ThreeResidualLocals.ModelNormalizers.ResidualBounds
public import Mathlib.GroupTheory.NoncommCoprod
import Mathlib.Tactic

/-!
# The common residual candidate A₄ × C₃

The disjoint cubic cycle centralizes the natural A₄ and intersects it trivially.
The multiplication homomorphism therefore identifies the join with the direct
product. Its order is 36. A small word parametrization supports subsequent action
calculations without enumerating all of S₇.

Source: Aschbacher–Smith 15.3.43, printed p.1140.
-/

@[expose] public section
open Equiv Subgroup
namespace AlternatingSeven.ThreeResidualLocals

private instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

theorem tailThree_order : orderOf tailThree = 3 := by
  apply orderOf_eq_prime_iff.mpr
  decide +kernel

theorem naturalFour_commute_tailThree (a : naturalFour) : Commute (a : Perm7) tailThree := by
  obtain ⟨i, hi⟩ : ∃ i, words12 naturalThree fourFlip i = (a : Perm7) := by
    change (a : Perm7) ∈ naturalExplicit
    rw [← naturalFour_eq_explicit]
    exact a.property
  rw [← hi]
  have h : ∀ i : Fin 12, Commute (words12 naturalThree fourFlip i) tailThree := by
    change ∀ i : Fin 12, words12 naturalThree fourFlip i * tailThree =
      tailThree * words12 naturalThree fourFlip i
    decide +kernel
  exact h i

private theorem natural_tail_commute (a : naturalFour) (b : zpowers tailThree) :
    Commute (a : Perm7) (b : Perm7) := by
  obtain ⟨k, hk⟩ := mem_zpowers_iff.mp b.property
  rw [← hk]
  exact (naturalFour_commute_tailThree a).zpow_right k

theorem naturalFour_disjoint_tailThree : Disjoint naturalFour (zpowers tailThree) := by
  apply Subgroup.disjoint_def.mpr
  intro g hn hq
  rw [mem_zpowers_iff_mem_range_orderOf, tailThree_order] at hq
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hq
  have hk3 : k < 3 := Finset.mem_range.mp hk
  interval_cases k
  · simp
  · exact False.elim (tailThree_not_mem_naturalFour (by simpa using hn))
  · have h : tailThree ^ 2 ∉ naturalFour := by
      rw [naturalFour_eq_explicit]
      decide +kernel
    exact False.elim (h hn)

/-- Multiplication embeds the two disjoint commuting factors. -/
def expandedProductHom : naturalFour × zpowers tailThree →* Perm7 :=
  naturalFour.subtype.noncommCoprod (zpowers tailThree).subtype (by exact natural_tail_commute)

theorem expandedProductHom_injective : Function.Injective expandedProductHom := by
  apply (MonoidHom.noncommCoprod_injective _ _ _).mpr
  simpa only [range_subtype] using And.intro naturalFour.subtype_injective
    (And.intro (zpowers tailThree).subtype_injective naturalFour_disjoint_tailThree)

theorem expandedProductHom_range : expandedProductHom.range = expandedFour := by
  rw [expandedProductHom, MonoidHom.noncommCoprod_range, range_subtype, range_subtype]
  rfl

theorem expandedFour_card : Nat.card expandedFour = 36 := by
  rw [← expandedProductHom_range]
  change Nat.card (Set.range expandedProductHom) = 36
  rw [Nat.card_range_of_injective expandedProductHom_injective, Nat.card_prod,
    naturalFour_card, Nat.card_zpowers, tailThree_order]

/-- The 36 natural words times powers of the disjoint cubic cycle. -/
def expandedWord (i : Fin 12 × Fin 3) : Perm7 :=
  words12 naturalThree fourFlip i.1 * tailThree ^ i.2.val

theorem mem_expandedFour_iff (g : Perm7) :
    g ∈ expandedFour ↔ ∃ i : Fin 12 × Fin 3, expandedWord i = g := by
  rw [← expandedProductHom_range]
  constructor
  · rintro ⟨⟨a, b⟩, rfl⟩
    obtain ⟨i, hi⟩ : ∃ i, words12 naturalThree fourFlip i = (a : Perm7) := by
      change (a : Perm7) ∈ naturalExplicit
      rw [← naturalFour_eq_explicit]
      exact a.property
    have hb := b.property
    rw [mem_zpowers_iff_mem_range_orderOf, tailThree_order] at hb
    obtain ⟨j, hj, hbj⟩ := Finset.mem_image.mp hb
    exact ⟨⟨i, j, Finset.mem_range.mp hj⟩, by
      change words12 naturalThree fourFlip i * tailThree ^ j = (a : Perm7) * (b : Perm7)
      rw [hi, hbj]⟩
  · rintro ⟨⟨i, j⟩, rfl⟩
    refine ⟨⟨⟨words12 naturalThree fourFlip i, ?_⟩,
      ⟨tailThree ^ j.val, npow_mem_zpowers _ _⟩⟩, rfl⟩
    rw [naturalFour_eq_explicit]
    exact ⟨i, rfl⟩

instance (g : Perm7) : Decidable (g ∈ expandedFour) :=
  decidable_of_iff (∃ i : Fin 12 × Fin 3, expandedWord i = g) (mem_expandedFour_iff g).symm

end AlternatingSeven.ThreeResidualLocals
