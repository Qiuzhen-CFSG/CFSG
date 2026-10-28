module

public import Theory.GroupTheory.PGroup.Omega
public import Mathlib.GroupTheory.Solvable

/-!
# Elementary abelian characteristic subgroups

A nontrivial finite abelian characteristic subgroup contains a nontrivial
elementary abelian characteristic subgroup: choose a prime divisor of its
order and take its first omega subgroup. Cauchy's theorem proves nontriviality,
and characteristicity is transitive through the ambient inclusion.

For normal subgroups of a nonsolvable overgroup, the ambient normalizer is
also nonsolvable. This preserves the distinction between normality in the
overgroup and normality in the whole group in local subgroup analysis.

Source: Cauchy's theorem and the characteristic omega-subgroup construction.
-/

public section

namespace Subgroup

variable {G : Type*} [Group G]

/-- Select a prime and a nontrivial elementary abelian subgroup without losing
characteristicity in the original group or containment in the supplied subgroup. -/
theorem exists_elementaryAbelian_characteristic_le [Finite G]
    (A : Subgroup G) [A.Characteristic] [IsMulCommutative A] (hA : A ≠ ⊥) :
    ∃ p : ℕ, p.Prime ∧ ∃ E : Subgroup G,
      E ≤ A ∧ E.Characteristic ∧ IsElementaryAbelian p E ∧ E ≠ ⊥ := by
  obtain ⟨p, hp, hdiv⟩ := Nat.exists_prime_and_dvd
    (ne_of_gt ((one_lt_card_iff_ne_bot A).mpr hA))
  let : Fact p.Prime := ⟨hp⟩
  let : (omega₁ A (p := p)).Characteristic := omega₁_characteristic A
  let : IsElementaryAbelian p (omega₁ A (p := p)) :=
    IsElementaryAbelian.omega₁_of_isMulCommutative A
  exact ⟨p, hp, (omega₁ A (p := p)).map A.subtype, map_subtype_le _,
    inferInstance, IsElementaryAbelian.map A.subtype,
    omega₁_map_subtype_ne_bot A p hdiv⟩

/-- Relative normality puts the overgroup inside the ambient normalizer, so
a solvable ambient normalizer would make the overgroup solvable. -/
theorem not_isSolvable_normalizer_map_of_normal
    (M : Subgroup G) (E : Subgroup M) [E.Normal] (hM : ¬ Group.IsSolvable M) :
    ¬ Group.IsSolvable (normalizer (E.map M.subtype : Set G)) := by
  intro hN
  let := hN
  have hMN : M ≤ normalizer (E.map M.subtype : Set G) := by
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map,
      range_subtype] using E.le_normalizer_map M.subtype
  exact hM (Group.isSolvable_of_isSolvable_injective
    (f := inclusion hMN) (inclusion_injective hMN))

end Subgroup
