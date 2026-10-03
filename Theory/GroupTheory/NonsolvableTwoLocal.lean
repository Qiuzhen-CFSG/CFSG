module

public import Theory.Quasithin
public import Mathlib.GroupTheory.Solvable
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Nonsolvable involution centralizers give nonsolvable two-local subgroups

This reduction preserves the centralizer obstruction in Stellmacher (10.1)(a).
The centralizer of an involution is the normalizer of its cyclic subgroup: the
automorphism group of that order-two subgroup has cardinality one. The exact
two-local conclusion is public for transferring two-local hypotheses.
The cyclic subgroup has order two, so its normalizer is two-local. Solvability
of that normalizer would imply solvability of the centralizer by inclusion.
The nonsolvable-centralizer reduction needs no ambient finiteness. The exact
two-local lemma is stated for finite groups.

Source: the nonsolvable-local addendum to Stellmacher's Theorem 1 and (10.1)(a),
`refs/latex/stellmacher-n-group.tex`.
-/

namespace Theory.GroupTheory

/-- The centralizer of an actual involution is itself a two-local subgroup. -/
public theorem isTwoLocal_involution_centralizer
    {G : Type*} [Group G] [Finite G] {x : G} (hx : orderOf x = 2) :
    IsTwoLocal (Subgroup.centralizer ({x} : Set G)) := by
  let A := Subgroup.zpowers x
  have hA : Nat.card A = 2 := by rw [Nat.card_zpowers, hx]
  have hp : IsPGroup 2 A := IsPGroup.of_card (n := 1) (by simpa using hA)
  have hne : A ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hA
    omega
  have hAut : Nat.card (MulAut A) = 1 := by rw [IsCyclic.card_mulAut, hA]; decide
  let : Subsingleton (MulAut A) := (Nat.card_eq_one_iff_unique.mp hAut).1
  have hNC : Subgroup.normalizer (A : Set G) ≤ Subgroup.centralizer ({x} : Set G) := by
    intro g hg
    have he : A.normalizerMonoidHom ⟨g, hg⟩ = 1 := Subsingleton.elim _ _
    have hv := congrArg (fun a : MulAut A => (a ⟨x, Subgroup.mem_zpowers x⟩ : G)) he
    change g * x * g⁻¹ = x at hv
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    have hh := congrArg (fun a : G => a * g) hv
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using hh
  refine ⟨A, hne, hp, le_antisymm ?_ hNC⟩
  rw [← Subgroup.centralizer_closure, ← Subgroup.zpowers_eq_closure]
  exact Subgroup.centralizer_le_normalizer _

public theorem exists_nonsolvable_twoLocal_of_involution_centralizer
    {G : Type*} [Group G] {x : G} (hx : orderOf x = 2)
    (hcentralizer : ¬ Group.IsSolvable (Subgroup.centralizer ({x} : Set G))) :
    ∃ U : Subgroup G, IsTwoLocal U ∧ ¬ Group.IsSolvable U := by
  have hcyclic : IsPGroup 2 (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by simpa only [Nat.card_zpowers, pow_one] using hx)
  have hne : Subgroup.zpowers x ≠ ⊥ := by
    intro hbot
    have hxone := Subgroup.zpowers_eq_bot.mp hbot
    simp [hxone] at hx
  have hle : Subgroup.centralizer ({x} : Set G) ≤
      Subgroup.normalizer (Subgroup.zpowers x : Set G) := by
    rw [← Subgroup.centralizer_closure, ← Subgroup.zpowers_eq_closure]
    exact Subgroup.centralizer_le_normalizer _
  refine ⟨Subgroup.normalizer (Subgroup.zpowers x : Set G),
    ⟨Subgroup.zpowers x, hne, hcyclic, rfl⟩, ?_⟩
  intro hsolvable
  let := hsolvable
  exact hcentralizer (Group.isSolvable_of_isSolvable_injective
    (Subgroup.inclusion_injective hle))

end Theory.GroupTheory
