module

public import Theory.SpecificGroups.SymmetricFive.OddLocal
public import Theory.GroupTheory.ElementaryNormalizerThreeRank
public import Theory.GroupTheory.PResidual.Quotient
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Sylow five-normalizer overgroups in S₅

A five-cycle is self-centralizing. Its cyclic automorphism group has order
four, so the normalizer has order dividing twenty; Sylow congruences force
exactly twenty. In any overgroup X the number of Sylow five-subgroups is
|X|/20, between one and six and congruent to one modulo five. Thus X is
either this normalizer or all of S₅. No subgroup lattice is enumerated.

The normalizer's quotient by its normal five-subgroup has order four,
while every element of that five-subgroup has odd order. Consequently its
two-residual is the original Sylow five-subgroup. The final theorem retains
an arbitrary literal homomorphism and identifies both a proper normalizer
overgroup image and its residual image, as needed by the J.4.4 source route.

Source: Aschbacher–Smith, J.4.4 five-normalizer calculation, using Sylow's
theorems and the elementary permutation structure of S₅.
-/

public section

open Subgroup
namespace Theory.SpecificGroups.SymmetricFive.FiveNormalizerOvergroups
abbrev D := Equiv.Perm (Fin 5)
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

private theorem card_group : Nat.card D = 120 := by
  norm_num [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]

theorem card_sylow (P : Sylow 5 D) : Nat.card P = 5 := by
  rw [P.card_eq_multiplicity, card_group]
  decide +kernel

theorem centralizer_eq (P : Sylow 5 D) : centralizer ((P : Subgroup D) : Set D) = (P : Subgroup D) := by
  let : IsCyclic P := isCyclic_of_prime_card (card_sylow P)
  obtain ⟨g, hg⟩ := isCyclic_iff_exists_orderOf_eq_natCard.mp (inferInstance : IsCyclic P)
  have ho : orderOf (g : D) = 5 := (Subgroup.orderOf_coe g).trans (hg.trans (card_sylow P))
  have hz : zpowers (g : D) = (P : Subgroup D) :=
    eq_of_le_of_card_ge (zpowers_le.mpr g.property) (by rw [Nat.card_zpowers, ho, card_sylow P])
  apply le_antisymm
  · exact (centralizer_le (Set.singleton_subset_iff.mpr g.property)).trans_eq
      ((_root_.SymmetricFive.centralizer_of_order_five ho).trans hz)
  · exact le_centralizer_iff_isMulCommutative.mpr inferInstance

theorem card_normalizer (P : Sylow 5 D) :
    Nat.card (normalizer ((P : Subgroup D) : Set D)) = 20 := by
  let N := normalizer ((P : Subgroup D) : Set D)
  let : IsCyclic P := isCyclic_of_prime_card (card_sylow P)
  have hdiv : Nat.card N ∣ 20 := by
    have hh := (P : Subgroup D).card_normalizer_dvd_card_centralizer_mul_card_mulAut
    change Nat.card N ∣ Nat.card (centralizer ((P : Subgroup D) : Set D)) * Nat.card (MulAut P) at hh
    rw [centralizer_eq P, IsCyclic.card_mulAut, card_sylow P] at hh
    exact hh
  have hfive : 5 ∣ Nat.card N := by
    have hh := card_dvd_of_le (P : Subgroup D).le_normalizer
    rwa [card_sylow P] at hh
  have hposs : Nat.card N = 5 ∨ Nat.card N = 10 ∨ Nat.card N = 20 := by
    have hh := Nat.mem_divisors.mpr ⟨hdiv, (by decide : 20 ≠ 0)⟩
    have hds : Nat.divisors 20 = {1, 2, 4, 5, 10, 20} := by decide
    simp only [hds, Finset.mem_insert, Finset.mem_singleton] at hh
    rcases hh with h | h | h | h | h | h <;> omega
  have hm := card_sylow_modEq_one 5 D
  rw [P.card_eq_index_normalizer] at hm
  change N.index % 5 = 1 % 5 at hm
  have hi := N.card_mul_index
  rw [card_group] at hi
  rcases hposs with h | h | h
  · rw [h] at hi
    omega
  · rw [h] at hi
    omega
  · exact h

/-- Every overgroup of the actual five-normalizer is that normalizer or S₅. -/
theorem overgroup_eq (P : Sylow 5 D) (X : Subgroup D)
    (hNX : normalizer ((P : Subgroup D) : Set D) ≤ X) :
    X = normalizer ((P : Subgroup D) : Set D) ∨ X = ⊤ := by
  let N := normalizer ((P : Subgroup D) : Set D)
  let R : Sylow 5 X := P.subtype ((P : Subgroup D).le_normalizer.trans hNX)
  have hRN : normalizer (R : Set X) = N.subgroupOf X := by
    exact (subgroupOf_normalizer_eq ((P : Subgroup D).le_normalizer.trans hNX)).symm
  have hcN : Nat.card (normalizer (R : Set X)) = 20 := by
    rw [hRN, Nat.card_congr (subgroupOfEquivOfLe hNX).toEquiv, card_normalizer P]
  have hcard := (normalizer (R : Set X)).card_mul_index
  rw [hcN, ← R.card_eq_index_normalizer] at hcard
  have hbound : Nat.card X ≤ 120 := card_group ▸ Nat.card_le_card_of_injective X.subtype X.subtype_injective
  have hmod := card_sylow_modEq_one 5 X
  change Nat.card (Sylow 5 X) % 5 = 1 % 5 at hmod
  have hchoice : Nat.card (Sylow 5 X) = 1 ∨ Nat.card (Sylow 5 X) = 6 := by omega
  rcases hchoice with h | h
  · left
    apply (eq_of_le_of_card_ge hNX ?_).symm
    rw [card_normalizer P]
    omega
  · right
    apply eq_of_le_of_card_ge le_top
    rw [card_top, card_group]
    omega

theorem normalizer_isCoatom (P : Sylow 5 D) : IsCoatom (normalizer ((P : Subgroup D) : Set D)) := by
  refine ⟨?_, ?_⟩
  · intro he
    have hc := card_normalizer P
    rw [he, card_top, card_group] at hc
    omega
  · intro X hX
    exact (overgroup_eq P X hX.le).resolve_left (ne_of_gt hX)

/-- The two-residual of the actual five-normalizer is its original Sylow five. -/
theorem residual_eq (P : Sylow 5 D) :
    pResidual 2 (normalizer ((P : Subgroup D) : Set D)) =
      (P : Subgroup D).subgroupOf (normalizer ((P : Subgroup D) : Set D)) := by
  let N := normalizer ((P : Subgroup D) : Set D)
  let R := (P : Subgroup D).subgroupOf N
  let : R.Normal := (P : Subgroup D).normal_in_normalizer
  have hc : Nat.card R = 5 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe (P : Subgroup D).le_normalizer).toEquiv,
      card_sylow P]
  have hquot : IsPGroup 2 (N ⧸ R) := by
    apply IsPGroup.of_card (n := 2)
    change R.index = 2 ^ 2
    have hh := R.card_mul_index
    rw [hc, card_normalizer P] at hh
    omega
  apply le_antisymm ((pResidual_le_iff_isPGroup_quotient 2 R).mpr hquot)
  intro x hx
  have hd : orderOf x ∣ 5 := by
    have hh := orderOf_dvd_natCard (⟨x, hx⟩ : R)
    rwa [← Subgroup.orderOf_coe, hc] at hh
  exact mem_pResidual_of_orderOf_coprime ((by decide : Nat.Coprime 2 5).of_dvd_right hd)

/-- Ambient image form needed by the source five-normalizer consumer. -/
theorem residual_map_eq (P : Sylow 5 D) :
    (pResidual 2 (normalizer ((P : Subgroup D) : Set D))).map (normalizer ((P : Subgroup D) : Set D)).subtype =
      (P : Subgroup D) := by
  rw [residual_eq, map_subgroupOf_eq_of_le (P : Subgroup D).le_normalizer]

/-- A proper subgroup containing the actual five-normalizer equals it. -/
theorem eq_normalizer_of_proper (P : Sylow 5 D) (X : Subgroup D)
    (hNX : normalizer ((P : Subgroup D) : Set D) ≤ X) (hX : X ≠ ⊤) :
    X = normalizer ((P : Subgroup D) : Set D) := (overgroup_eq P X hNX).resolve_right hX

/-- For the actual quotient map in a source application, normalizer containment
and properness identify both the image and the image of its two-residual. -/
theorem image_and_residual_eq {H : Type*} [Group H] [Finite H]
    (P : Sylow 5 D) (f : H →* D) (X : Subgroup H)
    (hNX : normalizer ((P : Subgroup D) : Set D) ≤ X.map f)
    (hproper : X.map f ≠ ⊤) :
    X.map f = normalizer ((P : Subgroup D) : Set D) ∧
      ((pResidual 2 X).map X.subtype).map f = (P : Subgroup D) := by
  have he := eq_normalizer_of_proper P (X.map f) hNX hproper
  refine ⟨he, ?_⟩
  rw [map_embedded_pResidual, he]
  exact residual_map_eq P

end Theory.SpecificGroups.SymmetricFive.FiveNormalizerOvergroups
