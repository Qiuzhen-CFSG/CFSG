module
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
/-!
# The three lines of a quotient of order four

A subgroup of order two has a unique nonidentity element. Hence a group of
order four has at most three such subgroups. Pulling this observation back
through the actual quotient map exhausts three distinct overgroups of a
normal subgroup. This is the subgroup-lattice step in quasithin 13.9.8.
-/
public section
open Subgroup

private theorem card_two_subgroups_bound (H : Type*) [Group H] [Finite H]
    (hH : Nat.card H = 4) : Nat.card {E : Subgroup H // Nat.card E = 2} ≤ 3 := by
  classical
  let I := {E : Subgroup H // Nat.card E = 2}
  have hex (E : I) : ∃ x : E.val, x ≠ 1 := by
    let : Nontrivial E.val := Finite.one_lt_card_iff_nontrivial.mp (by rw [E.property]; decide)
    exact exists_ne 1
  let f : I → {x : H // x ≠ 1} := fun E =>
    ⟨(Classical.choose (hex E)).val,fun h => Classical.choose_spec (hex E) (Subtype.ext h)⟩
  have hgen (E : I) : E.val = zpowers (f E).val := by
    apply le_antisymm
    · intro x hx
      obtain ⟨n,hn⟩ := mem_zpowers_iff.mp (mem_zpowers_of_prime_card E.property
        (Classical.choose_spec (hex E)) (g' := (⟨x,hx⟩ : E.val)))
      exact mem_zpowers_iff.mpr ⟨n,congrArg Subtype.val hn⟩
    · exact zpowers_le.mpr (Classical.choose (hex E)).property
  have hi : Function.Injective f := by
    intro E F h
    apply Subtype.ext
    rw [hgen E,hgen F,h]
  have hh := Nat.card_le_card_of_injective f hi
  have hc : Nat.card {x : H // x ≠ 1} = 3 := by
    let : Fintype H := Fintype.ofFinite H
    rw [Nat.card_eq_fintype_card,Fintype.card_subtype_compl]
    simp only [Fintype.card_unique]
    rw [← Nat.card_eq_fintype_card,hH]
  exact hc ▸ hh

private theorem three_card_two_exhaust (H : Type*) [Group H] [Finite H]
    (hH : Nat.card H = 4) (E1 E2 E3 E : Subgroup H)
    (h1 : Nat.card E1 = 2) (h2 : Nat.card E2 = 2) (h3 : Nat.card E3 = 2)
    (hE : Nat.card E = 2) (h12 : E1 ≠ E2) (h13 : E1 ≠ E3) (h23 : E2 ≠ E3) :
    E = E1 ∨ E = E2 ∨ E = E3 := by
  classical
  by_contra! hn
  let I := {A : Subgroup H // Nat.card A = 2}
  let : Finite (Subgroup H) := Finite.of_injective (fun A : Subgroup H => (A : Set H)) SetLike.coe_injective
  let : Fintype I := Fintype.ofFinite I
  let x1 : I := ⟨E1,h1⟩
  let x2 : I := ⟨E2,h2⟩
  let x3 : I := ⟨E3,h3⟩
  let x : I := ⟨E,hE⟩
  have hx12 : x1 ≠ x2 := fun hh => h12 (congrArg Subtype.val hh)
  have hx13 : x1 ≠ x3 := fun hh => h13 (congrArg Subtype.val hh)
  have hx23 : x2 ≠ x3 := fun hh => h23 (congrArg Subtype.val hh)
  have hxx1 : x ≠ x1 := fun hh => hn.1 (congrArg Subtype.val hh)
  have hxx2 : x ≠ x2 := fun hh => hn.2.1 (congrArg Subtype.val hh)
  have hxx3 : x ≠ x3 := fun hh => hn.2.2 (congrArg Subtype.val hh)
  have hc : ({x,x1,x2,x3} : Finset I).card = 4 := by
    simp [hx12,hx13,hx23,hxx1,hxx2,hxx3]
  have hh := Finset.card_le_card (Finset.subset_univ ({x,x1,x2,x3} : Finset I))
  rw [hc,Finset.card_univ,← Nat.card_eq_fintype_card] at hh
  have hb : Nat.card I ≤ 3 := card_two_subgroups_bound H hH
  omega

/-- The three distinct subgroups with quotient order two exhaust the overgroups
of a normal subgroup whose quotient has order four. -/
theorem Subgroup.eq_one_of_three_overgroups_of_quotient_card_four
    {H : Type*} [Group H] [Finite H] (N : Subgroup H) [N.Normal]
    (hH : Nat.card (H ⧸ N) = 4) (E1 E2 E3 E : Subgroup H)
    (hN1 : N ≤ E1) (hN2 : N ≤ E2) (hN3 : N ≤ E3) (hNE : N ≤ E)
    (h1 : N.relIndex E1 = 2) (h2 : N.relIndex E2 = 2) (h3 : N.relIndex E3 = 2)
    (hE : N.relIndex E = 2) (h12 : E1 ≠ E2) (h13 : E1 ≠ E3) (h23 : E2 ≠ E3) :
    E = E1 ∨ E = E2 ∨ E = E3 := by
  let π := QuotientGroup.mk' N
  have he (A B : Subgroup H) (hNA : N ≤ A) (hNB : N ≤ B) :
      A.map π = B.map π ↔ A = B := by
    constructor
    · intro hh
      have ha : (A.map π).comap π = A := comap_map_eq_self (by rwa [QuotientGroup.ker_mk'])
      have hb : (B.map π).comap π = B := comap_map_eq_self (by rwa [QuotientGroup.ker_mk'])
      exact ha.symm.trans ((congrArg (Subgroup.comap π) hh).trans hb)
    · rintro rfl; rfl
  have hc (A : Subgroup H) (hA : N.relIndex A = 2) : Nat.card (A.map π) = 2 := by
    rw [← relIndex_ker,QuotientGroup.ker_mk']
    exact hA
  rcases three_card_two_exhaust (H ⧸ N) hH (E1.map π) (E2.map π) (E3.map π) (E.map π)
      (hc E1 h1) (hc E2 h2) (hc E3 h3) (hc E hE)
      (fun hh => h12 ((he E1 E2 hN1 hN2).mp hh))
      (fun hh => h13 ((he E1 E3 hN1 hN3).mp hh))
      (fun hh => h23 ((he E2 E3 hN2 hN3).mp hh)) with h | h | h
  · exact Or.inl ((he E E1 hNE hN1).mp h)
  · exact Or.inr (Or.inl ((he E E2 hNE hN2).mp h))
  · exact Or.inr (Or.inr ((he E E3 hNE hN3).mp h))
