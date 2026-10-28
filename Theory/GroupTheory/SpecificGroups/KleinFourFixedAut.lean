module
public import Mathlib.GroupTheory.SpecificGroups.KleinFour
public import Mathlib.Data.Fintype.Perm
public import Mathlib.GroupTheory.PGroup

/-!
# Klein four automorphisms fixing a nonidentity element

A subgroup of automorphisms of a Klein four group that fixes a nonidentity
element is a two-group. Restrict each automorphism to the complement of the
identity and the fixed element. This complement has two elements, and the
restriction is injective because the two omitted elements are already fixed.
Thus the automorphism subgroup has order at most two, and its positive order
is a power of two.

This elementary stabilizer calculation is used in the automorphism analysis of
abelian two-groups with unequal cyclic factors and the wreathed subgroup
arguments of Alperin–Brauer–Gorenstein, Chapter II §1, Lemma 3. It requires
only the abstract Klein four instance and the common fixed element.
-/

namespace IsKleinFour
variable {V : Type*} [Group V] [IsKleinFour V]

public theorem isPGroup_aut_subgroup_of_fixed_ne_one
    (A : Subgroup (MulAut V)) {v : V} (hv : v ≠ 1)
    (hfix : ∀ f ∈ A, f v = v) : IsPGroup 2 A := by
  classical
  let : Fintype V := Fintype.ofFinite V
  let R := {x : V // x ∉ ({1, v} : Set V)}
  have hp (f : A) (x : V) :
      ((f : MulAut V) x ∉ ({1, v} : Set V)) ↔ x ∉ ({1, v} : Set V) := by
    have hf := hfix f f.property
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rw [← hf, f.val.injective.eq_iff]
    simp [hf]
  let restrict : A → Equiv.Perm R := fun f =>
    Equiv.Perm.subtypePerm f.val.toEquiv (hp f)
  have hinj : Function.Injective restrict := by
    intro f g h
    apply Subtype.ext
    apply MulEquiv.ext
    intro x
    by_cases hx : x = 1
    · subst x; simp
    by_cases hxv : x = v
    · subst x; rw [hfix f f.property, hfix g g.property]
    have hr : x ∉ ({1, v} : Set V) := by simpa using And.intro hx hxv
    exact congrArg Subtype.val (Equiv.congr_fun h (⟨x, hr⟩ : R))
  have hcardR : Fintype.card R = 2 := by
    dsimp [R]
    rw [Fintype.card_subtype_compl]
    have hc : Nat.card {x : V // x ∈ ({1, v} : Set V)} = 2 := by
      rw [Nat.card_coe_set_eq]
      simp [Ne.symm hv]
    simp only [← Nat.card_eq_fintype_card, hc, IsKleinFour.card_four]
  have hcard : Nat.card A ≤ 2 := by
    have h := Nat.card_le_card_of_injective restrict hinj
    simpa only [Nat.card_eq_fintype_card, Fintype.card_perm, hcardR,
      Nat.factorial_two] using h
  have hpos : 0 < Nat.card A := Nat.card_pos
  apply IsPGroup.of_card_dvd_pow (n := 1)
  have hcases : Nat.card A = 1 ∨ Nat.card A = 2 := by omega
  rcases hcases with h | h <;> simp only [h, pow_one, one_dvd, dvd_refl]

end IsKleinFour
