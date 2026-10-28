module

public import Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals.TreeSylow
public import Mathlib.GroupTheory.SpecificGroups.Alternating

/-!
# A fixed Sylow two-subgroup of A₈

The 64 even binary-tree words give exactly the intersection of the checked
binary-tree Sylow subgroup of S₈ with A₈. Injectivity of the word coordinates
and the order of A₈ certify that this is a Sylow two-subgroup. Both the
subgroup and its normal forms use actual even permutations on `Fin 8`.

Source application: Aschbacher–Smith, proof of 1.3.4, printed p.511;
GLS3, Table 5.3e, the octad stabilizer `E₁₆.A₈`.
-/

@[expose] public section
namespace Sporadic.Mathieu.M24LocalGeometry.PairOvergroups.Placement.EightPoint
open Subgroup
open Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals

abbrev Alt := alternatingGroup (Fin 8)
abbrev Sym := Equiv.Perm (Fin 8)

/-- The even permutations in the binary-tree Sylow subgroup. -/
def twoGroup : Subgroup Alt := treeGroup.subgroupOf (alternatingGroup (Fin 8))

/-- A binary-tree word with the first bottom-level bit chosen to make it even. -/
def evenIndex (i : Fin 64) : Fin 128 :=
  ⟨2 * (i.val % 8) + ((i.val % 2 + i.val / 2 % 2 + i.val / 4 % 2) % 2) +
    16 * (i.val / 8), by omega⟩

def twoWord (i : Fin 64) : Sym := treeWord (evenIndex i)

set_option maxRecDepth 10000 in
theorem twoWord_even : ∀ i, twoWord i ∈ alternatingGroup (Fin 8) := by
  change ∀ i, Equiv.Perm.sign (twoWord i) = 1
  decide +kernel

set_option maxRecDepth 10000 in
private theorem evenIndex_injective : Function.Injective evenIndex := by
  decide +kernel

private theorem twoWord_injective : Function.Injective twoWord :=
  treeWord_injective.comp evenIndex_injective

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem even_treeWord_covered : ∀ j : Fin 128,
    treeWord j ∈ alternatingGroup (Fin 8) → ∃ i : Fin 64, twoWord i = treeWord j := by
  change ∀ j : Fin 128, Equiv.Perm.sign (treeWord j) = 1 →
    ∃ i : Fin 64, twoWord i = treeWord j
  decide +kernel

def twoElement (i : Fin 64) : Alt := ⟨twoWord i, twoWord_even i⟩

theorem mem_twoGroup (g : Alt) : g ∈ twoGroup ↔ ∃ i, twoElement i = g := by
  constructor
  · intro hg
    obtain ⟨j, hj⟩ := (mem_treeGroup g.val).mp hg
    obtain ⟨i, hi⟩ := even_treeWord_covered j (hj ▸ g.property)
    exact ⟨i, Subtype.ext (hi.trans hj)⟩
  · rintro ⟨i, rfl⟩
    exact treeWord_mem (evenIndex i)

/-- Read the binary-tree coordinates, discarding the parity-determined bit.
For an arbitrary permutation this returns only a candidate coordinate. -/
def twoIndex (g : Sym) : Fin 64 :=
  ⟨(((g⁻¹ 0).val % 2 + 2 * ((g⁻¹ 2).val % 2) +
      4 * ((g⁻¹ 4).val % 2) + 8 * ((g⁻¹ 6).val % 2) +
      16 * ((g⁻¹ 0).val / 2 % 2) + 32 * ((g⁻¹ 4).val / 2 % 2) +
      64 * ((g⁻¹ 0).val / 4)) / 2) % 64, Nat.mod_lt _ (by decide)⟩

set_option maxRecDepth 10000 in
theorem twoIndex_word : ∀ i, twoIndex (twoWord i) = i := by
  decide +kernel

/-- Membership can be tested by reconstructing one word, without searching 64 words. -/
theorem mem_twoGroup_iff_test (g : Alt) :
    g ∈ twoGroup ↔ twoWord (twoIndex g.val) = g.val := by
  rw [mem_twoGroup]
  constructor
  · rintro ⟨i, rfl⟩
    exact congrArg twoWord (twoIndex_word i)
  · intro h
    exact ⟨twoIndex g.val, Subtype.ext h⟩

theorem twoElement_injective : Function.Injective twoElement := by
  intro i j h
  exact twoWord_injective (congrArg Subtype.val h)

theorem card_twoGroup : Nat.card twoGroup = 64 := by
  have e : twoGroup ≃ Set.range twoElement :=
    Equiv.setCongr (by ext g; exact mem_twoGroup g)
  rw [Nat.card_congr e,
    ← Nat.card_congr (Equiv.ofInjective twoElement twoElement_injective)]
  simp

theorem card_alt : Nat.card Alt = 20160 := by
  change Nat.card (alternatingGroup (Fin 8)) = 20160
  rw [nat_card_alternatingGroup]
  norm_num [Nat.factorial]

theorem two_multiplicity : 2 ^ (Nat.card Alt).factorization 2 = 64 := by
  rw [card_alt, show 20160 = 2 ^ 6 * 315 by decide,
    Nat.factorization_mul (by decide) (by decide), Nat.factorization_pow]
  norm_num [Nat.prime_two.factorization,
    Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 2 ∣ 315)]

noncomputable def twoSylow : Sylow 2 Alt :=
  Sylow.ofCard twoGroup (card_twoGroup.trans two_multiplicity.symm)

@[simp] theorem twoSylow_coe : (twoSylow : Subgroup Alt) = twoGroup := rfl

end Sporadic.Mathieu.M24LocalGeometry.PairOvergroups.Placement.EightPoint
end
