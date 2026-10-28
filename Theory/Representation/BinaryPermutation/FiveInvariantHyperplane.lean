module
public import Theory.Representation.BinaryPermutation.FiveAction
public import Mathlib.GroupTheory.Index
/-!
# Pointwise fixers of invariant hyperplanes in the binary five-point core

A nonidentity permutation fixing an order-eight subgroup pointwise is a
transposition. Every permutation preserving that hyperplane then fixes the
corresponding weight-two vector. Thus a common Sylow-invariant hyperplane
has trivial pointwise fixer whenever the Sylow subgroup fixes no nonsingular
vector. The public theorem supplies the exact alternative used by that argument.

The bounded checks use the 120 permutations and 32 binary words; no subgroup
lattice is enumerated. Source application: Aschbacher–Smith 13.2.3(1) and
13.5.10, printed pp.878 and 918.
-/
@[expose] public section
open Subgroup BinaryPermutation
namespace BinaryPermutation.FiveInvariantHyperplane
abbrev Space := core (Fin 5)
abbrev Perm := Equiv.Perm (Fin 5)
def fixedWords (g : Perm) : Finset (Full (Fin 5)) :=
  Finset.univ.filter fun x => (∑ i, x i) = 0 ∧ representation (Fin 5) g x = x
private theorem fixed_test : ∀ g : Perm, 8 ≤ (fixedWords g).card →
    g = 1 ∨ ∃ i j : Fin 5, i ≠ j ∧ g = Equiv.swap i j := by decide +kernel
private theorem swap_card : ∀ i j : Fin 5, i ≠ j →
    (fixedWords (Equiv.swap i j)).card = 8 := by decide +kernel
private theorem swap_preserving : ∀ (i j : Fin 5) (p : Perm), i ≠ j →
    (fixedWords (Equiv.swap i j)).filter (fun x =>
      representation (Fin 5) (Equiv.swap i j) (representation (Fin 5) p x) ≠
        representation (Fin 5) p x) = ∅ →
    representation (Fin 5) p (fun k => if k = i ∨ k = j then 1 else 0) =
      (fun k => if k = i ∨ k = j then 1 else 0) := by decide +kernel


private def fixed (g : Perm) : Subgroup (Multiplicative Space) where
  carrier := {x | coreRepresentation (Fin 5) g x.toAdd = x.toAdd}
  one_mem' := map_zero _
  mul_mem' {x y} hx hy := by
    change coreRepresentation (Fin 5) g (x.toAdd + y.toAdd) = x.toAdd + y.toAdd
    rw [map_add, hx, hy]
  inv_mem' {x} hx := by
    change coreRepresentation (Fin 5) g (-x.toAdd) = -x.toAdd
    rw [map_neg, hx]

private theorem card_fixed (g : Perm) : Nat.card (fixed g) = (fixedWords g).card := by
  let e : fixed g ≃ {x // x ∈ fixedWords g} :=
    { toFun x := ⟨x.val.toAdd.val, Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, x.val.toAdd.property, congrArg Subtype.val x.property⟩⟩
      invFun x := ⟨Multiplicative.ofAdd ⟨x.val, (Finset.mem_filter.mp x.property).2.1⟩,
        Subtype.ext (Finset.mem_filter.mp x.property).2.2⟩
      left_inv _ := rfl
      right_inv _ := rfl }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe]

private def duad (i j : Fin 5) (h : i ≠ j) : Space :=
  ⟨fun k => if k = i ∨ k = j then 1 else 0, by
    have hh : ∀ i j : Fin 5, i ≠ j →
        (∑ k : Fin 5, (if k = i ∨ k = j then 1 else 0 : ZMod 2)) = 0 := by decide
    exact hh i j h⟩

private theorem duad_nonsingular (i j : Fin 5) (h : i ≠ j) :
    FiveGeometry.form (duad i j h) ≠ 0 := by
  have hh : ∀ (i j : Fin 5) (h : i ≠ j), FiveGeometry.form (duad i j h) ≠ 0 := by decide
  exact hh i j h

/-- A nontrivial pointwise fixer of an invariant hyperplane supplies a common
nonsingular fixed vector for every actor preserving that hyperplane. -/
theorem fixed_hyperplane_dichotomy (P : Set Perm)
    (W : Subgroup (Multiplicative Space)) (hW : Nat.card W = 8)
    (hP : ∀ p ∈ P, ∀ x ∈ W,
      Multiplicative.ofAdd (coreRepresentation (Fin 5) p x.toAdd) ∈ W)
    (g : Perm) (hg : ∀ x ∈ W, coreRepresentation (Fin 5) g x.toAdd = x.toAdd) :
    g = 1 ∨ ∃ x : Space, FiveGeometry.form x ≠ 0 ∧
      ∀ p ∈ P, coreRepresentation (Fin 5) p x = x := by
  have hle : W ≤ fixed g := hg
  have hc : 8 ≤ (fixedWords g).card := by
    rw [← card_fixed, ← hW]
    exact Nat.card_le_card_of_injective (inclusion hle)
      (Subgroup.inclusion_injective hle)
  rcases fixed_test g hc with he | ⟨i,j,hij,rfl⟩
  · exact Or.inl he
  · right
    have hWF : W = fixed (Equiv.swap i j) :=
      eq_of_le_of_card_ge hle (by rw [card_fixed, swap_card i j hij, hW])
    refine ⟨duad i j hij, duad_nonsingular i j hij, ?_⟩
    intro p hp
    apply Subtype.ext
    apply swap_preserving i j p hij
    apply Finset.filter_eq_empty_iff.mpr
    intro x hxmem
    apply not_ne_iff.mpr
    obtain ⟨hx,hfix⟩ := (Finset.mem_filter.mp hxmem).2
    let v : Multiplicative Space := Multiplicative.ofAdd ⟨x,hx⟩
    have hv : v ∈ W := hWF.symm ▸ (show v ∈ fixed (Equiv.swap i j) from Subtype.ext hfix)
    exact congrArg Subtype.val (hg _ (hP p hp v hv))
end BinaryPermutation.FiveInvariantHyperplane
