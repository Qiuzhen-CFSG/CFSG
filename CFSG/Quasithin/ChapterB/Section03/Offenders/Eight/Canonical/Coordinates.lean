module

public import CFSG.Quasithin.ChapterB.Section03.Offenders.Eight.Canonical.Representatives
import Mathlib.Data.Fintype.Pi

/-!
# Binary coordinates on the disjoint-swap group

The binary support of the independent swaps gives an actual multiplicative
isomorphism from `C₂⁴` to `D`. Restricting the sixteen-element table by permutation
sign counts the even part, without enumerating the ambient symmetric group.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
Proposition B.3.2, printed pp. 83–84.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterB.Offenders.Eight
open Representation.BinaryOffender

/-- The four binary swap coordinates, with addition written multiplicatively. -/
abbrev BinaryFour := Multiplicative (Fin 4 → ZMod 2)

/-- Interpret a binary vector as the corresponding product of disjoint swaps. -/
def binaryPermutation : BinaryFour →* Perm where
  toFun x := dWords (finFunctionFinEquiv (Multiplicative.toAdd x))
  map_one' := by decide +kernel
  map_mul' := by decide +kernel

theorem binaryPermutation_injective : Function.Injective binaryPermutation := by
  intro x y h
  have he := finFunctionFinEquiv.injective (dWords_injective h)
  exact he

theorem mem_D_iff (g : Perm) : g ∈ D 8 ↔ ∃ i, dWords i = g :=
  mem_disjointTranspositions_iff 4 g

theorem binaryPermutation_range : binaryPermutation.range = D 8 := by
  ext g
  rw [mem_D_iff]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨finFunctionFinEquiv (Multiplicative.toAdd x), rfl⟩
  · rintro ⟨i, rfl⟩
    refine ⟨Multiplicative.ofAdd ((finFunctionFinEquiv (m := 2) (n := 4)).symm i), ?_⟩
    exact congrArg dWords ((finFunctionFinEquiv (m := 2) (n := 4)).apply_symm_apply i)

/-- The independent swaps identify `D` with a four-dimensional binary group. -/
noncomputable def binaryEquivD : BinaryFour ≃* D 8 :=
  (MonoidHom.ofInjective binaryPermutation_injective).trans
    (MulEquiv.subgroupCongr binaryPermutation_range)

/-- A direct equivalence between the sixteen binary words and `D`. -/
noncomputable def wordsEquivD : Fin 16 ≃ D 8 where
  toFun i := ⟨dWords i, (mem_D_iff _).mpr ⟨i, rfl⟩⟩
  invFun g := (finFunctionFinEquiv (Multiplicative.toAdd (binaryEquivD.symm g)))
  left_inv i := by
    apply dWords_injective
    change (binaryEquivD (binaryEquivD.symm ⟨dWords i, _⟩)).val = dWords i
    simp
  right_inv g := by
    change binaryEquivD (binaryEquivD.symm g) = g
    simp

/-- The even part of `D` has eight elements. -/
theorem card_evenPart : Nat.card (evenPart 8) = 8 := by
  let e : {i : Fin 16 // Equiv.Perm.sign (dWords i) = 1} ≃ evenPart 8 :=
    { toFun := fun i => ⟨dWords i.val, (mem_D_iff _).mpr ⟨i.val, rfl⟩, i.property⟩
      invFun := fun g => ⟨wordsEquivD.symm ⟨g.val, g.property.1⟩, by
        have h := congrArg (fun x : D 8 => (x : Perm)) (wordsEquivD.apply_symm_apply ⟨g.val, g.property.1⟩)
        change Equiv.Perm.sign (dWords _) = 1
        rw [show dWords (wordsEquivD.symm ⟨g.val, g.property.1⟩) = g.val from h]
        exact g.property.2⟩
      left_inv := fun i => Subtype.ext (wordsEquivD.symm_apply_apply i.val)
      right_inv := fun g => Subtype.ext
        (congrArg (fun x : D 8 => (x : Perm)) (wordsEquivD.apply_symm_apply ⟨g.val, g.property.1⟩)) }
  rw [← Nat.card_congr e, Nat.card_eq_fintype_card]
  decide +kernel

theorem rank_evenPart : rank (evenPart 8) = 3 :=
  rank_eq_of_card_eq_two_pow card_evenPart

theorem isElementaryTwo_evenPart : IsElementaryTwo (evenPart 8) := by
  apply isElementaryTwo_D8.of_le inf_le_left
  intro h
  have hc := card_evenPart
  change evenPart 8 = ⊥ at h
  rw [h, Subgroup.card_bot] at hc
  contradiction

end CFSG.Quasithin.ChapterB.Offenders.Eight
