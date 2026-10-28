module
public import Theory.Representation.BinarySevenCode.PermutationAction
public import Mathlib.GroupTheory.SpecificGroups.Alternating.MaximalSubgroups
public import Mathlib.Algebra.Group.Subgroup.Order

/-!
# Maximal stabilizers of nonzero even binary words

A nonzero even word on seven letters has a nonempty proper support.
Its A₇ stabilizer is the support's setwise stabilizer, hence maximal by
Mathlib's intransitive maximal-subgroup theorem: seven cannot be twice
the support size. Surjective pullback preserves this maximality.

The source application is the natural-module point centralizer in the
proper branch of Aschbacher--Smith 12.3.12, printed p.811, using the
omega-center decomposition in 12.3.7(1), printed p.809.
-/

public section
open Subgroup MulAction
open scoped Pointwise
namespace BinarySevenCode

private theorem fixes_word_iff_stabilizes_support
    (a : alternatingGroup (Fin 7)) (w : EvenWord) :
    evenRepresentation a.val w = w ↔
      a ∈ MulAction.stabilizer (alternatingGroup (Fin 7)) {i | w.val i ≠ 0} := by
  rw [MulAction.mem_stabilizer_iff, Set.ext_iff]
  constructor
  · intro h i
    rw [Set.mem_smul_set_iff_inv_smul_mem]
    change w.val (a.val.symm i) ≠ 0 ↔ w.val i ≠ 0
    have hi := congrArg (fun v : EvenWord => v.val i) h
    change w.val (a.val.symm i) = w.val i at hi
    rw [hi]
  · intro h
    apply Subtype.ext
    funext i
    apply (by decide : ∀ x y : ZMod 2, (x ≠ 0 ↔ y ≠ 0) → x = y)
    have hi := h i
    rw [Set.mem_smul_set_iff_inv_smul_mem] at hi
    exact hi

/-- Every nonzero point stabilizer in the natural binary A7 module is maximal. -/
theorem isCoatom_of_mem_iff_fixes_evenWord {H : Type*} [Group H]
    (q : H →* alternatingGroup (Fin 7)) (hq : Function.Surjective q)
    (w : EvenWord) (hw : w ≠ 0) (C : Subgroup H)
    (hC : ∀ x, x ∈ C ↔ evenRepresentation (q x).val w = w) : IsCoatom C := by
  let s : Set (Fin 7) := {i | w.val i ≠ 0}
  have he : C = (MulAction.stabilizer (alternatingGroup (Fin 7)) s).comap q := by
    ext x
    exact (hC x).trans (fixes_word_iff_stabilizes_support (q x) w)
  rw [he]
  apply Subgroup.isCoatom_comap_of_surjective hq
  apply alternatingGroup.isCoatom_stabilizer
  · apply Set.nonempty_iff_ne_empty.mpr
    intro h
    apply hw
    apply Subtype.ext
    funext i
    have hn : i ∉ s := by rw [h]; exact Set.notMem_empty i
    exact not_not.mp hn
  · have hw' : w.val ≠ 0 := fun h => hw (Subtype.ext h)
    have hh := weight_of_mem_evenWords w.property hw'
    apply Set.nonempty_iff_ne_empty.mpr
    intro h
    have hweight : weight w.val = 7 := by
      unfold weight
      have hf : Finset.univ.filter (fun i => w.val i ≠ 0) = Finset.univ := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
        have hn : i ∉ sᶜ := by rw [h]; exact Set.notMem_empty i
        exact not_not.mp hn
      rw [hf]
      rfl
    omega
  · simp only [Nat.card_fin]
    omega
end BinarySevenCode
