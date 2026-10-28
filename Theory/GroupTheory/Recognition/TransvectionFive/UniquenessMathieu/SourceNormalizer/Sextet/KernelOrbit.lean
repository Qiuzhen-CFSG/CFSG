module
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.SourceNormalizer.Sextet.Kernel

/-!
# Transitivity of the cubic kernel on each exceptional triple

The six-point kernel is free on every nonzero vector. Once its order is
three, evaluation on a nonzero vector of one of the six lines is a bijection
with that line's nonzero part. This supplies the product decomposition in
the ambient four-subgroup normalizer.

Source: Aschbacher, *Sporadic Groups* (1994), 40.4(2), p.218.
-/

public noncomputable section
namespace Theory.GroupTheory.TransvectionFive.UniquenessMathieu.SourceNormalizer.Sextet
open UniquenessLinear.PlaneCensus (Code)

private theorem nonzero_line_card (i : Fin 6) :
    Nat.card {y : Code // y ∈ line i ∧ y ≠ 0} = 3 := by
  rw [Nat.card_eq_fintype_card]
  have h : ∀ i : Fin 6, Fintype.card {y : Code // y ∈ line i ∧ y ≠ 0} = 3 := by decide +kernel
  exact h i

/-- The cubic kernel acts transitively on the three nonzero vectors of each
of the six literal four-element lines. -/
theorem kernel_transitive_line (hcard : Nat.card action.ker = 3)
    (i : Fin 6) (x : Code) (hx : x ∈ line i) (hx0 : x ≠ 0)
    (y : Code) (hy : y ∈ line i) (hy0 : y ≠ 0) :
    ∃ k : action.ker, k.val.val x = y := by
  let ev : action.ker → {y : Code // y ∈ line i ∧ y ≠ 0} := fun k =>
    ⟨k.val.val x, by
      have hm := (action_mem_line k.val i x).mpr hx
      have he : action k.val = 1 := k.property
      simpa only [he, Equiv.Perm.one_apply] using hm,
      fun hz => hx0 (k.val.val.injective (hz.trans (symmetry_zero k.val).symm))⟩
  have hinj : Function.Injective ev := by
    intro k l he
    have hv : k.val.val x = l.val.val x := congrArg Subtype.val he
    have hkl : (l⁻¹ * k : action.ker) = 1 := kernel_fix_nonzero _ x hx0 (by
      change l.val.val.symm (k.val.val x) = x
      rw [hv, l.val.val.symm_apply_apply])
    exact (inv_mul_eq_one.mp hkl).symm
  have hsurj : Function.Surjective ev :=
    (hinj.bijective_of_nat_card_le (by rw [nonzero_line_card, hcard])).2
  obtain ⟨k,hk⟩ := hsurj ⟨y,hy,hy0⟩
  exact ⟨k, congrArg Subtype.val hk⟩

end Theory.GroupTheory.TransvectionFive.UniquenessMathieu.SourceNormalizer.Sextet
