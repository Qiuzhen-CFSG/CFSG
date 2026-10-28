module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.GroupTheory.Index

/-!
# No subgroups of index two in SL2

Over a field where two is nonzero, SL2 has no subgroup of index two. This
includes the field of three elements and requires no finiteness assumption.
The result supplies the no-index-two property of the SL2 lift used in ABG
Chapter II, Section 3, Proposition 2 (article p.22).

Every square belongs to a subgroup of index two. Each transvection with
coefficient c is the square of the transvection with coefficient c/2, by the
additive transvection formula. Mathlib's transvection generation theorem for
SL2 then forces the subgroup to be the whole group.
-/

namespace Matrix.SpecialLinearGroup

/-- SL2 over a field where two is nonzero has no subgroup of index two. -/
public theorem index_ne_two {F : Type*} [Field F] (hF : (2 : F) ≠ 0)
    (L : Subgroup (SpecialLinearGroup (Fin 2) F)) : L.index ≠ 2 := by
  intro hL
  have htop : L = ⊤ := by
    apply top_unique
    intro A _
    apply Matrix.SL2.transvection_induction (fun A => A ∈ L) ?_ ?_ A
    · intro i j hij c
      have hsq := L.sq_mem_of_index_two hL (transvection hij (c / 2))
      simpa only [pow_two, ← transvection_add, ← mul_two,
        div_mul_cancel₀ c hF] using hsq
    · intro A B hA hB
      exact L.mul_mem hA hB
  simp [htop] at hL

end Matrix.SpecialLinearGroup
