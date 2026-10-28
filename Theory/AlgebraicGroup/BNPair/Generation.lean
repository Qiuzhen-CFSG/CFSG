module

public import Theory.AlgebraicGroup.BNPair.Defs

/-! Monoid generation by the distinguished involutions of a Tits system. -/

namespace Theory.AlgebraicGroup.TitsSystem

variable {X : Type*} [Group X]

/-- Since the distinguished generators are involutions, they generate the
quotient as a monoid as well as a group. -/
public lemma submonoid_closure_S_eq_top (T : TitsSystem (X := X)) :
    Submonoid.closure T.S = ⊤ := by
  let M := Submonoid.closure T.S
  have hmem : ∀ w ∈ Subgroup.closure T.S, w ∈ M ∧ w⁻¹ ∈ M := by
    intro w hw
    induction hw using Subgroup.closure_induction with
    | mem s hs =>
        have hsM : s ∈ M := Submonoid.subset_closure hs
        have hsInv : s⁻¹ = s :=
          mul_eq_one_iff_inv_eq.mp
            (by simpa only [pow_two] using (T.involutions s hs).2)
        refine ⟨hsM, ?_⟩
        rw [hsInv]
        exact hsM
    | one => exact ⟨M.one_mem, by rw [inv_one]; exact M.one_mem⟩
    | mul x y hx hy ihx ihy =>
        refine ⟨M.mul_mem ihx.1 ihy.1, ?_⟩
        rw [mul_inv_rev]
        exact M.mul_mem ihy.2 ihx.2
    | inv x hx ih => exact ⟨ih.2, by simpa using ih.1⟩
  apply top_unique
  intro w hw
  exact (hmem w (by rw [T.quotient_generate]; exact Subgroup.mem_top w)).1

end Theory.AlgebraicGroup.TitsSystem
