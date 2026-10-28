module

public import Theory.Representation.BinaryOffender.SubspaceAction
public import Theory.Representation.BinaryOffender.CodimensionSieve

/-!
# Pointwise centralizers on two sections separated by a line

Suppose fixed vectors lift through a subrepresentation W, and a subgroup B
moves the ambient fixed space only into a subspace of dimension at most one.
If that line lies in W, B fixes the fixed space of the quotient. Otherwise
its intersection with W is zero, so B fixes the fixed space inside W.

This is the linear passage from 13.8.23(3) to its pointwise-centralizer
conclusion in Aschbacher–Smith, *The Classification of Quasithin Groups*,
combined manuscript (1 March 2004), printed p.958.
-/

public section

open Subgroup
namespace Representation.BinaryOffender
variable {H U : Type*} [Group H] [AddCommGroup U] [Module (ZMod 2) U]
  [FiniteDimensional (ZMod 2) U]

/-- The literal pointwise kernels on the submodule and quotient give the
two alternatives; no faithfulness or representation model is required. -/
theorem fixedSpace_kernel_dichotomy (ρ : Representation (ZMod 2) H U)
    (W : Subrepresentation ρ) (A B : Subgroup H) (S : Submodule (ZMod 2) U)
    (hS : Module.finrank (ZMod 2) S ≤ 1)
    (hlift : (fixedSpace ρ A).map W.toSubmodule.mkQ = fixedSpace W.quotientRepresentation A)
    (hdisp : ∀ b ∈ B, ∀ v ∈ fixedSpace ρ A, ρ b v - v ∈ S) :
    B ≤ subspaceKernel W.toRepresentation (fixedSpace W.toRepresentation A) ⊤ ∨
    B ≤ subspaceKernel W.quotientRepresentation (fixedSpace W.quotientRepresentation A) ⊤ := by
  by_cases hSW : S ≤ W.toSubmodule
  · right
    intro b hb
    refine ⟨mem_top _, ?_⟩
    intro q hq
    rw [← hlift] at hq
    obtain ⟨v, hv, rfl⟩ := hq
    change W.toSubmodule.mkQ (ρ b v) = W.toSubmodule.mkQ v
    apply sub_eq_zero.mp
    rw [← map_sub]
    exact (Submodule.Quotient.mk_eq_zero _).mpr (hSW (hdisp b hb v hv))
  · left
    have hdis : Disjoint S W.toSubmodule := by
      by_cases hzero : S = ⊥
      · exact (hSW (hzero ▸ bot_le)).elim
      have hr : Module.finrank (ZMod 2) S = 1 := by
        have hp : 0 < Module.finrank (ZMod 2) S :=
          Nat.pos_of_ne_zero (fun he => hzero (Submodule.finrank_eq_zero.mp he))
        omega
      exact (Submodule.isAtom_iff_finrank_eq_one.mpr hr).not_le_iff_disjoint.mp hSW
    intro b hb
    refine ⟨mem_top _, ?_⟩
    intro w hw
    apply Subtype.ext
    apply sub_eq_zero.mp
    apply Submodule.disjoint_def.mp hdis
    · apply hdisp b hb
      intro a
      exact congrArg Subtype.val (hw a)
    · exact W.toSubmodule.sub_mem (W.apply_mem_toSubmodule b w.property) w.property

end Representation.BinaryOffender
