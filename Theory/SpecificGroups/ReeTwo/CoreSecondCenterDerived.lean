module

public import Theory.SpecificGroups.ReeTwo.CoreRootConjugacy
public import Mathlib.GroupTheory.Nilpotent

/-!
# The second center of the Ree two core

The first five coordinates give the abelian head of the core. Commutation
modulo the final root with the five initial roots forces this head to vanish.
The remaining roots are commutators, so the second center is derived.

Source: Shinoda (1975), (2.3), pp. 81-82, through the collected multiplication
in `ReeTwo.Core`.
-/

namespace ReeTwo.Core
open Subgroup
open scoped commutatorElement

private theorem center_cases (g : Core) (hg : g ∈ center Core) :
    g = 1 ∨ g = root 9 := by
  have h (i : CoreRoot) : root i * g = g * root i :=
    mem_center_iff.mp hg (root i)
  exact (by decide +kernel : ∀ g : Core,
    (∀ i : CoreRoot, root i * g = g * root i) → g = 1 ∨ g = root 9) g h

private def commuteModLast (x y : Core) : Prop :=
  x * y = y * x ∨ x * y = root 9 * (y * x)

private instance (x y : Core) : Decidable (commuteModLast x y) := by
  unfold commuteModLast
  infer_instance

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem second_center_head_test : ∀ g : Core,
    (∀ i : Fin 5, commuteModLast g (root ⟨i.val, by omega⟩)) →
      g.b0 = 0 ∧ g.b1 = 0 ∧ g.b2 = 0 ∧ g.b3 = 0 ∧ g.b4 = 0 := by
  decide +kernel

private theorem commuteModLast_of_second_center (g : Core)
    (hg : g ∈ Subgroup.upperCentralSeries Core 2) (y : Core) : commuteModLast g y := by
  have h := Subgroup.mem_upperCentralSeries_succ_iff.mp hg y
  rw [Subgroup.upperCentralSeries_one] at h
  rcases center_cases _ h with h | h
  · left
    have he := congrArg (fun t => t * y * g) h
    simpa [commutatorElement_def, mul_assoc] using he
  · right
    have he := congrArg (fun t => t * y * g) h
    simpa [commutatorElement_def, mul_assoc] using he

private theorem root_mem_derived (i : Fin 5) :
    root ⟨5 + i.val, by omega⟩ ∈ commutator Core := by
  have h (a b : Core) : rightComm a b ∈ commutator Core := by
    simpa [rightComm, commutatorElement_def, _root_.commutator_def] using
      (commutator_mem_commutator (show a⁻¹ ∈ (⊤ : Subgroup Core) from trivial)
        (show b⁻¹ ∈ (⊤ : Subgroup Core) from trivial))
  have h5 : rightComm (root 0) (root 2) = root 5 := by decide +kernel
  have h6 : rightComm (root 1) (root 2) = root 6 := by decide +kernel
  have h7 : rightComm (root 2) (root 3) = root 7 := by decide +kernel
  have h8 : rightComm (root 2) (root 4) = root 8 := by decide +kernel
  have h9 : rightComm (root 0) (root 8) = root 9 := by decide +kernel
  fin_cases i
  · exact h5 ▸ h _ _
  · exact h6 ▸ h _ _
  · exact h7 ▸ h _ _
  · exact h8 ▸ h _ _
  · exact h9 ▸ h _ _

/-- The second center of the concrete Ree two core is contained in its
derived subgroup. -/
public theorem second_center_le_derived :
    Subgroup.upperCentralSeries Core 2 ≤ commutator Core := by
  intro g hg
  obtain ⟨h0, h1, h2, h3, h4⟩ :=
    second_center_head_test g (fun i =>
      commuteModLast_of_second_center g hg (root ⟨i.val, by omega⟩))
  have h5 := root_mem_derived 0
  have h6 := root_mem_derived 1
  have h7 := root_mem_derived 2
  have h8 := root_mem_derived 3
  have h9 := root_mem_derived 4
  have hn := normal_form g
  rw [h0, h1, h2, h3, h4] at hn
  simp only [ZMod.val_zero, pow_zero, one_mul] at hn
  exact hn ▸ (mul_mem (mul_mem (mul_mem (mul_mem
    (pow_mem h5 _) (pow_mem h6 _))
    (pow_mem h7 _)) (pow_mem h8 _))
    (pow_mem h9 _))

end ReeTwo.Core
