module

public import Theory.SpecificGroups.Janko3.Model.Order.Level0.Consequences
public import Theory.SpecificGroups.Janko3.Model.Order.Terminal
public import Theory.SpecificGroups.Janko3.Model.Order.Level0.InverseChecks
import Mathlib.Tactic.FinCases

/-!
# Recovering the inverse J3 Schreier transitions

Generator A is an involution, and its two published transition rows coincide.
For B inverse, the index table inverts the forward index table. The two factor
words lie in H1. Once the second stabilizer step is certified, an element of H1
fixing 1 and 2 is trivial, so two-point checks certify that these factors cancel.
This avoids testing the full 6156-letter permutations again for inverse B.
Source: ATLAS J3G1-p6156B0 and `Order/data/witnesses.json`.
-/

namespace Sporadic.Janko3.OrderCertificate.Level0
open Theory.GroupTheory
set_option maxRecDepth 40000
set_option Elab.async false

/-- The second chain step and the terminal base certificate give a two-point base for H1. -/
public theorem H1_base_trivial
    (hstab : H2 = H1 ⊓ MulAction.stabilizer (Equiv.Perm (Fin 6156)) (1 : Fin 6156))
    (g : H1) (h1 : (g : Equiv.Perm (Fin 6156)) 1 = 1)
    (h2 : (g : Equiv.Perm (Fin 6156)) 2 = 2) : g = 1 := by
  have hg : (g : Equiv.Perm (Fin 6156)) ∈ H2 := by
    rw [hstab]
    exact ⟨g.property, h1⟩
  have he := congrArg (fun k : H2 => (k : Equiv.Perm (Fin 6156)))
    (H2_base_trivial ⟨g, hg⟩ h2)
  exact Subtype.ext he

private theorem factor13_cancel
    (hstab : H2 = H1 ⊓ MulAction.stabilizer (Equiv.Perm (Fin 6156)) (1 : Fin 6156))
    (r : Fin 6156) :
    evalWord L1Gen (L0Factor 1 (L0Act 3 r)) * evalWord L1Gen (L0Factor 3 r) = 1 := by
  let g : H1 := ⟨evalWord L1Gen (L0Factor 1 (L0Act 3 r)) * evalWord L1Gen (L0Factor 3 r), H1.mul_mem
    (evalWord_mem_wordSubgroup L1Gen L1Inv L1Inv_spec _)
    (evalWord_mem_wordSubgroup L1Gen L1Inv L1Inv_spec _)⟩
  have h1 : (g : Equiv.Perm (Fin 6156)) 1 = 1 := factor13_fix r 0
  have h2 : (g : Equiv.Perm (Fin 6156)) 2 = 2 := factor13_fix r 1
  exact congrArg (fun k : H1 => (k : Equiv.Perm (Fin 6156)))
    (H1_base_trivial hstab g h1 h2)

/-- Two forward rows suffice for the exact four-row certificate supplied in the data. -/
public theorem steps_of_forward
    (h0 : ∀ r, L0Gen 0 * L0Rep r = L0Rep (L0Act 0 r) * evalWord L1Gen (L0Factor 0 r))
    (h1 : ∀ r, L0Gen 1 * L0Rep r = L0Rep (L0Act 1 r) * evalWord L1Gen (L0Factor 1 r))
    (hstab : H2 = H1 ⊓ MulAction.stabilizer (Equiv.Perm (Fin 6156)) (1 : Fin 6156)) :
    Steps := by
  intro i r
  fin_cases i
  · exact h0 r
  · exact h1 r
  · have ha : atlasA⁻¹ = atlasA := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using atlasA_sq)
    change atlasA⁻¹ * L0Rep r = L0Rep (L0Act 2 r) * evalWord L1Gen (L0Factor 2 r)
    rw [ha, act2_eq, factor2_eq]
    exact h0 r
  · change L0Gen 3 * L0Rep r = L0Rep (L0Act 3 r) * evalWord L1Gen (L0Factor 3 r)
    apply mul_left_cancel (a := L0Gen 1)
    have hb : L0Gen 1 * L0Gen 3 = 1 := mul_inv_cancel atlasB
    rw [← mul_assoc, hb, one_mul, ← mul_assoc, h1, act13, mul_assoc,
      factor13_cancel hstab, mul_one]

end Sporadic.Janko3.OrderCertificate.Level0
