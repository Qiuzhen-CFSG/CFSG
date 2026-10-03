module

public import Theory.Character.FiniteOrderTrace

/-!
# Character values equal to the degree

A complex character of a finite group takes its degree exactly on the
representation kernel. The forward implication follows because a finite-order
operator whose trace equals its dimension is the identity; the reverse
implication evaluates the trace of the identity.

This is Suzuki, *Group Theory II*, Chapter 6, (1.8)(ii), extracted from
`BenderSuzuki/External/Suzuki/VI/theorem_1_8.lean`. Its historical public name
and irreducibility hypothesis are retained. The proof uses the general
finite-order trace criterion already available in Theory.
-/

namespace BenderSuzuki.External.Suzuki.VI
universe u v

/-- Suzuki, *Group Theory II*, Chapter 6, (1.8)(ii). -/
public theorem suzuki_ch6_theorem_1_8_ii
    {G : Type u} [Group G] [Finite G]
    {V : Type v} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (rho : Representation ℂ G V) [Representation.IsIrreducible rho]
    (x : G) :
    rho.character x = rho.character 1 ↔ x ∈ rho.ker := by
  constructor
  · intro hx
    rw [MonoidHom.mem_ker]
    apply finite_order_end_eq_one_of_trace_eq_finrank (rho x)
    · exact Nat.ne_of_gt (orderOf_pos x)
    · rw [← MonoidHom.map_pow, pow_orderOf_eq_one, MonoidHom.map_one]
    · simpa [Representation.character] using hx
  · intro hx
    rw [MonoidHom.mem_ker] at hx
    simp [Representation.character, hx]


end BenderSuzuki.External.Suzuki.VI
