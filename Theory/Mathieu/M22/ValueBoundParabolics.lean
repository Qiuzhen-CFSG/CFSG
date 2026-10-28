module

public import Theory.PGroupCore
public import Mathlib.GroupTheory.Sylow
public import Mathlib.Data.Fintype.Perm

/-!
# Local pairs for the Mathieu value bound

The two overgroups used for M₂₂ have intrinsic two-core quotients S₅ and
S₃. Their intersections with the simple normal subgroup have the same
quotients in the outer-extension case. The latter information is retained
separately for lifting through an odd central kernel: quotient shapes of
the whole overgroups alone do not describe the restrictions of that kernel.

These are interfaces for actual subgroups and actual quotient isomorphisms,
not assertions that the witnesses exist. The concrete geometry and the
central-cover lifting argument must construct them.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, E.4.3(2),
printed pp. 241–242 (PDF pp. 252–253).
-/

@[expose] public section
namespace Sporadic.Mathieu.M22ValueBound
variable {G : Type*} [Group G]

/-- Two genuine Sylow overgroups generating the ambient group, with the
specified quotients by their own two-cores. No splitting is asserted. -/
structure ParabolicPair (T : Sylow 2 G) where
  first : Subgroup G
  second : Subgroup G
  sylow_le_first : (T : Subgroup G) ≤ first
  sylow_le_second : (T : Subgroup G) ≤ second
  generate : first ⊔ second = ⊤
  firstQuotient : (first ⧸ pCore 2 first) ≃* Equiv.Perm (Fin 5)
  secondQuotient : (second ⧸ pCore 2 second) ≃* Equiv.Perm (Fin 3)

/-- Additional intrinsic quotient identifications in the normal component.
These supply the restriction data for the odd central-cover argument. -/
structure InnerCompatiblePair (T : Sylow 2 G) (L : Subgroup G)
    extends ParabolicPair T where
  firstInnerQuotient :
    ((first ⊓ L : Subgroup G) ⧸ pCore 2 (first ⊓ L : Subgroup G)) ≃*
      Equiv.Perm (Fin 5)
  secondInnerQuotient :
    ((second ⊓ L : Subgroup G) ⧸ pCore 2 (second ⊓ L : Subgroup G)) ≃*
      Equiv.Perm (Fin 3)

end Sporadic.Mathieu.M22ValueBound
