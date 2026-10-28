module

public import Theory.AtlasPort.LinearGroups.G2.Basic
public import Theory.AtlasPort.OtherSporadic.Codes.HexacodeAutomorphismPackage
public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
public import Mathlib.LinearAlgebra.SymplecticGroup
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# The component models used by the Borel reduction

These are output predicates for the group alternatives of B.5.5(1)(iv),
B.5.6 and B.5.1. Every branch contains a multiplicative equivalence with
the concrete model. The field exponent is retained. The symplectic and G₂
branches use their derived groups, including their binary endpoints.
The triple cover is the actual even hexacode group.

These definitions assert no classification or automorphism theorem.
In particular, membership must be derived from the genuine offender action,
and exclusion of the two exceptional branches is a separate obligation.
The representation clauses of the appendix results are still needed when
applying those results; these predicates record only their group outputs.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), printed
pp.86, 99, 104–105 and 1144.
-/

@[expose] public section

open Subgroup

namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BorelInner

universe u

/-- The Lie-type alternatives, with actual models and the defining field exponent.
The small derived groups are retained as derived groups. -/
inductive LieComponentModel (D : Type u) [Group D] (e : ℕ) : Prop
  | linear_two (he : 2 ≤ e) (F : Type) [Field F] [Finite F]
      (hF : Nat.card F = 2 ^ e)
      (model : Nonempty (D ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F))
  | linear_three (he : 1 ≤ e) (F : Type) [Field F] [Finite F]
      (hF : Nat.card F = 2 ^ e)
      (model : Nonempty (D ≃* Matrix.SpecialLinearGroup (Fin 3) F))
  | symplectic (he : 1 ≤ e) (F : Type) [Field F] [Finite F]
      (hF : Nat.card F = 2 ^ e)
      (model : Nonempty (D ≃* commutator (Matrix.symplecticGroup (Fin 2) F)))
  | g2 (he : 1 ≤ e) (F : Type) [Field F] [Finite F]
      (hF : Nat.card F = 2 ^ e)
      (model : Nonempty (D ≃* commutator (Atlas.G2.Model F)))
  | binary_linear (he : e = 1) (n : ℕ) (hn : n = 4 ∨ n = 5)
      (model : Nonempty (D ≃* Matrix.ProjectiveSpecialLinearGroup (Fin n) (ZMod 2)))

/-- The complete component group list before the A.3.18 exclusions in (k).
This is an output predicate, not a classification assumption in `SourceSetup`. -/
inductive ComponentModel (D : Type u) [Group D] : Prop
  | lie (e : ℕ) (model : LieComponentModel D e)
  | alternating_seven (model : Nonempty (D ≃* alternatingGroup (Fin 7)))
  | triple_alternating_six (model : Nonempty (D ≃* Atlas.Codes.HexEvenAutomorphisms))

end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BorelInner
