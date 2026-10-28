module
public import Theory.Representation.BinaryOffender.Homogeneous.Selection.ThreeCopies

/-!
# Additive costs of arbitrarily many invariant isotypic sections

A two-group fixes a simple copy in a semisimple isotypic restriction. Induction
in the literal quotient selects as many copies as the total dimension permits.
The submodule--quotient codimension inequality adds their displacement costs
for the same actor. The type and the actor do not change in the induction.

The Hermitian-square consumer uses four copies and the ranks of the actual
component-action images. Source: Aschbacher--Smith A.1.42 and D.3.7, pp.32,199.
-/

public noncomputable section
open scoped MonoidAlgebra
open Subgroup Representation
namespace Representation.BinaryOffender.Homogeneous
universe u v w
variable {G : Type u} [Group G]
  (N : Subgroup G) [N.Normal]
  {E : Type w} [AddCommGroup E] [Module (ZMod 2)[N] E]
  [Module (ZMod 2) E] [IsScalarTower (ZMod 2) (ZMod 2)[N] E]

theorem section_cost_le_fixedCodim_of_degree
    (P : Subgroup G) (hP : IsPGroup 2 P) (hgen : N ⊔ P = ⊤)
    (c : ℕ) (hE : 0 < Module.finrank (ZMod 2) E)
    (hsection : ∀ (W : Type v) [AddCommGroup W] [Module (ZMod 2) W]
      (σ : Representation (ZMod 2) G W) (X : Subrepresentation σ),
      Nonempty ((X.compActors N.subtype).asSubmodule ≃ₗ[(ZMod 2)[N]] E) →
      c ≤ fixedCodim X.toRepresentation P)
    (k : ℕ) {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (ρ : Representation (ZMod 2) G V)
    [IsSemisimpleModule (ZMod 2)[N] (Representation.asModule (ρ.comp N.subtype))]
    (htype : IsIsotypicOfType (ZMod 2)[N] (Representation.asModule (ρ.comp N.subtype)) E)
    (hd : k * Module.finrank (ZMod 2) E ≤ Module.finrank (ZMod 2) V) :
    k*c ≤ fixedCodim ρ P := by
  induction k generalizing V with
  | zero => simp
  | succ k ih =>
    let : FiniteDimensional (ZMod 2) V := Module.Finite.of_finite
    let : Nontrivial V := Module.finrank_pos_iff.mp (by nlinarith : 0 < Module.finrank (ZMod 2) V)
    obtain ⟨U,_,heU⟩ := exists_simple_section_of_isotypic ρ N htype P hP hgen
    have hdU : Module.finrank (ZMod 2) U.toSubmodule = Module.finrank (ZMod 2) E :=
      (heU.some.restrictScalars (ZMod 2)).finrank_eq
    let : Finite (V ⧸ U.toSubmodule) := Finite.of_surjective _ U.toSubmodule.mkQ_surjective
    let := quotient_restriction_semisimple ρ N U
    have hq := quotient_restriction_isotypic ρ N U htype
    have hdim := U.toSubmodule.finrank_quotient_add_finrank
    have hb := ih U.quotientRepresentation hq (by nlinarith)
    have hu := hsection V ρ U heU
    have hs := fixedCodim_quotient_add_subrepresentation_le ρ U P
    nlinarith
end Representation.BinaryOffender.Homogeneous
