module
public import Theory.Representation.BinaryOffender.Homogeneous.Selection.FaithfulSections
public import Theory.Representation.BinaryOffender.TwoSectionBudget

/-!
# Three invariant isotypic sections and the two-rank degree bound

A two-group fixes a simple copy of a semisimple isotypic binary module.
Repeating this selection in the literal quotients supplies three invariant
sections whenever the ambient degree exceeds twice the simple degree.
If the same elementary actor moves at least its rank on every such section,
their additive fixed-codimension budget contradicts a two-rank upper bound.

This is the faithful-actor multiplicity estimate in Aschbacher--Smith,
D.3.9(1) and D.3.21(3), printed pp.199--200 and 205. Natural-module
applications are in `Theory.Representation.SL2.NaturalDegreeBound`.
-/

public noncomputable section
open scoped MonoidAlgebra
open Subgroup Representation
namespace Representation.BinaryOffender.Homogeneous
universe u v w
variable {G : Type u} [Group G] {V : Type v}
  [AddCommGroup V] [Module (ZMod 2) V] [Finite V] [Nontrivial V]
  (ρ : Representation (ZMod 2) G V) (N : Subgroup G) [N.Normal]
  {E : Type w} [AddCommGroup E] [Module (ZMod 2)[N] E]
  [Module (ZMod 2) E] [IsScalarTower (ZMod 2) (ZMod 2)[N] E]

/-- Three literal invariant sections of the prescribed normal-subgroup type. -/
theorem exists_three_simple_sections_of_degree_gt
    [IsSemisimpleModule (ZMod 2)[N] (Representation.asModule (ρ.comp N.subtype))]
    (htype : IsIsotypicOfType (ZMod 2)[N] (Representation.asModule (ρ.comp N.subtype)) E)
    (P : Subgroup G) (hP : IsPGroup 2 P) (hgen : N ⊔ P = ⊤)
    (hd : 2 * Module.finrank (ZMod 2) E < Module.finrank (ZMod 2) V) :
    ∃ (U : Subrepresentation ρ) (W : Subrepresentation U.quotientRepresentation)
      (X : Subrepresentation W.quotientRepresentation),
      Nonempty ((U.compActors N.subtype).asSubmodule ≃ₗ[(ZMod 2)[N]] E) ∧
      Nonempty ((W.compActors N.subtype).asSubmodule ≃ₗ[(ZMod 2)[N]] E) ∧
      Nonempty ((X.compActors N.subtype).asSubmodule ≃ₗ[(ZMod 2)[N]] E) := by
  let : FiniteDimensional (ZMod 2) V := Module.Finite.of_finite
  obtain ⟨U,_,heU⟩ := exists_simple_section_of_isotypic ρ N htype P hP hgen
  have hdU : Module.finrank (ZMod 2) U.toSubmodule = Module.finrank (ZMod 2) E :=
    (heU.some.restrictScalars (ZMod 2)).finrank_eq
  have hU : U.toSubmodule ≠ ⊤ := by
    intro he
    rw [he,finrank_top] at hdU
    omega
  let : Finite (V ⧸ U.toSubmodule) := Finite.of_surjective _ U.toSubmodule.mkQ_surjective
  let : Nontrivial (V ⧸ U.toSubmodule) := Submodule.Quotient.nontrivial_iff.mpr hU
  let := quotient_restriction_semisimple ρ N U
  have hq := quotient_restriction_isotypic ρ N U htype
  obtain ⟨W,_,heW⟩ := exists_simple_section_of_isotypic U.quotientRepresentation N hq P hP hgen
  have hdW : Module.finrank (ZMod 2) W.toSubmodule = Module.finrank (ZMod 2) E :=
    (heW.some.restrictScalars (ZMod 2)).finrank_eq
  have hdim := U.toSubmodule.finrank_quotient_add_finrank
  have hW : W.toSubmodule ≠ ⊤ := by
    intro he
    rw [he,finrank_top] at hdW
    omega
  let : Finite ((V ⧸ U.toSubmodule) ⧸ W.toSubmodule) :=
    Finite.of_surjective _ W.toSubmodule.mkQ_surjective
  let : Nontrivial ((V ⧸ U.toSubmodule) ⧸ W.toSubmodule) :=
    Submodule.Quotient.nontrivial_iff.mpr hW
  let := quotient_restriction_semisimple U.quotientRepresentation N W
  have hq' := quotient_restriction_isotypic U.quotientRepresentation N W hq
  obtain ⟨X,_,heX⟩ := exists_simple_section_of_isotypic W.quotientRepresentation N hq' P hP hgen
  exact ⟨U,W,X,heU,heW,heX⟩

/-- Three faithful section costs cannot fit the same actor's two-rank budget. -/
theorem degree_le_two_of_section_rank_bound [Finite G]
    [IsSemisimpleModule (ZMod 2)[N] (Representation.asModule (ρ.comp N.subtype))]
    (htype : IsIsotypicOfType (ZMod 2)[N] (Representation.asModule (ρ.comp N.subtype)) E)
    (P : Subgroup G) (hP : IsElementaryTwo P) (hgen : N ⊔ P = ⊤)
    (hb : fixedCodim ρ P ≤ 2 * rank P)
    (hsection : ∀ (W : Type v) [AddCommGroup W] [Module (ZMod 2) W]
      (σ : Representation (ZMod 2) G W) (X : Subrepresentation σ),
      Nonempty ((X.compActors N.subtype).asSubmodule ≃ₗ[(ZMod 2)[N]] E) →
      rank P ≤ fixedCodim X.toRepresentation P) :
    Module.finrank (ZMod 2) V ≤ 2 * Module.finrank (ZMod 2) E := by
  by_contra! hd
  let : IsElementaryAbelian 2 P := hP.2
  let : FiniteDimensional (ZMod 2) V := Module.Finite.of_finite
  obtain ⟨U,W,X,heU,heW,heX⟩ := exists_three_simple_sections_of_degree_gt ρ N htype P
    (IsElementaryAbelian.isPGroup 2 P) hgen hd
  have hu := hsection V ρ U heU
  have hw := hsection _ U.quotientRepresentation W heW
  have hx := hsection _ W.quotientRepresentation X heX
  have hs := fixedCodim_quotient_add_subrepresentation_le ρ U P
  have ht := fixedCodim_quotient_add_subrepresentation_le U.quotientRepresentation W P
  have hx' := fixedCodim_subrepresentation_le W.quotientRepresentation X P
  have hp := hP.rank_pos
  omega
end Representation.BinaryOffender.Homogeneous
