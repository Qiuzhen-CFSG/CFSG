module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.ModelSieve.SectionAlternatives
public import Theory.Representation.BinaryOffender.AmbientSectionTransport

/-!
# Preserve the marked component section when changing its ambient actor

The appendix classification acts on J_H*, whereas the original SectionAction
acts on H*. For a component C ≤ J, restriction does not change C-fixed vectors
or the commutator subspace. The identity on the original invariant subspace
therefore identifies its two literal central quotients equivariantly.
Composing this map with the hexacode coordinates retains the same source
section and the compatible group equivalence. In particular no dimension-only
recognition or abstract covering-group comparison is used.

The final lemma assembles a group enumeration and an independently supplied
marked exceptional section. It does not construct either classification input.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.5.3–B.5.6,
printed pp.104–105, K.1.3, printed p.453, and 15.3.49(l), printed p.1144.
-/

@[expose] public section

open Subgroup Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.ModelSieve
variable {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) D V} {C J : Subgroup D}

/-- Carry the marked section from the restricted actor to its original ambient group. -/
noncomputable def HexSection.of_subgroupOf (hCJ : C ≤ J)
    (s : HexSection (ρ.comp J.subtype) (C.subgroupOf J)) : HexSection ρ C := by
  let q := subgroupCentralQuotientEquiv ρ C J hCJ s.space
  have hi : IsIrrPlus ρ C s.space :=
    (IsIrrPlus.subgroupOf_iff ρ C J hCJ s.space).mp s.isIrrPlus
  refine { space := s.space
           stable := hi.choose
           full := hi.choose_spec.1
           irreducible := hi.choose_spec.2
           groupEquiv := (subgroupOfEquivOfLe hCJ).symm.trans s.groupEquiv
           moduleEquiv := q.symm.trans s.moduleEquiv
           equivariant := ?_ }
  intro g v
  obtain ⟨w, rfl⟩ := q.surjective v
  have hq : q (centralQuotientRepresentation (ρ.comp J.subtype) (C.subgroupOf J)
      s.space s.stable ((subgroupOfEquivOfLe hCJ).symm g) w) =
      centralQuotientRepresentation ρ C s.space hi.choose g (q w) := by
    induction w using Submodule.Quotient.induction_on with | _ w => rfl
  change s.moduleEquiv (q.symm (centralQuotientRepresentation ρ C s.space hi.choose g (q w))) =
    Representation.Hexacode.action (s.groupEquiv ((subgroupOfEquivOfLe hCJ).symm g)).val
      (s.moduleEquiv (q.symm (q w)))
  rw [← hq, q.symm_apply_apply, q.symm_apply_apply]
  exact s.equivariant _ _

/-- Passing to the ambient actor leaves the chosen source subspace unchanged. -/
theorem HexSection.of_subgroupOf_space (hCJ : C ≤ J)
    (s : HexSection (ρ.comp J.subtype) (C.subgroupOf J)) :
    (s.of_subgroupOf hCJ).space = s.space := rfl

/-- The component isomorphism is composed with the actual subgroup inclusion. -/
theorem HexSection.of_subgroupOf_groupEquiv (hCJ : C ≤ J)
    (s : HexSection (ρ.comp J.subtype) (C.subgroupOf J)) :
    (s.of_subgroupOf hCJ).groupEquiv =
      (subgroupOfEquivOfLe hCJ).symm.trans s.groupEquiv := rfl

/-- The quotient coordinates are transported through the identity on the
source subspace and its fixed-space quotient. -/
theorem HexSection.of_subgroupOf_moduleEquiv (hCJ : C ≤ J)
    (s : HexSection (ρ.comp J.subtype) (C.subgroupOf J)) :
    (s.of_subgroupOf hCJ).moduleEquiv =
      (subgroupCentralQuotientEquiv ρ C J hCJ s.space).symm.trans s.moduleEquiv := rfl

/-- Transport every component alternative to the original ambient action. -/
theorem ComponentSectionAlternative.of_subgroupOf (hCJ : C ≤ J)
    (h : ComponentSectionAlternative (ρ.comp J.subtype) (C.subgroupOf J)) :
    ComponentSectionAlternative ρ C := by
  let e := (subgroupOfEquivOfLe hCJ).symm
  cases h with
  | lie f model =>
    apply ComponentSectionAlternative.lie f
    cases model with
    | linear_two lo F hF model =>
      exact .linear_two lo F hF (model.map (e.trans ·))
    | linear_three lo F hF model =>
      exact .linear_three lo F hF (model.map (e.trans ·))
    | symplectic lo F hF model =>
      exact .symplectic lo F hF (model.map (e.trans ·))
    | g2 lo F hF model => exact .g2 lo F hF (model.map (e.trans ·))
    | binary_linear he n hn model =>
      exact .binary_linear he n hn (model.map (e.trans ·))
  | alternating_seven model => exact .alternating_seven (model.map (e.trans ·))
  | triple_cover sectionModel => exact .triple_cover (sectionModel.map (·.of_subgroupOf hCJ))

/-- A group enumeration becomes the section-preserving enumeration when the
exceptional branch supplies its actual equivariant section identification. -/
theorem ComponentSectionAlternative.of_componentModel
    (h : BorelInner.ComponentModel C)
    (hhex : Nonempty (C ≃* Atlas.Codes.HexEvenAutomorphisms) → Nonempty (HexSection ρ C)) :
    ComponentSectionAlternative ρ C := by
  cases h with
  | lie f model => exact .lie f model
  | alternating_seven model => exact .alternating_seven model
  | triple_alternating_six model => exact .triple_cover (hhex model)

end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.ModelSieve
