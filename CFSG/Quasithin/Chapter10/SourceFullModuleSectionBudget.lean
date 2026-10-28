module
public import CFSG.Quasithin.Chapter10.SourceA5OriginalIrreducibility.FaithfulAction
public import Theory.Representation.BinaryOffender.TwoSectionBudget

/-!
# The original full-module actor's two-section budget

The original minimal setup supplies the faithful irreducible action of
M/C_M(V_M) on V_M/C_VM(L₀), together with the genuine cubic ratio bound.
Its actual elementary cubic actor cannot act faithfully on two invariant
sections whose faithful action images are both non-FF. The intermediate
actor may be any subgroup containing this chosen actor, so the local tensor
section need only be invariant under that subgroup, not under all of M.

This is the numerical part of Aschbacher--Smith D.3.9(1), printed pp.199--200.
The existence of the local chief filtration and faithfulness of the chosen
actor on L₀ are separate source inputs; full/local equality is not asserted.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Representation.BinaryOffender
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
local instance sectionBudgetElementary (D : FundamentalSetup KnownSimple.IsKnownSimple T L) :
    IsElementaryAbelian 2 D.fullModule :=
  D.fullModule_elementary (source_module_nonsolvable_uniqueness D)

/-- The same original numerical actor supplies the obstruction to two non-FF
chief sections, while retaining its exact quotient and conjugation coordinates. -/
theorem source_minimal_full_quotient_section_budget
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L) (hD : D.IsMinimalFullModule)
    (hbound : SourceFullModuleCubicBound D) :
    let U := D.fullModule.subgroupOf D.maximalLocal
    let := (source_full_module_reduced D).normal
    let q := QuotientGroup.mk' (centralizer (U : Set D.maximalLocal))
    ∃ τ : Representation (ZMod 2) (D.maximalLocal ⧸ centralizer (U : Set D.maximalLocal))
      (Additive D.fullCentralQuotient),
      Function.Injective τ ∧ τ.IsIrreducible ∧ cubicRatio τ ≤ 2 ∧
      (∀ (m : D.maximalLocal) (v : D.fullModule),
        τ (q m) (Additive.ofMul (QuotientGroup.mk' D.fullCentralizer v)) =
          Additive.ofMul (QuotientGroup.mk' D.fullCentralizer
            ⟨(m : G) * (v : G) * (m : G)⁻¹,
              (mem_normalizer_iff.mp (D.maximalLocal_normalizes_fullModule m.property) v).mp
                v.property⟩)) ∧
      HasCubicTwoSectionBudget τ := by
  dsimp only
  let U := D.fullModule.subgroupOf D.maximalLocal
  let := (source_full_module_reduced D).normal
  let : FiniteDimensional (ZMod 2) (Additive D.fullCentralQuotient) := Module.Finite.of_finite
  have h := source_minimal_full_quotient_faithful_cubic_action D hD hbound
  rcases h with ⟨τ,hfaith,hirr,hc,hτ⟩
  exact ⟨τ,hfaith,hirr,hc,hτ,hasCubicTwoSectionBudget_of_le_two τ hc⟩

end CFSG.Quasithin.Chapter10
