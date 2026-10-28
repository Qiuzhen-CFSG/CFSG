module
public import CFSG.Quasithin.Chapter3.Section01.StandingGuard.Cardinality
public import CFSG.Quasithin.Chapter10.SourceA5DualNumerical
public import CFSG.Quasithin.Chapter10.SourceFullModuleSectionBudget
public import CFSG.Quasithin.Chapter10.SourceA5OriginalTensorBranch

/-!
# Numerical input for the original chosen A₅ module

The multiple-overgroup premise retained by the forward classification gives
an outside maximal local for the original M. The complete B.5.13 source proof
then supplies the cubic bound on the literal full-module action. We apply it
to the minimal quotient's two-section budget and the same-seed tensor branch.
Neither application retains an independent numerical assumption.

The separate local outside-core branch and the seed-equality proof remain
with their source arguments. Source: Aschbacher--Smith 3.1.6--8, 3.2.6,
D.3.7 and D.3.9, printed pp.573--581 and197--201.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Representation.BinaryOffender
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- The standing guard holds for the actual selected maximal local. -/
theorem source_maximalOutside_of_many
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard) :
    Chapter3.HasMaximalOutside T D.maximalLocal :=
  Chapter3.hasMaximalOutside_of_many T hmany D.maximalLocal
    (source_module_nonsolvable_uniqueness D).normalizer_maximal
    (le_normalizer_componentOrbit L T)

/-- B.5.13 supplies the literal full-module bound in the multiple-overgroup branch. -/
theorem source_full_module_cubic_bound_of_many
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard) :
    SourceFullModuleCubicBound D :=
  source_full_module_cubic_bound D (source_maximalOutside_of_many D hmany)

local instance (D : FundamentalSetup KnownSimple.IsKnownSimple T L) :
    IsElementaryAbelian 2 D.fullModule :=
  D.fullModule_elementary (source_module_nonsolvable_uniqueness D)

/-- The actual minimal quotient's two-section obstruction, with its numerical
premise discharged and the original conjugation formula preserved. -/
theorem source_minimal_full_quotient_section_budget_of_many
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L) (hD : D.IsMinimalFullModule)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard) :
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
      HasCubicTwoSectionBudget τ :=
  source_minimal_full_quotient_section_budget D hD
    (source_full_module_cubic_bound_of_many D hmany)

/-- The same-seed source tensor branch needs only the genuine standing premise,
not a separately assumed cubic bound. Seed equality remains an earlier input. -/
theorem source_a5_tensor_model_of_seed_eq_full_of_many
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hminimal : D.IsMinimalFullModule) (hseed : D.seed = D.fullModule)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard) :
    Nonempty (SourceA5TensorModel D e) :=
  source_a5_original_tensor_model_of_seed_eq_full D e hn hminimal hseed
    (source_full_module_cubic_bound_of_many D hmany)

end CFSG.Quasithin.Chapter10
