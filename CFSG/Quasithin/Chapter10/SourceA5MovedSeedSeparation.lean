module
public import CFSG.Quasithin.Chapter10.SourceA5MovedLocalModels
public import CFSG.Quasithin.Chapter10.SourceA5MovedSeedSupport
public import Theory.Representation.BinaryOffender.CubicRatio.MarkedNormalizer
public import Theory.Representation.AlternatingFiveMovedPair.NaturalEstimate
public import Theory.Representation.AlternatingFiveMovedPair.Mixed.NormalizerEstimate
/-!
# Separated support for the original proper moved seed

The actual central quotient of a proper homogeneous seed has exactly the
natural pair or mixed pair model if both A₅ factors act. Each full linear
normalizer has elementary fixed codimension strictly greater than twice the
actor rank. Faithfulness of the original local actor transfers its cubic
bound to that normalizer, giving a contradiction. Perfectness then lifts
trivial factor action on the quotient to centralization of the original seed.

This completes the proper-seed branch of Aschbacher–Smith D.3.5, printed
pp. 195–196. The original local cubic bound remains its source input; the
original moved-action consumer additionally uses the independent chosen
full/local module identity. No model or multiplicity premise remains.
-/
@[expose] public section
open scoped IsMulCommutative
open Subgroup Theory.GroupTheory Representation
open Representation.BinaryOffender Representation.AlternatingFiveMovedPair
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
  (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
  {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))

local instance separationModuleElementary : IsElementaryAbelian 2 D.moduleSubgroup :=
  D.module_elementary

include e hn ht htn

/-- Both factors cannot act on an original proper seed: its exact local
quotient would be a natural or mixed pair, contradicting the original cubic
bound in that model's full linear normalizer. -/
theorem source_a5_moved_seed_not_both_active
    (hproper : D.seed ≠ D.moduleSubgroup) (hbound : SourceLocalModuleCubicBound D) :
    ¬ ((∃ g, originalA5SeedAction D e hn ht htn (g,1) ≠ 1) ∧
      (∃ g, originalA5SeedAction D e hn ht htn (1,g) ≠ 1)) := by
  rintro ⟨hleft,hright⟩
  let := (source_parabolic_module_reduced D).normal
  let base := SL2FourNatural.alternatingFiveEquiv.symm
  obtain ⟨τ,i,hτ,hcubic,_,hi,_,_,hmodel⟩ :=
    source_a5_moved_local_central_quotient_models D e hn ht htn
      hproper hleft hright base hbound
  let := hi
  rcases hmodel with hnat | hmixed
  · obtain ⟨a⟩ := hnat
    exact not_cubicRatio_le_of_marked_normal_range τ hτ i Natural.action
      (base.prodCongr base).toMonoidHom (base.prodCongr base).surjective a 2
      Natural.normalizer_strict_cubic_bound hcubic
  · obtain ⟨a⟩ := hmixed
    exact not_cubicRatio_le_of_marked_normal_range τ hτ i Mixed.action
      (base.prodCongr base).toMonoidHom (base.prodCongr base).surjective a 2
      Mixed.normalizer_strict_cubic_bound hcubic

/-- The proper-seed branch of D.3.5 has separated support on the two original
components. Every model and orbit premise has been discharged. -/
theorem source_a5_moved_seed_separated
    (hproper : D.seed ≠ D.moduleSubgroup) (hbound : SourceLocalModuleCubicBound D) :
    D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G) :=
  source_a5_seed_separated_of_not_both_active D e hn ht htn
    (source_a5_moved_seed_not_both_active D e hn ht htn hproper hbound)

local instance movedSeedSeparationElementary : IsElementaryAbelian 2 (⁅D.fullModule,L⁆ : Subgroup G) :=
  source_original_full_moved_elementary D

/-- The actual original moved action is irreducible and its moved copy
centralizes L once the independent chosen full/local identity is supplied. -/
theorem source_a5_original_irreducible_of_moved_seed
    (hproper : D.seed ≠ D.moduleSubgroup) (hbound : SourceLocalModuleCubicBound D)
    (hfull : D.fullModule = D.moduleSubgroup) :
    (originalMovedQuotientAction D e).IsIrreducible ∧
      (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G) :=
  source_a5_original_irreducible_of_not_both_seed_factors_active D e hn ht htn hfull
    (source_a5_moved_seed_not_both_active D e hn ht htn hproper hbound)
end CFSG.Quasithin.Chapter10
