module
public import CFSG.Quasithin.Chapter10.SourceA5OriginalSeparatedPassage
public import CFSG.Quasithin.Chapter10.SourceA5MovedSeedSeparation
public import CFSG.Quasithin.Chapter10.SourceA5NumericalSelection
public import CFSG.Quasithin.Chapter10.SourceA5MovedNormalizer.Completion

/-!
# Original module control in the proper-seed branch

D.3.5 separates the proper seed using the literal local cubic bound. The
separated full-module argument then gives the original full/local equality
and moved quotient irreducibility. The genuine multiple-overgroup premise
supplies its numerical input through B.5.13. Finally source 10.2.6 controls
the full normalizer of the same original moved module.

The earlier local cubic bound and proper-seed branch remain explicit.
Source: Aschbacher--Smith D.3.5--9 and 10.1--2, printed pp.195--201,741--749.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))

local instance properSeedMovedElementary :
    IsElementaryAbelian 2 (⁅D.fullModule,L⁆ : Subgroup G) :=
  source_original_full_moved_elementary D

/-- The original proper-seed branch discharges support separation, the full
cubic bound, and full/local equality in the moved-action consumer. -/
theorem source_a5_original_proper_seed_control
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hD : D.IsMinimalFullModule)
    (hproper : D.seed ≠ D.moduleSubgroup)
    (hlocal : SourceLocalModuleCubicBound D)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard) :
    D.fullModule = D.moduleSubgroup ∧
      (originalMovedQuotientAction D e).IsIrreducible ∧
      (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G) ∧
      normalizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G) ≤ D.maximalLocal := by
  have hsep := source_a5_moved_seed_separated D e hn ht htn hproper hlocal
  have hbound := source_full_module_cubic_bound_of_many D hmany
  have hfull := source_a5_full_eq_local_of_separated_seed D e hn ht htn hD hbound hsep
  obtain ⟨hi,hcross⟩ := source_a5_original_irreducible_of_minimal_separated_seed
    D e hn ht htn hD hbound hsep
  exact ⟨hfull,hi,hcross,source_a5_moved_normalizer_le D e ht htn hcross⟩

end CFSG.Quasithin.Chapter10
