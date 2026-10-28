module

public import CFSG.Quasithin.Chapter6.SourceReduction.LocalSieve.SeedReduction

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearResidualEmbeddingComplete

/-!
# The graph row cannot produce local Cartan escape

The proved graph-action exclusion gives maximality of the actual PSL3(4)
residual. Source uniqueness then places every local overgroup of H in its
normalizer. Apply this to the original Y to eliminate the graph row of
the local sieve, with no module-recognition or centralization premise.

Source: Aschbacher--Smith, 5.1.12 and 5.1.14(1), pp.635,638.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LocalSieve
variable {G : Type*} [Group G] [Finite G]

/-- The proved graph exclusion makes the exceptional linear residual maximal.
Every original local overgroup therefore normalizes that exact residual. -/
theorem overgroup_normalizes_linear_four_residual
    {T : Sylow 2 G} {M H Y : Subgroup G}
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hTM : (T : Subgroup G) ≤ M)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (hY : Y ∈ Chapter1.HOver G (H : Set G)) :
    Y ≤ normalizer (residual H : Set G) := by
  have hn := overgroup_normalizes_seed_orbit
    hG (linear_residual_maximal hG hTM hH hlinear)
    (residual_sup_sylow T H hH.1.1.2) hY
  have he : componentOrbit (residual H) (T : Subgroup G) = residual H :=
    residual_localOrbit_eq hH.1.1.2
  rwa [he] at hn

/-- Source 5.1.12's graph row is excluded under the original escaping premise. -/
theorem not_linear_four_residual_of_escape
    {T : Sylow 2 G} {M H A Y : Subgroup G}
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hTM : (T : Subgroup G) ≤ M)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G)) :
    ¬ ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4 :=
  fun hlinear => hescape (inf_le_right.trans
    (overgroup_normalizes_linear_four_residual hG hTM hH hlinear hY))

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LocalSieve
