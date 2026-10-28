module
public import CFSG.Quasithin.Chapter10.SourceA5NumericalComplete
public import CFSG.Quasithin.Chapter10.SourceA5ModuleAlternatives

/-!
# Original A₅ module alternatives with both cubic bounds proved

The multiple-overgroup premise supplies the local and full cubic bounds
for the same fundamental setup. D.3.5 therefore separates a proper seed,
while the same-seed argument produces the tensor model. The original
full/local equality and moved-action alternatives have no numerical input
left to discharge.

Source: Aschbacher--Smith 3.1.8, D.3.5--9 and 10.1--2,
printed pp.576,195--201,741--754.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))

local instance completeAlternativesMovedElementary :
    IsElementaryAbelian 2 (⁅D.fullModule,L⁆ : Subgroup G) :=
  source_original_full_moved_elementary D

/-- The actual proper-seed module controls its moved action with no separate
local or full cubic premise. -/
theorem source_a5_original_proper_seed_control_of_many
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hD : D.IsMinimalFullModule)
    (hproper : D.seed ≠ D.moduleSubgroup)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard) :
    D.fullModule = D.moduleSubgroup ∧
      (originalMovedQuotientAction D e).IsIrreducible ∧
      (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G) ∧
      normalizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G) ≤ D.maximalLocal :=
  source_a5_original_proper_seed_control D e hn ht htn hD hproper
    (source_local_module_cubic_bound_of_many D hmany) hmany

/-- The original seed dichotomy is complete under the actual standing
multiple-overgroup hypothesis. -/
theorem source_a5_original_tensor_or_moved_control_of_many
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hD : D.IsMinimalFullModule)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard) :
    D.fullModule = D.moduleSubgroup ∧
      (Nonempty (SourceA5TensorModel D e) ∨
        (originalMovedQuotientAction D e).IsIrreducible ∧
        (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G) ∧
        normalizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G) ≤ D.maximalLocal) :=
  source_a5_original_tensor_or_moved_control D e hn ht htn hD
    (source_local_module_cubic_bound_of_many D hmany) hmany

end CFSG.Quasithin.Chapter10
