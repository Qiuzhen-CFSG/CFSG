module

public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SporadicExclusions.JankoFour.Contracts
public import Theory.Mathieu.M24.ComponentLayers

/-!
# The Mathieu layer of the source Sylow overgroup

A seed B in the supplied component L, invariant under the literal N_S(L),
and an actual surjection B → M24 with two-group kernel give a Mathieu layer
in B ∨ S. The component need only be subnormal inside H; S may permute its
conjugates. All kernels and both quotient levels are retained.

This discharges the `hlayer` premise of `Geometry.cover_of_component_seed`
from the seed surjection. The independent component-seed construction supplies
B, its invariance and the surjection; this theorem makes no model-recognition
or splitting assumption.

Source: Aschbacher–Smith, 2.3.9(7), printed p.526; GLS3, Table 5.3i.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.ComponentRefinement.JankoFour
variable {G : Type*} [Group G] {H L M : Subgroup G} {S : Sylow 2 H} {z : G}

/-- The exact Mathieu-layer premise for the source component-seed cover. -/
theorem hasMathieuTwoLayer_of_component_seed (h : LocalSetup H L M S z)
    (B : Subgroup G) (hBL : B ≤ L)
    (hinv : (S : Subgroup H).map H.subtype ⊓ normalizer (L : Set G) ≤
      normalizer (B : Set G))
    (f : B →* Sporadic.Mathieu.M24) (hf : Function.Surjective f)
    (hker : IsPGroup 2 f.ker) :
    Sporadic.Mathieu.HasMathieuTwoLayer
      (B ⊔ (S : Subgroup H).map H.subtype : Subgroup G) := by
  let := h.finite
  exact h.component.relative_local_adjoin_hasMathieuTwoLayer h.component_le hBL
    (map_subtype_le _) (S.isPGroup'.map H.subtype) hinv f hf hker

end CFSG.Quasithin.Chapter2.ComponentRefinement.JankoFour

end
