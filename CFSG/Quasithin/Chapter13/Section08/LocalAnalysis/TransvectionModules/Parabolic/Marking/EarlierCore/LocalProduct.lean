module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Parabolic.Marking.EarlierCore.NaturalSetup

/-!
# The actual product I₂ and its two-residual

The two-core of G₁ lies in the standing Sylow subgroup T. Invariance of
L and V₂ makes T normalize L₂ = O²(N_L(V₂)). Thus O₂(G₁)L₂ is a subgroup
and agrees with its join. Since L₂ is two-perfect and O₂(G₁) is a two-group,
this product has two-residual exactly L₂. This is the ordinary part of
the first equality in 13.5.4(6), proved independently of its local assertions.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.5.4 and its proof, printed p.916; use in 13.8.6, printed p.948.
-/

public section

namespace CFSG.Quasithin.Chapter13.Section08.TransvectionParabolic.EarlierCore.NaturalSetup

open Subgroup
open scoped Pointwise

variable {G : Type*} [Group G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G}
  (d : NaturalSetup T L V V₁ V₂ V₃)

include d

/-- The actual two-core of G₁ lies in the given ambient Sylow subgroup. -/
theorem line_core_le_sylow : (normalizer (V₁ : Set G)).pCoreIn 2 ≤ T := by
  have h := pCoreIn_le_sylow (normalizer (V₁ : Set G)) (T.subtype d.line_stable)
  rwa [Sylow.coe_subtype, map_subgroupOf_eq_of_le d.line_stable] at h

/-- T normalizes L₂ by the relative normalizer definition. -/
theorem sylow_normalizes_plane_residual :
    (T : Subgroup G) ≤ normalizer (localResidual L V₂ : Set G) :=
  normalizes_localResidual L T V₂ d.normalizes_L d.plane_stable

/-- O₂(G₁) acts on L₂, even though L₂ need not preserve the point V₁. -/
theorem line_core_normalizes_plane_residual :
    (normalizer (V₁ : Set G)).pCoreIn 2 ≤ normalizer (localResidual L V₂ : Set G) :=
  d.line_core_le_sylow.trans d.sylow_normalizes_plane_residual

/-- The defined I₂ is literally the set product in 13.5.4. -/
theorem localI_product : (localI L V₁ V₂ : Set G) =
    ((normalizer (V₁ : Set G)).pCoreIn 2 : Set G) * (localResidual L V₂ : Set G) :=
  localI_coe_eq_product L V₁ V₂ d.line_core_normalizes_plane_residual

/-- The first equality of 13.5.4(6) follows directly from the source definitions. -/
theorem localI_residual [Finite G] : residual (localI L V₁ V₂) = localResidual L V₂ := by
  unfold localI
  rw [sup_comm]
  exact embedded_pResidual_join_pGroup _ _
    (isPPerfect_embedded_pResidual 2 (L ⊓ normalizer (V₂ : Set G)))
    (isPGroup_pCoreIn 2 _) d.line_core_normalizes_plane_residual

/-- Both factors of I₂ normalize the source plane. -/
theorem localI_le_plane_normalizer : localI L V₁ V₂ ≤ normalizer (V₂ : Set G) :=
  sup_le (d.line_core_le_sylow.trans d.plane_stable)
    ((residual_le _).trans inf_le_right)

end CFSG.Quasithin.Chapter13.Section08.TransvectionParabolic.EarlierCore.NaturalSetup

end
