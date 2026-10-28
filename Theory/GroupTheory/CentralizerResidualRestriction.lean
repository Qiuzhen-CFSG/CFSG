module

public import Theory.GroupTheory.CentralizerResidualProducts

/-!
# Restricting a full centralizer to a containing subgroup

If H contains C_G(u), the centralizer calculated inside H maps onto the full
centralizer in G. Residual images and faithful core images therefore identify
the literal O₂(O²(C_H(u))) with O₂(O²(C_G(u))). This justifies doing local
square calculations in a proper subgroup without replacing the ambient core.

Source application: Aschbacher–Smith, I.2.2(6b), printed pp.410 and 412,
combined manuscript of 1 March 2004. The result itself is general finite-group
theory and does not assert a model-specific centralizer calculation.
-/

public section
namespace Theory.GroupTheory
open Subgroup
variable {G : Type*} [Group G]

/-- Containment of the full centralizer makes the restricted centralizer exact. -/
theorem map_centralizer_subtype (H : Subgroup G) (u : H)
    (hC : centralizer ({(u : G)} : Set G) ≤ H) :
    (centralizer ({u} : Set H)).map H.subtype = centralizer ({(u : G)} : Set G) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (mem_centralizer_singleton_iff.mp hy))
  · intro hx
    refine ⟨⟨x, hC hx⟩, mem_centralizer_singleton_iff.mpr ?_, rfl⟩
    exact Subtype.ext (mem_centralizer_singleton_iff.mp hx)

/-- The two-residual uses the entire centralizer in both groups. -/
theorem map_centralizerTwoResidual_subtype [Finite G] (H : Subgroup G) (u : H)
    (hC : centralizer ({(u : G)} : Set G) ≤ H) :
    (centralizerTwoResidual u).map H.subtype = centralizerTwoResidual (u : G) := by
  unfold centralizerTwoResidual
  rw [map_embedded_pResidual, map_centralizer_subtype H u hC]

/-- The embedded two-core of the two-residual is unchanged by this restriction. -/
theorem map_centralizerResidualCore_subtype [Finite G] (H : Subgroup G) (u : H)
    (hC : centralizer ({(u : G)} : Set G) ≤ H) :
    (centralizerResidualCore u).map H.subtype = centralizerResidualCore (u : G) := by
  unfold centralizerResidualCore
  rw [map_pCoreIn_of_injective _ _ _ H.subtype_injective,
    map_centralizerTwoResidual_subtype H u hC]

end Theory.GroupTheory
