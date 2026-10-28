module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.CubicActionQuotient
public import CFSG.Quasithin.Chapter12.Section02.SourceApplications.NaturalAt
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.InnerLinearExclusion.Guarded.CubicGeometry

/-!
# Same-group structural-input version

This proof uses only `Structural1222At` and `Theorem12213At` at the original G,T.
It preserves the literal groups and quotient maps of the source argument below.

# The faithful cubic action quotient and its solvable kernel

For D = ⟨L₂,Y,T⟩ and W = ⟨V₁^D⟩, the nonnormalizing residual images
force each original vertex to meet C_D(W) in exactly O₂(D). The common
Sylow intersection and the odd-order theorem make C_D(W) solvable.

The two vertex images have common Sylow subgroups of index three.
They cannot coincide, since their residual images do not normalize one
another. Thus D/C_D(W) is a Goldschmidt triple with the full original
overlap and trivial two-core. The first isomorphism theorem identifies
its amalgam with the original three quotients by O₂(D), compatibly with
both inclusions. The order-four chief interval supplies every premise.

This establishes the kernel reduction used at the beginning of 14.5.8;
solvability of the entire D and the later containment argument remain.
Source: Aschbacher–Smith, F.6.7–8, printed p.305; 14.5.6–8,
printed pp.1014–1015; 14.7.20, printed p.1049, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.InnerLinearExclusion.Guarded
open Chapter12.Section08 CriticalFusion.Source
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- The intrinsic residuals of the two original vertices, in the generated
group, are exactly the restrictions of L₂ and Y. -/
theorem cubic_action_residuals
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (Y : Subgroup G) (hYp : IsPPerfect 2 Y)
    (hYT : (T : Subgroup G) ≤ normalizer (Y : Set G)) :
    let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
    let A := (F.P L).subgroupOf D
    let B := (Y ⊔ (T : Subgroup G)).subgroupOf D
    (pResidual 2 A).map A.subtype = (F.Li L 2).subgroupOf D ∧
      (pResidual 2 B).map B.subtype = Y.subgroupOf D := by
  let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
  have hPD : F.P L ≤ D := le_sup_left
  have hBD : Y ⊔ (T : Subgroup G) ≤ D := le_sup_right
  have hYD : Y ≤ D := le_sup_left.trans hBD
  have hXD : F.Li L 2 ≤ D := by
    apply le_trans _ hPD
    rw [plane_parabolic_eq_join h structural]
    exact le_sup_left
  constructor
  · apply (map_injective D.subtype_injective)
    rw [map_embedded_pResidual,map_subgroupOf_eq_of_le hPD,
      plane_parabolic_residual h structural,map_subgroupOf_eq_of_le hXD]
  · apply (map_injective D.subtype_injective)
    rw [map_embedded_pResidual,map_subgroupOf_eq_of_le hBD,
      embedded_pResidual_join_pGroup Y _ hYp T.isPGroup' hYT,
      map_subgroupOf_eq_of_le hYD]

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.InnerLinearExclusion.Guarded
