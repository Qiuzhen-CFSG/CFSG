module
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.KernelComplete
public import CFSG.Quasithin.Chapter5.A5Source.Complete

/-!
# Original 13.2.9 with the source Baumann bound discharged

The completed original A5 argument supplies 5.1.7(1) from the genuine
4.3.2 uniqueness over L. Applying it to the literal outside omega action
identifies its kernel and overlap core with O₂(H), and makes the residual
modulo its own two-core elementary cubic. Solvability remains source13.2.8(1).

Source: Aschbacher–Smith 13.2.9, printed pp.880–881, using 5.1.7(1),
printed pp.633–634, and the earlier 4.3.2 uniqueness over L.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section02.A5Outside
variable {G : Type*} [Group G] [Finite G]

/-- The original omega-action kernel, with the Baumann premise proved. -/
theorem source_omega_centralizer_eq_twoCore_of_source_uniqueness
    {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G}
    (d : Section05.A5Source.Context T L V V₁ V₂ V₃)
    (hu : Chapter4.UniqueMaximalOvergroup L (normalizer (L : Set G)))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : Group.IsSolvable H) :
    centralizer ((omegaOrbit T H).subgroupOf H : Set H) = pCore 2 H :=
  source_omega_centralizer_eq_twoCore d hH
    (Chapter5.A5Source.baumann_normalizer_of_source_uniqueness d hu) hZ hs

/-- The literal overlap core, with the Baumann premise proved. -/
theorem source_overlap_core_eq_twoCore_of_source_uniqueness
    {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G}
    (d : Section05.A5Source.Context T L V V₁ V₂ V₃)
    (hu : Chapter4.UniqueMaximalOvergroup L (normalizer (L : Set G)))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : Group.IsSolvable H) :
    ((normalizer (L : Set G)).subgroupOf H).normalCore = pCore 2 H :=
  source_overlap_core_eq_twoCore d hH
    (Chapter5.A5Source.baumann_normalizer_of_source_uniqueness d hu) hZ hs

/-- The original elementary cubic residual quotient, with 5.1.7 discharged. -/
theorem source_residual_core_quotient_elementary_of_source_uniqueness
    {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G}
    (d : Section05.A5Source.Context T L V V₁ V₂ V₃)
    (hu : Chapter4.UniqueMaximalOvergroup L (normalizer (L : Set G)))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : Group.IsSolvable H) :
    IsElementaryAbelian 3 (pResidual 2 H ⧸ pCore 2 (pResidual 2 H)) :=
  source_residual_core_quotient_elementary d hH
    (Chapter5.A5Source.baumann_normalizer_of_source_uniqueness d hu) hZ hs

end CFSG.Quasithin.Chapter13.Section02.A5Outside
