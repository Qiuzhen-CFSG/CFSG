module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.At.LocalAction

/-!
# Original seed intersections and the normal point edge

Transitivity on the original seed turns abelianness of its point span into
commutation of intersecting conjugates. If the point residual is normal in
an original local I, its commutator with the edge two-core lies in both
subgroups, hence in the point residual's two-core and then in O₂(I).
Thus their literal images in I/O₂(I) commute.

These are the geometric inputs to the selected quadratic endpoint and its
faithful actor in the five-core exclusion. Neither argument requires a
universal structural record. Source: Aschbacher–Smith, 12.8.5, p.850,
F.9.13–17, pp.322–324, and 14.7.5–6, pp.1043–1045, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource
open Chapter12.Section08 CriticalFusion.Source
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- The original abelian point span makes intersecting seed conjugates commute. -/
theorem intersecting_seed_conjugates_commute
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U) :
    ∀ g : G, V ⊓ V.map (MulAut.conj g).toMonoidHom ≠ ⊥ →
      ⁅V,V.map (MulAut.conj g).toMonoidHom⁆ = ⊥ := by
  obtain ⟨z,hz,he⟩ := SetupFlagGeometry.exists_point_generator F (by decide)
  have hh := F.abelian_U_iff_intersections_commute (by decide) z he hz (by
    intro x hx hx1
    obtain ⟨l,hl,hconj⟩ := h.vector_transitive
      (F.le_seed 1 (he ▸ mem_zpowers z)) hx hz hx1
    exact ⟨l,h.chosen.normalizes hl,hconj⟩)
  intro g hg
  have hc := (hh.mp hab) g⁻¹
  simpa only [conjugate,inv_inv] using hc (by simpa only [conjugate,inv_inv] using hg)

omit [Finite G] in
/-- Relative point normality kills the edge-core commutator in the same local quotient. -/
theorem normal_local_edge_core_commuting_images
    (F : InvariantFlag T V 3) {I : Subgroup G}
    (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    [((F.Li L 1).subgroupOf I).Normal] :
    ((F.Ri L 1).subgroupOf I).map (QuotientGroup.mk' (pCore 2 I)) ≤
      centralizer (((F.Li L 1).subgroupOf I).map
        (QuotientGroup.mk' (pCore 2 I)) : Set (I ⧸ pCore 2 I)) := by
  let E := F.Li L 1 ⊔ (T : Subgroup G)
  have hLI := F.Li_one_le_of_mem_Hz hI
  have hEI : E ≤ I := sup_le hLI (F.sylow_le_of_mem_Hz hI)
  have hRI : F.Ri L 1 ≤ I := (pCoreIn_le 2 E).trans hEI
  have hIN : I ≤ normalizer (F.Li L 1 : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hLI).mp inferInstance
  have hER : E ≤ normalizer (F.Ri L 1 : Set G) :=
    E.le_normalizer.trans (normalizer_le_normalizer_characteristic_image E (pCore 2 E))
  have hRL : ⁅F.Ri L 1,F.Li L 1⁆ ≤ F.Li L 1 :=
    le_normalizer_iff_commutator_le_right.mp (hRI.trans hIN)
  have hRR : ⁅F.Ri L 1,F.Li L 1⁆ ≤ F.Ri L 1 :=
    le_normalizer_iff_commutator_le_left.mp ((show F.Li L 1 ≤ E from le_sup_left).trans hER)
  have hc : ⁅F.Ri L 1,F.Li L 1⁆ ≤ (F.Li L 1).pCoreIn 2 :=
    (le_inf hRL hRR).trans (inf_pCoreIn_le_of_le 2 (show F.Li L 1 ≤ E from le_sup_left))
  apply commutator_eq_bot_iff_le_centralizer.mp
  rw [←map_commutator,Subgroup.map_eq_bot_iff,QuotientGroup.ker_mk']
  apply map_le_map_iff_of_injective I.subtype_injective |>.mp
  rw [map_commutator,map_subgroupOf_eq_of_le hRI,map_subgroupOf_eq_of_le hLI]
  exact hc.trans (pCoreIn_mono_of_normalizes hLI hIN)

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource
