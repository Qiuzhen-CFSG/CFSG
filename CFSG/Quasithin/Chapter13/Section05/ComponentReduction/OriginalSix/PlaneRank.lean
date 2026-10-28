module
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.OriginalSix.PointG2
public import CFSG.Quasithin.Chapter13.Section05.AmbientSource.SourcePlaneBounds
public import CFSG.Quasithin.Chapter13.Section05.PlaneGeometry.TwoBlocks.SourceContainment.Ordinary
/-!
# The original plane-centralizer rank bound

The actual nonabelian seed closure moves the plane under the point core.
The ordinary A₆ plane actor then supplies the original13.3.15 normal
closure, whose cubic quotient leaves three-rank at most one in C_G(V₂).
This is the source bound used against the A₈ point-stabilizer calculation.
Source: Aschbacher–Smith13.5.4(3), printed p.916.
-/
public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section05.ComponentReduction.OriginalSix
open Section08.SourceCompletion AmbientSource PlaneGeometry.TwoBlocks
variable {G : Type*} [Group G] [Finite G] {D : ChapterF.Section09.Setup G}
  {V₂ M : Subgroup G}
  (d : NaturalSetup D.T D.L D.V D.V₁ V₂ D.Vplus M D.Gz)
include d

theorem source_plane_centralizer_rank (h : D.Hypothesis)
    (e : (D.L ⧸ pCore 2 D.L)≃*alternatingGroup (Fin 6))
    (hU : ¬IsMulCommutative D.UH) : primeRank 3 (centralizer (V₂:Set G))≤1 := by
  have hm := source_point_plane_noncentral d D.H
    (h.H_centralizes.trans (Subgroup.centralizer_le_normalizer _)) hU
  have hm' : ⁅D.Gz.pCoreIn 2,V₂⁆≠⊥ := d.first_normalizer.symm ▸ hm
  obtain ⟨hx,hk⟩ := Ordinary.planeActor_action_source d e
  exact (source_plane_core_and_rank d (planeActor (L:=D.L) (V₂:=V₂))
    (planeActor_le.trans inf_le_right) (planeActor_normalized d)
    planeActor_twoPerfect hx hk hm').2

end CFSG.Quasithin.Chapter13.Section05.ComponentReduction.OriginalSix
