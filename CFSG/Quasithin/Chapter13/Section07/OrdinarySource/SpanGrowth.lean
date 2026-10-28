module
public import CFSG.Quasithin.Chapter13.Section07.OrdinarySource.F9Application
public import CFSG.Quasithin.Chapter13.Section07.SpanGrowth
/-!
# The original full-span quotient is noncentral

The actual parabolic centralizer supplies point/seed normalizer control.
Together with the completed abelian seed closure and plane noncentrality,
this discharges every geometric input of13.7.7. The seed commutator
identifies U_H with [V_H,O₂(H)]; centrality of V_H/U_H would then collapse
the strict seed span to V₃.

Source: Aschbacher–Smith13.7.7, printed p.940.
-/
public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section07.OrdinarySource
open Section08.SourceCompletion
variable {G : Type*} [Group G] [Finite G] {D : ChapterF.Section09.Setup G}
  {V₂ M : Subgroup G}
  (d : NaturalSetup D.T D.L D.V D.V₁ V₂ D.Vplus M D.Gz)
  (e : (D.L ⧸ pCore 2 D.L) ≃* alternatingGroup (Fin 6))
include d e
/-- Source13.7.7 with F.9, seed abelianness, the escaping subgroup and
normalizer control discharged from the original ordinary input. -/
theorem noncentral_full_span_quotient
    (h1221 : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple D.T D.L)
    (hH : D.H ∈ Section08.Source.Hz D.L₁ D.T D.Gz M)
    (hm : ⁅(normalizer (D.V₁:Set G)).pCoreIn 2,V₂⁆≠⊥) :
    ¬ ⁅D.VH,D.H⁆≤D.UH := by
  obtain ⟨h,hU,hne⟩ := inputs_of_plane_noncentral d e h1221 hH hm
  have hc := Section05.AmbientSource.source_parabolic_centralizer d e h1221 hm
  have hb : normalizer (D.V₁:Set G)⊓normalizer (D.Vplus:Set G)≤M := by
    rw [←d.first_normalizer]
    exact (Section05.PointAction.normalizer_intersection_source d hc).trans inf_le_left
  exact source_noncentral_VH_quotient_of_earlier_geometry d h hU hH.2.1 hH.2.2 hb hne
end CFSG.Quasithin.Chapter13.Section07.OrdinarySource
