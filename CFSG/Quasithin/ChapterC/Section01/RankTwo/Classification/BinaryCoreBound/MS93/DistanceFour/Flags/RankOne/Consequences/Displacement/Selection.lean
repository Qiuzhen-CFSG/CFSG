module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Consequences.Displacement.Reduction
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.Paths

/-!
# Selecting a noncentral critical path for MS93 (4.6.9)

Noncentrality of the radius-derived subgroup supplies a vertex c beyond beta
with [Z_c,V_alpha] not contained in the intrinsic center of G_alpha. Since
Q_c centralizes Z_c, V_alpha escapes Q_c. A first critical shift selects d
at distance two from alpha with (d,c) critical. Reversal and the common escape
theorem, applied with alpha as midpoint, give V_c not contained in Q_alpha.
A second critical shift and reversal now produce a critical pair (alpha,a')
with c at distance two from both endpoints.

Thus the selected noncentral generator really is a critical midpoint. The
argument uses only the supplied geometry, common facts and early facts;
FlagControl is retained as an input for the displacement assembly.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), the opening choice in (4.6.9), printed p.908, using the second
(4.6.6), pp.903--904, and the critical escape statement 2.2(v).
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne
variable {M : Type*} [Group M] {L R : Subgroup M}

/-- The opening choice of (4.6.9), retaining criticality, both midpoint
distances, the distinguished edge, and noncentral displacement. -/
theorem exists_noncentralCriticalPath [Finite M] (source : LocalSource L R)
    (geometry : Geometry R) (common : CommonFacts R source geometry)
    (hb : geometry.b R = 4) (early : EarlyFacts R geometry)
    (_control : FlagControl source) : Nonempty (NoncentralCriticalPath R geometry) := by
  obtain ⟨c, hc, hbc, hnc⟩ :=
    exists_noncentral_edge_generator geometry common.large_distance early
  have hcol : color R c = false := by
    have h := adjacent_color_ne R hbc
    have hbeta : color R (beta R) = true := rfl
    cases he : color R c <;> simp_all
  have hac : (cosetGraph R).dist (alpha R) c = 2 := by
    rw [SimpleGraph.dist_comm]
    exact hc.1
  have hescape : ¬ V R (alpha R) ≤ Q R c := by
    intro h
    apply hnc
    exact (commutator_mono le_rfl h).trans
      ((geometry.centralizes c hcol).le.trans bot_le)
  have hforward : (cosetGraph R).dist (alpha R) c + 2 = geometry.b R := by
    rw [hac, hb]
  obtain ⟨d, hdcol, hda, hdcrit⟩ :=
    DistanceEight.PathCentrality.exists_critical_shift R rfl hforward hescape
  have hreverse := common.critical_reverse d hdcol c hcol hdcrit
  have hcescape : ¬ V R c ≤ Q R (alpha R) := by
    apply common.escape c hcol d hreverse (alpha R)
    · rw [SimpleGraph.dist_comm]
      exact hda
    · rw [hc.1, hreverse.1, geometry.distance_constant c hcol]
      exact hb.symm
  have hbackward : (cosetGraph R).dist c (alpha R) + 2 = geometry.b R := by
    rw [hc.1, hb]
  obtain ⟨a', ha', ha'c, hcrit⟩ :=
    DistanceEight.PathCentrality.exists_critical_shift R hcol hbackward hcescape
  refine ⟨⟨a', c, common.critical_reverse a' ha' (alpha R) rfl hcrit, hac, ?_, hbc, hnc⟩⟩
  rw [SimpleGraph.dist_comm]
  exact ha'c

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne
