module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Early.Orbit.Source.Complete

/-!
# Neighboring moving layers in the mixed core commutator

The original kernel at alpha fixes the M-vertex two steps farther along
its source path. The first hat at that neighboring vertex is its moving
radius group joined with Z, so displacement by the original core lies in
that moving group. The original second-hat commutator estimate places the
same displacement in Z at alpha.

Conjugating this exact intersection under the stabilizer at alpha bounds
the mixed commutator of the whole second hat with the original core. This
uses the actual path, kernels and conjugation conventions of the source;
no additional module pairing or fixed-factor bound is assumed. Controlling
the resulting intersection span inside U joined with H is still separate.

Source: Meierfrankenfeld--Stellmacher (1993), consequences of (4.5.3)(i)--(ii),
printed pp.897--898, toward the center collection in (4.5)(iii)--(iv).
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Center
open NormalizerTransfer PathCentrality Higher
open scoped Pointwise
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {geometry : Geometry R} {source : LocalSource L R}

private theorem first_hat_local_commutator (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) (p : Early.SourcePath R (alpha R)) :
    ⁅hatV R (p.walk.getVert 6) (p.walk.getVert 8),
      stabilizer R (p.walk.getVert 6)⁆ ≤ Vcirc R (p.walk.getVert 6) := by
  let c := p.walk.getVert 6
  have hc : color R c = false := p.even_color (by decide) (by decide)
  have hloc : Vcirc R c ≤ stabilizer R c :=
    (Vcirc_le_V R c).trans (geometry.V_local c hc (by
      rw [geometry.distance_constant c hc]; exact common.large_distance))
  have hmove : ⁅Vcirc R c,stabilizer R c⁆ ≤ Vcirc R c :=
    le_normalizer_iff_commutator_le_left.mp (Vcirc_normalized c)
  have hZ : ⁅Z R c,stabilizer R c⁆ ≤ Vcirc R c :=
    (Escape.Initial.Z_commutator_stabilizer source c hc).le.trans
      (commutator_mono (Z_le_VBall R c 2) le_rfl)
  have hpre : hatV R c (p.walk.getVert 8) ≤
      commutatorPreimage (stabilizer R c) (stabilizer R c) (Vcirc R c) := by
    rw [(Early.Orbit.Source.HatIdentity.SmallSeed.identitiesOnPath common earlier p).forward
      6 (by decide) (by decide) (by decide)]
    exact sup_le (le_commutatorPreimage hloc hmove)
      (le_commutatorPreimage (Z_le_stabilizer R c) hZ)
  exact (commutator_mono hpre le_rfl).trans
    (commutator_commutatorPreimage_le _ _ _ (Vcirc_normalized c))

/-- The actual neighboring first hat has core displacement in the moving/Z intersection. -/
theorem neighboring_first_core_commutator (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) (p : Early.SourcePath R (alpha R)) :
    ⁅hatV R (p.walk.getVert 6) (p.walk.getVert 8),core R (alpha R)⁆ ≤
      Vcirc R (p.walk.getVert 6) ⊓ Z R (alpha R) := by
  have hdist : (cosetGraph R).dist (alpha R) (p.walk.getVert 6) = 2 := by
    simpa only [p.center_eq] using
      p.distance (geometry := geometry) (i := 4) (j := 6) (by decide) (by decide)
  have hlocal : core R (alpha R) ≤ stabilizer R (p.walk.getVert 6) :=
    (DistanceTwo.core_le_Q _).trans
      (Q_le_stabilizer_of_dist_two R _ _ rfl hdist)
  apply le_inf
  · exact (commutator_mono le_rfl hlocal).trans (first_hat_local_commutator common earlier p)
  · have hseed : hatV R (p.walk.getVert 6) (p.walk.getVert 8) ≤
        hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8) :=
      Escape.Initial.Natural.conjugatesIn_contains _ _
    exact (commutator_mono hseed (DistanceTwo.core_le_Q _)).trans
      (Early.Orbit.Source.Complete.sourceOrbitFacts common earlier p).hatW_commutator

/-- All conjugates of the seed bound control the whole actual second hat. -/
theorem second_core_commutator_le_neighboring_moving_span
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    (p : Early.SourcePath R (alpha R)) :
    ⁅hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8),core R (alpha R)⁆ ≤
      conjugatesIn (Vcirc R (p.walk.getVert 6) ⊓ Z R (alpha R))
        (stabilizer R (alpha R)) := by
  let P := stabilizer R (alpha R)
  let A := hatV R (p.walk.getVert 6) (p.walk.getVert 8)
  let K := core R (alpha R)
  let D := conjugatesIn (Vcirc R (p.walk.getVert 6) ⊓ Z R (alpha R)) P
  have hPD : P ≤ normalizer D := conjugatesIn_normalized _ _
  have hPK : P ≤ normalizer K := DistanceTwo.core_normalized _
  have hAD : ⁅A,K⁆ ≤ D :=
    (neighboring_first_core_commutator common earlier p).trans
      (Escape.Initial.Natural.conjugatesIn_contains _ _)
  have hAP : A ≤ P := by
    have hseed : A ≤ hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8) :=
      Escape.Initial.Natural.conjugatesIn_contains _ _
    let q := Early.Orbit.SourceApplications.higherPath geometry p
    exact hseed.trans ((hatW_le_radius R q.two_step_distances.1.le
      q.two_step_distances.2.1.le).trans
        ((Escape.Propagation.RadiusFour.VBall_le_Q (alpha R) rfl 4
          (by rw [earlier.distance]; decide)).trans (fun _ hx => hx.1)))
  have hAC : A ≤ commutatorPreimage P K D := le_commutatorPreimage hAP hAD
  have hPC : P ≤ normalizer (commutatorPreimage P K D) :=
    commutatorPreimage_normalized P K D P hPD P.le_normalizer hPK hPD
  have hspan : hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8) ≤
      commutatorPreimage P K D := by
    apply iSup_le
    intro g
    exact (map_mono hAC).trans
      (mem_normalizer_iff_map_conj_eq.mp (hPC (P.inv_mem g.property))).le
  exact (commutator_mono hspan le_rfl).trans (commutator_commutatorPreimage_le P K D hPD)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Center
