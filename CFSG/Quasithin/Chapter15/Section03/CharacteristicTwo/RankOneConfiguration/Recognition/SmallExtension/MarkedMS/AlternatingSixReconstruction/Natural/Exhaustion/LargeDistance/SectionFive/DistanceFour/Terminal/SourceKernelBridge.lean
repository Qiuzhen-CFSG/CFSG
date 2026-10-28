module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.SmallKernelNormalization
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CubeFullKernel

/-!
# The source moving kernel and the literal full backward kernel

On two consecutive critical paths `c--v` and `a--z`, with `a` the midpoint
of the first and `v` the midpoint of the second, the edge attachment in
`Z_c ∩ Q_v` lies in `Z_a`. Thus its join with `Z_a` agrees with the join
formed using `U_c ∩ Q_v`.

Failure of normalization by `Z_z` forces full omega central generation.
The predecessor-kernel decomposition and that central generation identify
`[Z_c ∩ Q_v, Z_z ∩ Q_a]` with `[U_c ∩ Q_v, X_z ∩ Q_a]`.
The source inequality for `[U_c ∩ Q_v, Z_z]` then normalizes the original
full-kernel join. The critical commutator absorbs the midpoint contribution.
Both moving covers and all edge and endpoint central attachments are retained.

This proves the bridge needed to apply the moving-U/full-X calculation of
Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two* (1993),
(5.12)(1), printed pp.924--925. It does not prove that source inequality.
`SourceKernelFailure` applies the bridge to the literal strict backward
selection, without assuming its full-kernel normalization or central generation.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement Pointwise IsMulCommutative
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R} (s : FullSymmetricAction h e hz hn d)

include s in
/-- The full backward kernel and the moving kernel give the same join with
its midpoint seed. The edge attachment is absorbed by that seed. -/
theorem backward_full_kernel_join_eq_moving
    (hc : DistanceTwo.CentralLayer d) (hb : replacementDistance h d = 4)
    {c v : Vertex d.radical}
    (q : CriticalPath d.radical (replacementGeometry h d) c v) :
    (Z d.radical c ⊓ Q d.radical v) ⊔ Z d.radical (q.walk.getVert 2) =
      (U d.radical c ⊓ Q d.radical v) ⊔ Z d.radical (q.walk.getVert 2) := by
  have hb2 : 2 < replacementDistance h d := by omega
  have hql : q.walk.length = 4 := q.length_eq_b.trans hb
  let qr : CriticalPath d.radical (replacementGeometry h d) v c := {
    start_color := q.end_color
    walk := q.walk.reverse
    shortest := by rw [SimpleGraph.Walk.length_reverse,q.shortest,SimpleGraph.dist_comm]
    critical := critical_reverse_pair s hc q }
  have hdecomp := (critical_kernel_predecessor_moving s hc hb2 qr).1
  have hlast : qr.walk.getVert (qr.walk.length - 1) = q.walk.getVert 1 := by
    change q.walk.reverse.getVert (q.walk.reverse.length - 1) = _
    rw [SimpleGraph.Walk.length_reverse,SimpleGraph.Walk.getVert_reverse,hql]
  rw [hlast] at hdecomp
  have hat : Adjacent d.radical (q.walk.getVert 2) (q.walk.getVert 1) :=
    adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp
      (q.walk.adj_getVert_succ (i := 1) (by omega)))
  have ha : color d.radical (q.walk.getVert 2) = false :=
    (q.vertex_color (by omega)).mpr (by decide)
  rw [hdecomp,sup_assoc,sup_eq_right.mpr (adjacent_Z_le d.radical ha hat)]

include s in
/-- For the actual consecutive critical paths, the full backward failure
line is precisely the moving-U/full-X commutator of MS93 (5.12)(1). -/
theorem small_backward_failure_line_eq_source
    (hc : DistanceTwo.CentralLayer d) (hb : replacementDistance h d = 4)
    {a z c : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (hsmall : (Q d.radical z).relIndex (Z d.radical a) < 4)
    (q : CriticalPath d.radical (replacementGeometry h d) c (p.walk.getVert 2))
    (hq2 : q.walk.getVert 2 = a)
    (hbad : ¬ Z d.radical z ≤ normalizer
      (((Z d.radical c ⊓ Q d.radical (p.walk.getVert 2)) ⊔
        Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _)) :
    ⁅Z d.radical c ⊓ Q d.radical (p.walk.getVert 2),Z d.radical z ⊓ Q d.radical a⁆ =
      ⁅U d.radical c ⊓ Q d.radical (p.walk.getVert 2),X d.radical z ⊓ Q d.radical a⁆ := by
  have hb2 : 2 < replacementDistance h d := by omega
  have hpl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hql : q.walk.length = 4 := q.length_eq_b.trans hb
  have hca : (cosetGraph d.radical).dist c a ≤ 2 := by
    rw [←hq2,q.dist_start (by omega)]
  have hgen := (small_backward_kernel_normalized_or_centrally_generated s hc hb p
    hsmall q.start_color hca).resolve_left hbad
  let qr : CriticalPath d.radical (replacementGeometry h d) (p.walk.getVert 2) c := {
    start_color := q.end_color
    walk := q.walk.reverse
    shortest := by rw [SimpleGraph.Walk.length_reverse,q.shortest,SimpleGraph.dist_comm]
    critical := critical_reverse_pair s hc q }
  have hpre : qr.walk.getVert (qr.walk.length - 2) = a := by
    change q.walk.reverse.getVert (q.walk.reverse.length - 2) = a
    rw [SimpleGraph.Walk.length_reverse,SimpleGraph.Walk.getVert_reverse,hql]
    exact hq2
  have hmove := (critical_kernel_predecessor_moving s hc hb2 qr).2.2
    (Z d.radical z ⊓ Q d.radical a) (by rw [hpre]; exact inf_le_right)
  rw [hmove]
  symm
  apply (critical_X_displacements_of_central_generation s hc p (hgen z p.end_color)
    (U d.radical c ⊓ Q d.radical (p.walk.getVert 2)) ?_).2
  apply inf_le_right.trans
  apply Q_le_stabilizer_of_dist_le_two _ _ q.end_color p.end_color
  rw [p.dist_end,hpl]

include s in
/-- The source moving-kernel inequality suffices for normalization of the
literal full-kernel join. Central generation, when needed, is derived from
failure of that normalization rather than assumed. -/
theorem small_backward_kernel_normalized_of_source_bound
    (hc : DistanceTwo.CentralLayer d) (hb : replacementDistance h d = 4)
    {a z c : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (hsmall : (Q d.radical z).relIndex (Z d.radical a) < 4)
    (q : CriticalPath d.radical (replacementGeometry h d) c (p.walk.getVert 2))
    (hq2 : q.walk.getVert 2 = a)
    (hsource : ⁅U d.radical c ⊓ Q d.radical (p.walk.getVert 2),Z d.radical z⁆ ≤
      ⁅Z d.radical a,Z d.radical z⁆ ⊔
        ⁅U d.radical c ⊓ Q d.radical (p.walk.getVert 2),X d.radical z ⊓ Q d.radical a⁆) :
    Z d.radical z ≤ normalizer
      (((Z d.radical c ⊓ Q d.radical (p.walk.getVert 2)) ⊔
        Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _) := by
  by_contra hbad
  have hb2 : 2 < replacementDistance h d := by omega
  have hpl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hql : q.walk.length = 4 := q.length_eq_b.trans hb
  let K := U d.radical c ⊓ Q d.radical (p.walk.getVert 2)
  let P := K ⊔ Z d.radical a
  have hca : (cosetGraph d.radical).dist c a ≤ 2 := by
    rw [←hq2,q.dist_start (by omega)]
  have hgen := (small_backward_kernel_normalized_or_centrally_generated s hc hb p
    hsmall q.start_color hca).resolve_left hbad
  have hKGz : K ≤ stabilizer d.radical z := by
    apply inf_le_right.trans
    apply Q_le_stabilizer_of_dist_le_two _ _ q.end_color p.end_color
    rw [p.dist_end,hpl]
  have hdisp := critical_X_displacements_of_central_generation s hc p
    (hgen z p.end_color) K hKGz
  change ⁅K,Z d.radical z⁆ ≤ ⁅Z d.radical a,Z d.radical z⁆ ⊔
    ⁅K,X d.radical z ⊓ Q d.radical a⁆ at hsource
  rw [hdisp.2] at hsource
  have hQaGc : Q d.radical a ≤ stabilizer d.radical c :=
    Q_le_stabilizer_of_dist_le_two _ _ p.start_color q.start_color
      (by rwa [SimpleGraph.dist_comm])
  have hQaGv : Q d.radical a ≤ stabilizer d.radical (p.walk.getVert 2) :=
    Q_le_stabilizer_of_dist_le_two _ _ p.start_color q.end_color
      (by rw [p.dist_start (by omega)])
  have hNK : Q d.radical a ≤ normalizer (K : Set (FreeAmalgam d.radical)) :=
    (le_inf (hQaGc.trans (U_normalized c))
      (hQaGv.trans (Q_normalized d.radical _))).trans inf_normalizer_le_normalizer_inf
  have hH : ⁅K,Z d.radical z ⊓ Q d.radical a⁆ ≤ K :=
    le_normalizer_iff_commutator_le_left.mp (inf_le_right.trans hNK)
  have hR : ⁅Z d.radical a,Z d.radical z⁆ ≤ Z d.radical a :=
    ((critical_Z_commutator_le_moving (h := h) p).trans inf_le_left).trans
      (DistanceEight.U_le_Z d.radical a)
  have hKP : ⁅K,Z d.radical z⁆ ≤ P :=
    hsource.trans (sup_le (hR.trans le_sup_right) (hH.trans le_sup_left))
  have hbound : ⁅P,Z d.radical z⁆ ≤ P :=
    commutator_sup_le_of_relative_normal P K (Z d.radical a) (Z d.radical z) P
      P.le_normalizer le_sup_left le_sup_right hKP (hR.trans le_sup_right)
  apply hbad
  have he := backward_full_kernel_join_eq_moving s hc hb q
  rw [hq2] at he
  rw [he]
  exact le_normalizer_iff_commutator_le_left.mpr hbound

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
