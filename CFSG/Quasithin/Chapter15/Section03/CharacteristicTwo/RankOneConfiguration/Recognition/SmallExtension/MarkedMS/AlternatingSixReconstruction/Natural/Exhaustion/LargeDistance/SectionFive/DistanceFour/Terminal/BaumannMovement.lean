module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.CentralMovement
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.RadiusDerived

/-!
# Large-path movement in the actual Baumann subgroup

For either moving cover, the central attachment at the first endpoint lies
in the incident edge seed and hence in the midpoint seed. Thus large-path
midpoint movement equals the critical commutator modulo the midpoint seed.

The whole movement also lies in the backward seed kernel: it centralizes
the midpoint core, which contains the opposite seed. On the selected
backward path, the controlling actor therefore fixes this movement modulo
the midpoint seed. The actor and first edge kernel generate the midpoint
stabilizer, making the joined subgroup normal. The actual section action
puts it in the Baumann subgroup. Normal closure and the relative backward
transport give this bound for the original selected span and put its core
movement in the midpoint seed joined with the starting seed.

The whole derived radius inherits the bound through RadiusDerived.
Membership in the Baumann subgroup means residual fixedness modulo the
full seed; residual fixedness itself and the terminal contradiction remain
to be established.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (3.3)(ii), (5.2)(ii), (5.12)(1)--(2), printed pp.867,914--915,924--926.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
open scoped IsMulCommutative commutatorElement Pointwise
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R} (s : FullSymmetricAction h e hz hn d)

include s in
/-- On both covers, the possible central discrepancy is absorbed by the
actual midpoint seed. -/
theorem large_midpoint_movement_sup_seed_eq
    (hc : DistanceTwo.CentralLayer d) (hb : replacementDistance h d = 4)
    {c z : Vertex d.radical}
    (q : CriticalPath d.radical (replacementGeometry h d) c z)
    (hlarge : 4 ≤ (Q d.radical z).relIndex (Z d.radical c)) :
    ⁅Z d.radical c,Q d.radical (q.walk.getVert 2)⁆ ⊔
        Z d.radical (q.walk.getVert 2) =
      ⁅Z d.radical c,Z d.radical z⁆ ⊔ Z d.radical (q.walk.getVert 2) := by
  let a := q.walk.getVert 2
  let t := q.walk.getVert 1
  have hl : q.walk.length = 4 := q.length_eq_b.trans hb
  have ha : color d.radical a = false := (q.vertex_color (by omega)).mpr (by decide)
  have hct : Adjacent d.radical c t := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using q.walk.adj_getVert_succ (i := 0) (by omega)
  have hat : Adjacent d.radical a t := adjacent_symm d.radical
    ((cosetGraph_adj d.radical _ _).mp (q.walk.adj_getVert_succ (i := 1) (by omega)))
  have ht : color d.radical t = true := by
    have hh := adjacent_color_ne d.radical hct
    rw [q.start_color] at hh
    exact Bool.eq_true_of_not_eq_false (Ne.symm hh)
  have hCQ : U d.radical c ≤ Q d.radical c :=
    (DistanceEight.U_le_Z d.radical c).trans
      (((replacementGeometry h d).omega_bound c q.start_color (by
        rw [(replacementGeometry h d).distance_constant _ q.start_color]
        exact replacementDistance_pos h d)).trans (omegaCenter_le _))
  have hattach : U d.radical c ⊓
      centralizer (stabilizer d.radical c : Set (FreeAmalgam d.radical)) ≤ Z d.radical a := by
    apply le_trans _ (adjacent_Z_le d.radical ha hat)
    intro x hx
    rw [Z,if_neg (by simp [ht])]
    change x ∈ omegaCenter (Q d.radical t)
    apply mem_omegaCenter_iff.mpr
    refine ⟨Q_le_adjacent_h d.radical ht hct (hCQ hx.1),?_,?_⟩
    · let := (replacementGeometry h d).Z_elementary (replacementDistance_pos h d) c q.start_color
      exact elemPow_eq_one_of_isElementaryAbelian x (DistanceEight.U_le_Z d.radical c hx.1)
    · intro y hy
      exact hx.2 y (hy.2 _ (adjacent_symm d.radical hct))
  have hcontrol := large_midpoint_movement_le_commutator_sup_center s hc hb q hlarge
  have hmovement := large_midpoint_movement s hc hb q hlarge
  apply le_antisymm
  · exact sup_le (hcontrol.trans (sup_le le_sup_left (hattach.trans le_sup_right))) le_sup_right
  · exact sup_le (hmovement.2.2.2.trans le_sup_left) le_sup_right

include s in
private theorem large_midpoint_movement_le_kernel
    (hc : DistanceTwo.CentralLayer d) (hb : replacementDistance h d = 4)
    {c z : Vertex d.radical}
    (q : CriticalPath d.radical (replacementGeometry h d) c z)
    (hlarge : 4 ≤ (Q d.radical z).relIndex (Z d.radical c)) :
    ⁅Z d.radical c,Q d.radical (q.walk.getVert 2)⁆ ≤
      Z d.radical c ⊓ Q d.radical z := by
  have hl : q.walk.length = 4 := q.length_eq_b.trans hb
  have hmovement := large_midpoint_movement s hc hb q hlarge
  have hHZ := hmovement.1.trans (DistanceEight.U_le_Z d.radical c)
  have hZQ : Z d.radical z ≤ Q d.radical (q.walk.getVert 2) := by
    apply Z_le_Q_of_dist_lt d.radical z ((replacementGeometry h d).exists_critical z q.end_color)
    rw [(replacementGeometry h d).distance_constant _ q.end_color,
      SimpleGraph.dist_comm,q.dist_end,hl]
    exact show 2 < replacementDistance h d by omega
  apply le_inf hHZ
  rw [←C_eq_Q s hc z q.end_color]
  exact le_inf (hHZ.trans (Z_le_stabilizer_of_dist_le c _ q.critical.1.le))
    ((large_midpoint_core_quadratic s hc hb q hlarge).trans (centralizer_le hZQ))

include s in
private theorem controlled_large_selected_core_baumann_control
    (hc : DistanceTwo.CentralLayer d) (hb : replacementDistance h d = 4)
    {c z : Vertex d.radical}
    (q : CriticalPath d.radical (replacementGeometry h d) c z)
    (hlarge : 4 ≤ (Q d.radical z).relIndex (Z d.radical c))
    (W : Subgroup (FreeAmalgam d.radical))
    (hgen : Q d.radical (q.walk.getVert 1) ⊔ W =
      stabilizer d.radical (q.walk.getVert 2))
    (hWne : ¬ W ≤ Q d.radical (q.walk.getVert 2))
    (hWbound : ⁅(Z d.radical c ⊓ Q d.radical z) ⊔
      Z d.radical (q.walk.getVert 2),W⁆ ≤ Z d.radical (q.walk.getVert 2)) :
    ⁅localZSpan d.radical c (q.walk.getVert 2),Q d.radical (q.walk.getVert 2)⁆ ≤
      B d.radical (q.walk.getVert 2) ((replacementGeometry h d).Z_normal _) ∧
    ⁅localZSpan d.radical c (q.walk.getVert 2),Q d.radical (q.walk.getVert 2)⁆ ≤
      ⁅Z d.radical c,Z d.radical z⁆ ⊔ Z d.radical (q.walk.getVert 2) := by
  let a := q.walk.getVert 2
  let t := q.walk.getVert 1
  let H := ⁅Z d.radical c,Q d.radical a⁆
  let J := H ⊔ Z d.radical a
  have hb2 : 2 < replacementDistance h d := by omega
  have hl : q.walk.length = 4 := q.length_eq_b.trans hb
  have ha : color d.radical a = false := (q.vertex_color (by omega)).mpr (by decide)
  have hmovement := large_midpoint_movement s hc hb q hlarge
  have hHV : H ≤ V d.radical a := (hmovement.1.trans (DistanceEight.U_le_Z d.radical c)).trans
    ((Z_le_localZSpan d.radical c a).trans (localZSpan_le_V d.radical (by
      rw [q.dist_start (by omega)])))
  have hJV : J ≤ V d.radical a := sup_le hHV (Z_le_VBall d.radical _ 2)
  have hVG := ((replacementGeometry h d).V_le_Q hb2 a ha).trans
    (show Q d.radical a ≤ stabilizer d.radical a from fun _ hx => hx.1)
  have hWG : W ≤ stabilizer d.radical a := le_sup_right.trans_eq hgen
  have hTG : Q d.radical t ≤ stabilizer d.radical a := le_sup_left.trans_eq hgen
  have hJW : ⁅J,W⁆ ≤ Z d.radical a :=
    (commutator_mono (sup_le_sup_right
      (large_midpoint_movement_le_kernel s hc hb q hlarge) _) le_rfl).trans hWbound
  have hWN : W ≤ normalizer (J : Set (FreeAmalgam d.radical)) :=
    le_normalizer_iff_commutator_le_left.mpr (hJW.trans le_sup_right)
  have hTN : Q d.radical t ≤ normalizer (J : Set (FreeAmalgam d.radical)) :=
    (le_inf hmovement.2.2.1 (hTG.trans (Z_normalized d.radical a))).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hGN : stabilizer d.radical a ≤ normalizer (J : Set (FreeAmalgam d.radical)) := by
    rw [←hgen]
    exact sup_le hTN hWN
  have hJB := normalized_radius_le_slice_of_actor_at s hb2 ha J W hJV hGN hWG hWne hJW
  have hZcG : Z d.radical c ≤ stabilizer d.radical a :=
    ((Z_le_localZSpan d.radical c a).trans (localZSpan_le_V d.radical (by
      rw [q.dist_start (by omega)]))).trans hVG
  have hspan : ⁅localZSpan d.radical c a,Q d.radical a⁆ ≤ J := by
    rw [localZSpan_eq_conjugates]
    apply commutator_iSup_le_of_relative_normal (stabilizer d.radical a)
      (Q d.radical a) J _ hGN
    · intro g
      exact (map_mono hZcG).trans_eq (mem_normalizer_iff_map_conj_eq.mp
        ((stabilizer d.radical a).le_normalizer ((stabilizer d.radical a).inv_mem g.property)))
    · intro g
      have hh := map_mono (f := (MulAut.conj (g : FreeAmalgam d.radical)⁻¹).toMonoidHom)
        (show H ≤ J from le_sup_left)
      have hQ : (Q d.radical a).map (MulAut.conj (g : FreeAmalgam d.radical)⁻¹).toMonoidHom =
          Q d.radical a := mem_normalizer_iff_map_conj_eq.mp
        (Q_normalized d.radical a ((stabilizer d.radical a).inv_mem g.property))
      have hJ : J.map (MulAut.conj (g : FreeAmalgam d.radical)⁻¹).toMonoidHom = J :=
        mem_normalizer_iff_map_conj_eq.mp
          (hGN ((stabilizer d.radical a).inv_mem g.property))
      change (⁅Z d.radical c,Q d.radical a⁆).map _ ≤ J.map _ at hh
      rwa [map_commutator,hQ,hJ] at hh
  refine ⟨hspan.trans hJB,?_⟩
  have heq := large_midpoint_movement_sup_seed_eq s hc hb q hlarge
  exact hspan.trans_eq heq

include e hz hn in
/-- A large critical image puts the entire original selected core movement
in the actual Baumann subgroup and the two specified seeds, for both covers
and every radical image. -/
theorem large_selected_core_baumann_control_knownSimple
    (hb : replacementDistance h d = 4) {z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z)
    (hlarge : 4 ≤ (Q d.radical z).relIndex (Z d.radical (alpha d.radical))) :
    ⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical),Q d.radical (alpha d.radical)⁆ ≤
      B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _) ∧
    ⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical),Q d.radical (alpha d.radical)⁆ ≤
      Z d.radical (p.walk.getVert 2) ⊔ Z d.radical (alpha d.radical) := by
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  obtain ⟨W,hFE,hWZ,hi,hcomm,hWne,hexact,t,c,hat,hct,hgen,hgenQ,
    q,hq1,hq2,hq3,hidx,hstrict,htransport,hmove,hDexact,hWN,hfix,hback⟩ :=
    full_seed_backward_large_knownSimple (e := e) (hz := hz) (hn := hn) hb p hlarge
  obtain ⟨x,hx,hxt,k,hk,hc',g,hg,hagree⟩ := htransport
  have hspan := controlled_backward_span_eq hb p hat x hx k hc' g hg.2 hagree
  have hbound : ⁅(Z d.radical c ⊓ Q d.radical (p.walk.getVert 2)) ⊔
      Z d.radical (alpha d.radical),W⁆ ≤ Z d.radical (alpha d.radical) := by
    rw [hDexact]
    exact ((critical_Z_commutator_le_moving (h := h) p).trans inf_le_left).trans
      (DistanceEight.U_le_Z d.radical _)
  have hh := controlled_large_selected_core_baumann_control s hc hb q hback W
    (by rwa [hq1,hq2]) (by rwa [hq2]) (by rwa [hq2])
  rw [hq2,hspan] at hh
  exact ⟨hh.1,hh.2.trans (sup_le_sup_right
    (((critical_Z_commutator_le_moving (h := h) q).trans inf_le_right).trans
      (DistanceEight.U_le_Z d.radical _)) _)⟩

include e hz hn in
/-- The entire derived radius lies in the Baumann subgroup in the large-image
branch and in the midpoint seed joined with the starting seed. This is
fixedness modulo the seed, with no cover-order premise. -/
theorem large_radius_derived_baumann_control_knownSimple
    (hb : replacementDistance h d = 4) {z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z)
    (hlarge : 4 ≤ (Q d.radical z).relIndex (Z d.radical (alpha d.radical))) :
    ⁅V d.radical (alpha d.radical),V d.radical (alpha d.radical)⁆ ≤
      B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _) ∧
    ⁅V d.radical (alpha d.radical),V d.radical (alpha d.radical)⁆ ≤
      Z d.radical (p.walk.getVert 2) ⊔ Z d.radical (alpha d.radical) := by
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hselected := large_selected_core_baumann_control_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p hlarge
  have hle := large_radius_derived_le_selected_core s hc hb p hlarge
  exact ⟨hle.trans hselected.1,hle.trans hselected.2⟩

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS

