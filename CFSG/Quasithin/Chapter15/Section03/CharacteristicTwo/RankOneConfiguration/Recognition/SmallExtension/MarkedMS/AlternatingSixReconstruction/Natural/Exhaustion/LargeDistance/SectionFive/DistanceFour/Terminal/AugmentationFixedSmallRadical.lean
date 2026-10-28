module
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowAdjacent
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.RadiusTransfer
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CubeRadiusPlane

/-!
# Residual fixedness for the smaller radical images

For a large critical path at distance four, the midpoint core acts
quadratically on the moving cover. Its faithful natural image is therefore
elementary abelian. If the edge radical image has order at most four, or
is non-elementary of order eight, the midpoint-core image has order at most
four. The opposite critical seed already has image of order at least four,
so the two images coincide. Their movements on the entire moving cover
coincide as well, including its central attachment.

The actual full-seed backward selector then makes the selected movement
invariant under the midpoint stabilizer. Its order bound gives residual
fixedness, which passes to the moving radius and then the full radius.
Both moving-cover orders and the original Sylow status are retained. The
radical-image branches of elementary order eight and order sixteen are
separate obligations.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (5.12)(2), printed pp.925--926. The internal imports reuse edge
coordinates and whole-seed movement without changing their public boundaries.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender BinaryPermutation
open Theory.SpecificGroups.SymmetricSix Theory.SpecificGroups.SymmetricSix.BinaryFlags
open Theory.GroupTheory Representation.NormalElementaryQuotient
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open scoped IsMulCommutative commutatorElement Pointwise
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R} (s : FullSymmetricAction h e hz hn d)

private theorem small_radical_elementary_card_le_four
    (E P : Subgroup S) [IsElementaryAbelian 2 P]
    (hPE : P ≤ E)
    (hE : Nat.card E ≤ 4 ∨ Nat.card E = 8 ∧ ¬ IsElementaryAbelian 2 E) :
    Nat.card P ≤ 4 := by
  rcases hE with hE | ⟨hE,hne⟩
  · exact (card_le_of_le hPE).trans hE
  have hP : Nat.card P < 8 := by
    have hle := (card_le_of_le hPE).trans_eq hE
    by_contra! hh
    have heq : P = E := eq_of_le_of_card_ge hPE (by omega)
    exact hne (heq ▸ inferInstance)
  have hp : IsPGroup 2 P := IsElementaryAbelian.isPGroup 2 P
  obtain ⟨n,hn⟩ := hp.exists_card_eq
  rw [hn] at hP ⊢
  have hn3 : n < 3 := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp hP
  exact Nat.pow_le_pow_right (by decide : 1 ≤ 2) (show n ≤ 2 by omega)

include s in
private theorem small_radical_cover_movement_eq
    (A P E : Subgroup d.overgroup) (hAP : A ≤ P) (hPE : P ≤ E)
    (hlarge : 4 ≤ Nat.card (A.map s.projection))
    (hquad : ⁅replacementMoved d,P⁆ ≤ centralizer (P : Set d.overgroup))
    (hE : Nat.card (E.map s.projection) ≤ 4 ∨
      Nat.card (E.map s.projection) = 8 ∧
        ¬ IsElementaryAbelian 2 (E.map s.projection)) :
    ⁅replacementMoved d,P⁆ = ⁅replacementMoved d,A⁆ := by
  let := replacementMoved_normal h d
  let : IsElementaryAbelian 2 (P.map s.projection) :=
    elementary_of_faithful_quadratic (naturalRepresentation (Fin 6))
      (naturalRepresentation_injective (Fin 6) (by decide)) _
      (image_quadratic_of_commutator s P hquad)
  have hcard := small_radical_elementary_card_le_four (E.map s.projection)
    (P.map s.projection) (map_mono hPE) hE
  have heq : A.map s.projection = P.map s.projection :=
    eq_of_le_of_card_ge (map_mono hAP) (hcard.trans hlarge)
  have hh : commutatorSpace (replacementMoved d) P = commutatorSpace (replacementMoved d) A := by
    rw [commutatorSpace_eq (replacementMoved d) s.projection s.surjective
      (s.projection_kernel.trans (moved_centralizer s).symm),
      commutatorSpace_eq (replacementMoved d) s.projection s.surjective
      (s.projection_kernel.trans (moved_centralizer s).symm),heq]
  apply le_antisymm ?_ (commutator_mono le_rfl hAP)
  intro x hx
  have hv : Additive.ofMul (⟨x,(commutator_le_left _ _) hx⟩ : replacementMoved d) ∈
      commutatorSpace (replacementMoved d) P := hx
  rw [hh] at hv
  exact hv

include s in
/-- If the radical image has order at most four, or is non-elementary of
order eight, a large critical path identifies the full midpoint-core
movement with the actual critical commutator on either moving cover. -/
theorem small_radical_large_midpoint_movement_eq
    (hc : DistanceTwo.CentralLayer d) (hb : replacementDistance h d = 4)
    (hrad : Nat.card (d.radical.map s.projection) ≤ 4 ∨
      Nat.card (d.radical.map s.projection) = 8 ∧
        ¬ IsElementaryAbelian 2 (d.radical.map s.projection))
    {a z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (hlarge : 4 ≤ (Q d.radical z).relIndex (Z d.radical a)) :
    ⁅Z d.radical a,Q d.radical (p.walk.getVert 2)⁆ = ⁅Z d.radical a,Z d.radical z⁆ := by
  let c := p.walk.getVert 2
  let t := p.walk.getVert 1
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hat : Adjacent d.radical a t := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) (by omega)
  have hct : Adjacent d.radical c t := adjacent_symm d.radical
    ((cosetGraph_adj d.radical _ _).mp (p.walk.adj_getVert_succ (i := 1) (by omega)))
  have ht : color d.radical t = true := by
    have hh := adjacent_color_ne d.radical hat
    rw [p.start_color] at hh
    exact Bool.eq_true_of_not_eq_false (Ne.symm hh)
  have hPc : Q d.radical c ≤ Q d.radical t := Q_le_adjacent_h d.radical ht hct
  have hAz : Z d.radical z ≤ Q d.radical c := by
    apply Z_le_Q_of_dist_lt d.radical z ((replacementGeometry h d).exists_critical z p.end_color)
    rw [(replacementGeometry h d).distance_constant _ p.end_color,SimpleGraph.dist_comm,p.dist_end,hl]
    exact show 2 < replacementDistance h d by omega
  obtain ⟨i,hi,hir,hiR,hiQ,hiU⟩ := SylowAdjacent.edge_coordinates (h := h) hc p.start_color hat
  have hTG : Q d.radical t ≤ stabilizer d.radical a :=
    fun _ hx => hx.2 _ (adjacent_symm d.radical hat)
  let A := (Z d.radical z).comap i
  let P := (Q d.radical c).comap i
  have hmA : A.map i = Z d.radical z :=
    map_comap_eq_self (((hAz.trans hPc).trans hTG).trans_eq hir.symm)
  have hmP : P.map i = Q d.radical c :=
    map_comap_eq_self ((hPc.trans hTG).trans_eq hir.symm)
  have hPR : P ≤ d.radical := by
    have hh := comap_mono (f := i) hPc
    rwa [←hiR,comap_map_eq_self_of_injective hi] at hh
  have hcard : 4 ≤ Nat.card (A.map s.projection) := by
    have hh := reverse_critical_image_four_le s hc (replacementDistance_pos h d) p hlarge
    rw [←hmA,←hiQ,relIndex_map_map_of_injective _ _ hi,
      ←s.projection_kernel,relIndex_ker] at hh
    exact hh
  have hquad : ⁅replacementMoved d,P⁆ ≤ centralizer (P : Set d.overgroup) := by
    intro x hx y hy
    apply hi
    simp only [map_mul]
    have hh := mem_map_of_mem i hx
    rw [map_commutator,hiU,hmP] at hh
    exact large_midpoint_core_quadratic s hc hb p hlarge
      (commutator_mono (DistanceEight.U_le_Z d.radical a) le_rfl hh) (i y) hy
  have hh := congrArg (Subgroup.map i)
    (small_radical_cover_movement_eq s A P d.radical (comap_mono hAz) hPR hcard hquad hrad)
  rw [map_commutator,map_commutator,hiU,hmP,hmA] at hh
  rw [seed_commutator_eq_moving (h := h) (e := e) (hz := hz) p.start_color hat _ hPc,
    seed_commutator_eq_moving (h := h) (e := e) (hz := hz) p.start_color hat _ (hAz.trans hPc)]
  exact hh
include s in
private theorem small_radical_selected_core_control
    (hc : DistanceTwo.CentralLayer d) (hb : replacementDistance h d = 4)
    (hrad : Nat.card (d.radical.map s.projection) ≤ 4 ∨
      Nat.card (d.radical.map s.projection) = 8 ∧
        ¬ IsElementaryAbelian 2 (d.radical.map s.projection)) {c z : Vertex d.radical}
    (q : CriticalPath d.radical (replacementGeometry h d) c z)
    (hlarge : 4 ≤ (Q d.radical z).relIndex (Z d.radical c))
    (W : Subgroup (FreeAmalgam d.radical))
    (hgen : Q d.radical (q.walk.getVert 1) ⊔ W = stabilizer d.radical (q.walk.getVert 2))
    (hfix : ⁅Z d.radical c,Z d.radical z⁆ ≤ centralizer (W : Set (FreeAmalgam d.radical))) :
    let D := ⁅Z d.radical c,Z d.radical z⁆
    ⁅localZSpan d.radical c (q.walk.getVert 2),Q d.radical (q.walk.getVert 2)⁆ = D ∧
      D ≤ fixedCore d.radical (q.walk.getVert 2) ∧
      D ≤ X d.radical (q.walk.getVert 2) ∧ Nat.card D ≤ 8 := by
  let a := q.walk.getVert 2
  let D := ⁅Z d.radical c,Z d.radical z⁆
  have heq := small_radical_large_midpoint_movement_eq s hc hb hrad q hlarge
  have hdata := large_midpoint_movement s hc hb q hlarge
  rw [heq] at hdata
  have hcard := large_midpoint_movement_card s hc hb q hlarge
  rw [heq] at hcard
  have hGN : stabilizer d.radical a ≤ normalizer (D : Set (FreeAmalgam d.radical)) := by
    rw [←hgen]
    exact sup_le hdata.2.2.1 ((le_centralizer_iff.mp hfix).trans (Subgroup.centralizer_le_normalizer _))
  have hl : q.walk.length = 4 := q.length_eq_b.trans hb
  have ha : color d.radical a = false := (q.vertex_color (by omega)).mpr (by decide)
  have hfixed : D ≤ fixedCore d.radical a :=
    small_core_residual_fixed_knownSimple (h := h) (e := e) ha D
      (hdata.2.1.trans (omegaCenter_le _)) ((Ltilde_le_stabilizer _).trans hGN) hcard
  refine ⟨le_antisymm ?_ (heq.symm.le.trans
    (commutator_mono (Z_le_localZSpan d.radical _ _) le_rfl)),hfixed,hdata.2.1,hcard⟩
  have hZcG : Z d.radical c ≤ stabilizer d.radical a := by
    apply Z_le_stabilizer_of_dist_le
    rw [q.dist_start (by omega),(replacementGeometry h d).distance_constant _ q.start_color]
    change 2 ≤ replacementDistance h d
    omega
  rw [localZSpan_eq_conjugates]
  apply commutator_iSup_le_of_relative_normal (stabilizer d.radical a)
    (Q d.radical a) D _ hGN
  · intro g
    exact (map_mono hZcG).trans_eq (mem_normalizer_iff_map_conj_eq.mp
      ((stabilizer d.radical a).le_normalizer ((stabilizer d.radical a).inv_mem g.property)))
  · intro g
    have hh := congrArg (Subgroup.map (MulAut.conj (g : FreeAmalgam d.radical)⁻¹).toMonoidHom) heq
    have hQ : (Q d.radical a).map (MulAut.conj (g : FreeAmalgam d.radical)⁻¹).toMonoidHom =
        Q d.radical a := mem_normalizer_iff_map_conj_eq.mp
      (Q_normalized d.radical a ((stabilizer d.radical a).inv_mem g.property))
    have hD : D.map (MulAut.conj (g : FreeAmalgam d.radical)⁻¹).toMonoidHom = D :=
      mem_normalizer_iff_map_conj_eq.mp (hGN ((stabilizer d.radical a).inv_mem g.property))
    change (⁅Z d.radical c,Q d.radical a⁆ : Subgroup (FreeAmalgam d.radical)).map _ = D.map _ at hh
    rw [map_commutator,hQ,hD] at hh
    exact hh.le

include e hz hn in
/-- For the smaller radical images, the entire selected span has small,
residual-fixed core movement on both covers. The actual backward selector
supplies the same original span. -/
theorem small_radical_large_selected_span_core_fixed_knownSimple
    (hb : replacementDistance h d = 4)
    (hrad : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) ≤ 4 ∨
      Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 8 ∧
        ¬ IsElementaryAbelian 2 (d.radical.map (SourceReduction.projection h e hz hn d)))
    {z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z)
    (hlarge : 4 ≤ (Q d.radical z).relIndex (Z d.radical (alpha d.radical))) :
    let H := ⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical),Q d.radical (alpha d.radical)⁆
    H ≤ fixedCore d.radical (alpha d.radical) ∧
      H ≤ X d.radical (alpha d.radical) ∧ Nat.card H ≤ 8 ∧
      H = ⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical),
        localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)⁆ ∧
      H ≤ Z d.radical (p.walk.getVert 2) := by
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  obtain ⟨W,hFE,hWZ,hi,hcomm,hWne,hexact,t,c,hat,hct,hgen,hgenQ,
    q,hq1,hq2,hq3,hidx,hstrict,htransport,hmove,hDexact,hWN,hfix,hback⟩ :=
    full_seed_backward_large_knownSimple (e := e) (hz := hz) (hn := hn) hb p hlarge
  obtain ⟨x,hx,hxt,k,hk,hc',g,hg,hagree⟩ := htransport
  have hspan := controlled_backward_span_eq hb p hat x hx k hc' g hg.2 hagree
  have hd := small_radical_selected_core_control s hc hb
    (by rwa [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s]) q hback W
    (by rwa [hq1,hq2]) hfix
  rw [hq2,hspan] at hd
  dsimp only
  refine ⟨hd.1.symm ▸ hd.2.1,hd.1.symm ▸ hd.2.2.1,hd.1.symm ▸ hd.2.2.2,?_,?_⟩
  · apply le_antisymm
    · rw [hd.1]
      have hZc : Z d.radical c ≤ localZSpan d.radical (p.walk.getVert 2) (alpha d.radical) := by
        rw [←hspan]
        exact Z_le_localZSpan d.radical _ _
      exact commutator_mono hZc (Z_le_localZSpan d.radical _ _)
    · apply commutator_mono le_rfl
      have hl : p.walk.length = 4 := p.length_eq_b.trans hb
      exact (localZSpan_le_V d.radical (by rw [SimpleGraph.dist_comm,p.dist_start (by omega)])).trans
        ((replacementGeometry h d).V_le_Q (show 2 < replacementDistance h d by omega) (alpha d.radical) rfl)
  · rw [hd.1]
    exact ((critical_Z_commutator_le_moving (h := h) q).trans inf_le_right).trans
      (DistanceEight.U_le_Z d.radical _)
include e hz hn in
/-- The smaller radical-image branches control the entire moving radius,
retaining the complete starting seed and either central cover. -/
theorem small_radical_large_moving_radius_core_fixed_knownSimple
    (hb : replacementDistance h d = 4)
    (hrad : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) ≤ 4 ∨
      Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 8 ∧
        ¬ IsElementaryAbelian 2 (d.radical.map (SourceReduction.projection h e hz hn d)))
    {z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z)
    (hlarge : 4 ≤ (Q d.radical z).relIndex (Z d.radical (alpha d.radical))) :
    ⁅Vcirc d.radical (alpha d.radical),Q d.radical (alpha d.radical)⁆ ≤
      fixedCore d.radical (alpha d.radical) := by
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hm := large_moving_radius_le_selected_span s hc hb p hlarge
  have hf := (small_radical_large_selected_span_core_fixed_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hrad p hlarge).1
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hb2 : 2 < replacementDistance h d := by omega
  have hPG : localZSpan d.radical (p.walk.getVert 2) (alpha d.radical) ≤
      stabilizer d.radical (alpha d.radical) :=
    (localZSpan_le_V d.radical (by rw [SimpleGraph.dist_comm,p.dist_start (by omega)])).trans
      ((replacementGeometry h d).V_local _ rfl hb2)
  apply (commutator_mono hm le_rfl).trans
  exact commutator_sup_le_of_relative_normal (stabilizer d.radical (alpha d.radical)) _ _ _ _
    (fixedCore_normalized d.radical (alpha d.radical)) hPG (Z_le_stabilizer d.radical _) hf
    ((Z_centralizes_Q d.radical (alpha d.radical) rfl).le.trans bot_le)

include e hz hn in
/-- A large critical image forces the entire radius-core commutator to be
residual-fixed whenever the radical image has order at most four or is
non-elementary of order eight. In particular this includes the order-32
moving cover; no restriction on the original Sylow status is imposed. -/
theorem small_radical_large_radius_core_fixed_knownSimple
    (hb : replacementDistance h d = 4)
    (hrad : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) ≤ 4 ∨
      Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 8 ∧
        ¬ IsElementaryAbelian 2 (d.radical.map (SourceReduction.projection h e hz hn d)))
    {z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z)
    (hlarge : 4 ≤ (Q d.radical z).relIndex (Z d.radical (alpha d.radical))) :
    ⁅V d.radical (alpha d.radical),Q d.radical (alpha d.radical)⁆ ≤
      fixedCore d.radical (alpha d.radical) := by
  exact radius_core_fixed_of_moving_core_fixed
    (fullSymmetricAction_knownSimple h e hz hn d (by omega)) (by omega)
    (small_radical_large_moving_radius_core_fixed_knownSimple
      (e := e) (hz := hz) (hn := hn) hb hrad p hlarge)

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
