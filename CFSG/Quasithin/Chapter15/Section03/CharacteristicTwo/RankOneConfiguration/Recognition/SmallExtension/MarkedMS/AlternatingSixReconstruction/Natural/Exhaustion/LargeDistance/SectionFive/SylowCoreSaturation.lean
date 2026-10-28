module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowTerminalComparison
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.ResidualSmallSection
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowTrappedExclusion

/-!
# Whole-core saturation and terminal seed comparison

A subgroup of an actual component core, of order at most eight and invariant
under the component residual, is fixed by that residual: its automorphism
group has order prime to five, while every nontrivial image of the original
perfect component retains the A6 five-section. A subactor of a small mover
has whole-seed commutator of order at most eight on either moving cover.

On the terminal shift chain this bounds the commutator with the entire
neighboring core. The nonfixed critical line inside it excludes residual
invariance and centralization by the preceding endpoint. Consequently a
seed actor fixed by that endpoint and normalized by the last seed cannot
exhaust the whole-core product. In the unequal-mover branch its image is
strictly smaller than four. Two critical seeds with these properties have
the same image of order two and the same nonzero commutator line.

The original-radical application retains its embedding, generating edge and
all shifted vertices. The pair comparison has explicit containment and
endpoint-fixedness premises; it does not construct the required directional
reverse seeds or establish mover equality. Both covers and their full central
attachments remain. The source (5.10)--(5.11) terminal contradiction, other
image and distance-four branches remain open.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (5.10), printed p.923. The internal imports reuse the small residual
representation argument and neighboring-seed radius inclusion in this family.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement Pointwise
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R}

include h e in
private theorem small_core_residual_fixed_base
    (Y : Subgroup (FreeAmalgam d.radical))
    (hYQ : Y ≤ Q d.radical (alpha d.radical))
    (hYN : Ltilde d.radical (alpha d.radical) ≤ normalizer (Y : Set (FreeAmalgam d.radical)))
    (hsmall : Nat.card Y ≤ 8) :
    Y ≤ fixedCore d.radical (alpha d.radical) := by
  let i := embedM d.radical
  let Y₀ := Y.comap i
  let K := (L.subgroupOf (L ⊔ R)).subgroupOf d.overgroup
  have hYm : Y₀.map i = Y := map_comap_eq_self
    ((hYQ.trans (fun _ hx => hx.1)).trans_eq (stabilizer_m_base d.radical))
  have hKm : K.map i = Ltilde d.radical (alpha d.radical) := by
    rw [Ltilde_alpha,replacement_residual h d]
  have hKN : K ≤ normalizer (Y₀ : Set d.overgroup) := by
    intro k hk
    apply mem_normalizer_iff.mpr
    intro y
    change i y ∈ Y ↔ i (k*y*k⁻¹) ∈ Y
    rw [map_mul,map_mul,map_inv]
    exact mem_normalizer_iff.mp (hYN (hKm ▸ mem_map_of_mem i hk)) _
  have hQ : Y₀ ≤ pCore 2 d.overgroup := by
    apply (map_le_map_iff_of_injective (embedM_injective d.radical)).mp
    rw [hYm,←Q_alpha d.radical (replacement_radical_isPGroup h d) (replacement_core_le_radical h d)]
    exact hYQ
  have hcard : Nat.card Y₀ ≤ 8 := by
    rw [←card_map_of_injective (embedM_injective d.radical),hYm]
    exact hsmall
  have hd : Nat.card Y₀ ∣ 8 := by
    obtain ⟨n,he⟩ := (pCore_isPGroup (p := 2) (G := d.overgroup)).to_le hQ |>.exists_card_eq
    have hn : n ≤ 3 := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp (by
      simpa only [he] using hcard)
    rw [he]
    exact pow_dvd_pow 2 hn
  let f : K →* MulAut Y₀ := Y₀.normalizerMonoidHom.comp
    (K.subtype.codRestrict (normalizer (Y₀ : Set d.overgroup)) (fun k => hKN k.property))
  let j : K ≃* L :=
    (subgroupOfEquivOfLe (show L.subgroupOf (L ⊔ R) ≤ d.overgroup from le_sup_left)).trans
      (subgroupOfEquivOfLe (show L ≤ L ⊔ R from le_sup_left))
  have hf := component_hom_eq_one_of_five_coprime (h := h) (e := e) (f.comp j.symm.toMonoidHom)
    (five_coprime_card_mulAut_of_card_dvd_eight hd)
  have hf' : f = 1 := by
    apply MonoidHom.ext
    intro k
    obtain ⟨l,rfl⟩ := j.symm.surjective k
    exact DFunLike.congr_fun hf l
  have hc : Y₀ ≤ centralizer (K : Set d.overgroup) := by
    intro y hy k hk
    have he := congrArg (fun a : MulAut Y₀ => (a ⟨y,hy⟩ : d.overgroup))
      (DFunLike.congr_fun hf' (⟨k,hk⟩ : K))
    change k*y*k⁻¹ = y at he
    exact mul_inv_eq_iff_eq_mul.mp he
  have hm := congrArg (Subgroup.map i) (commutator_eq_bot_iff_le_centralizer.mpr hc)
  rw [map_commutator,hYm,hKm,Subgroup.map_bot] at hm
  exact le_inf hYQ (commutator_eq_bot_iff_le_centralizer.mp hm)

include h e in
/-- A residual-invariant subgroup of the actual core of order at most eight
is fixed by the residual. The original perfect A6 component supplies the
five-divisibility obstruction to a nontrivial small automorphism action. -/
theorem small_core_residual_fixed_knownSimple
    {a : Vertex d.radical} (ha : color d.radical a = false)
    (Y : Subgroup (FreeAmalgam d.radical)) (hYQ : Y ≤ Q d.radical a)
    (hYN : Ltilde d.radical a ≤ normalizer (Y : Set (FreeAmalgam d.radical)))
    (hsmall : Nat.card Y ≤ 8) : Y ≤ fixedCore d.radical a := by
  obtain ⟨g,rfl⟩ := exists_mVertex_of_color d.radical ha
  let f := (MulAut.conj g⁻¹⁻¹).toMonoidHom
  have he : act d.radical g⁻¹ (mVertex d.radical g) = alpha d.radical := by
    simp only [act_mVertex,mul_inv_cancel]
    rfl
  have hQ : (Y.map f) ≤ Q d.radical (alpha d.radical) := by
    have hh := map_mono (f := f) hYQ
    change Y.map f ≤ (Q d.radical (mVertex d.radical g)).map
      (MulAut.conj g⁻¹⁻¹).toMonoidHom at hh
    rw [←Q_act,he] at hh
    exact hh
  have hN : Ltilde d.radical (alpha d.radical) ≤ normalizer (Y.map f : Set _) := by
    have hh := (map_mono (f := f) hYN).trans (le_normalizer_map f)
    change (Ltilde d.radical (mVertex d.radical g)).map (MulAut.conj g⁻¹⁻¹).toMonoidHom ≤ _ at hh
    rw [←Ltilde_act,he] at hh
    exact hh
  have hh := small_core_residual_fixed_base (h := h) (e := e) (Y.map f) hQ hN
    (by rw [card_map_of_injective (MulAut.conj g⁻¹⁻¹).injective]; exact hsmall)
  apply (map_le_map_iff_of_injective (f := f) (MulAut.conj g⁻¹⁻¹).injective).mp
  change Y.map f ≤ (fixedCore d.radical (mVertex d.radical g)).map
    (MulAut.conj g⁻¹⁻¹).toMonoidHom
  change Y.map f ≤ (Q d.radical (mVertex d.radical g) ⊓
    centralizer (Ltilde d.radical (mVertex d.radical g) : Set (FreeAmalgam d.radical))).map
      (MulAut.conj g⁻¹⁻¹).toMonoidHom
  rw [←map_inf_centralizer_of_injective _ (MulAut.conj g⁻¹⁻¹).injective,←Q_act,←Ltilde_act,he]
  exact hh

include e hz hn in
/-- Every subactor of the maximum small mover has whole-seed commutator
of order at most eight, including the order-thirty-two moving cover. -/
theorem small_mover_seed_commutator_card_knownSimple
    (hb : 4 < replacementDistance h d)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {a t : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t)
    (A : Subgroup (FreeAmalgam d.radical))
    (hA : A ≤ SmallMover.join (U d.radical a) (Q d.radical a) (Q d.radical t) 4) :
    Nat.card (⁅Z d.radical a,A⁆ : Subgroup (FreeAmalgam d.radical)) ≤ 8 := by
  let J := SmallMover.join (U d.radical a) (Q d.radical a) (Q d.radical t) 4
  have hj := SylowAdjacent.sixteen_edge_small_mover_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hcard ha hat
  have ht : color d.radical t = true := by
    have hh := adjacent_color_ne d.radical hat
    cases he : color d.radical t <;> simp_all
  have hZt : Z d.radical t ≤ centralizer (A : Set (FreeAmalgam d.radical)) := by
    intro x hx y hy
    rw [Z,if_neg (by simp [ht])] at hx
    exact (mem_omegaCenter_iff.mp hx).2.2 y (hj.2.1 (hA hy))
  have hZtN : Z d.radical t ≤ normalizer (U d.radical a : Set (FreeAmalgam d.radical)) :=
    ((adjacent_Z_le d.radical ha hat).trans (Z_le_stabilizer d.radical a)).trans (U_normalized a)
  have hcomm : ⁅Z d.radical a,A⁆ = ⁅U d.radical a,A⁆ := by
    rw [DistanceTwo.CentralLayer.Z_eq_moving_sup_edge_at h e hz d ha hat,
      commutator_sup_fixed _ _ A hZtN hZt]
  have hJG : J ≤ stabilizer d.radical a := hj.2.1.trans
    (fun _ hx => hx.2 _ (adjacent_symm d.radical hat))
  have hWU : ⁅U d.radical a,J⁆ ≤ U d.radical a :=
    le_normalizer_iff_commutator_le_left.mp (hJG.trans (U_normalized a))
  let F := U d.radical a ⊓ centralizer (J : Set (FreeAmalgam d.radical))
  have hWF : ⁅Z d.radical a,A⁆ ≤ F := by
    rw [hcomm]
    exact (commutator_mono le_rfl hA).trans
      (le_inf hWU (commutator_eq_bot_iff_le_centralizer.mp hj.2.2.2.2.2))
  have hfix : F.relIndex (U d.radical a) = 4 := by
    obtain ⟨J',_,hJ',_,_,_,_,hfix,_⟩ := SylowSmallMovers.edge_normalizer_small_movers_knownSimple
      (e := e) (hz := hz) (hn := hn) hb ha hat
    rw [SylowLarge.sixteen_edge_relative_normalizer_knownSimple
      (e := e) (hz := hz) (hn := hn) (by omega : 2 < replacementDistance h d) hcard ha hat] at hJ'
    change J = _ at hJ'
    change (U d.radical a ⊓ centralizer (J : Set _)).relIndex (U d.radical a) = 4
    rw [inf_relIndex_left,hJ']
    exact hfix
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hUcard : Nat.card (U d.radical a) ≤ 32 := by
    obtain ⟨i,hi,_,_,hiU⟩ := vertex_coordinates (h := h) hc a ha
    rw [←hiU,card_map_of_injective hi]
    rcases moved_card s with he | he <;> omega
  let := finite_Z d.radical a
  let : Finite (U d.radical a) := Finite.of_injective
    (inclusion (DistanceEight.U_le_Z d.radical a)) (inclusion_injective _)
  let : Finite F := Finite.of_injective (inclusion (show F ≤ U d.radical a from inf_le_left))
    (inclusion_injective _)
  have hprod := relIndex_mul_card_of_le (show F ≤ U d.radical a from inf_le_left)
  rw [hfix] at hprod
  exact (card_le_of_le hWF).trans (by omega)

include e hz hn in
/-- The entire neighboring-core commutator has order at most eight but
cannot be invariant under the intermediate residual. Its contained terminal
critical line escapes that residual's fixed core. -/
theorem orbit_terminal_core_commutator_not_normalized_knownSimple
    (hb : 4 < replacementDistance h d)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (q : BackwardShift (h := h) p) (r : BackwardShift (h := h) q.path)
    (t : BackwardShift (h := h) r.path)
    (hr : SylowTerminalPath.OrbitPrefix (h := h) r.path (replacementDistance h d)) :
    let W := ⁅Z d.radical t.start,Q d.radical r.start⁆
    W ≤ Q d.radical r.start ∧ Nat.card W ≤ 8 ∧
      (¬ Ltilde d.radical r.start ≤ normalizer (W : Set (FreeAmalgam d.radical))) ∧
      ¬ W ≤ centralizer (Z d.radical (q.path.walk.getVert (q.path.walk.length-2)) :
        Set (FreeAmalgam d.radical)) := by
  let W := ⁅Z d.radical t.start,Q d.radical r.start⁆
  let z := r.path.walk.getVert (r.path.walk.length-2)
  have hcore := orbit_terminal_core_containment_knownSimple hb hcard p q r t hr
  have hsmall := small_mover_seed_commutator_card_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hcard t.path.start_color t.adjacent_shift
    (Q d.radical r.start) hcore
  have hZQ : Z d.radical t.start ≤ Q d.radical r.start :=
    (neighbor_seed_le_radius t.adjacent_start t.adjacent_shift).trans
      ((replacementGeometry h d).V_le_Q (by omega : 2 < replacementDistance h d)
        r.start r.path.start_color)
  have hWQ : W ≤ Q d.radical r.start :=
    (Subgroup.commutator_le_sup _ _).trans (sup_le hZQ le_rfl)
  have hzQ : Z d.radical z ≤ Q d.radical r.start := by
    apply Z_le_Q_of_dist_lt d.radical z ((replacementGeometry h d).exists_critical z t.path.end_color)
    rw [(replacementGeometry h d).distance_constant z t.path.end_color,SimpleGraph.dist_comm]
    change (cosetGraph d.radical).dist r.start (r.path.walk.getVert (r.path.walk.length-2)) < _
    rw [r.path.dist_start (Nat.sub_le _ _)]
    have hl : r.path.walk.length = replacementDistance h d := r.path.length_eq_b
    change r.path.walk.length-2 < replacementDistance h d
    omega
  have hnot : ¬ Ltilde d.radical r.start ≤ normalizer (W : Set (FreeAmalgam d.radical)) := by
    intro hnorm
    have hfixed := small_core_residual_fixed_knownSimple (h := h) (e := e)
      r.path.start_color W hWQ hnorm hsmall
    exact orbit_terminal_line_not_le_fixedCore_knownSimple hb hcard p q r t hr
      ((commutator_mono le_rfl hzQ).trans hfixed)
  refine ⟨hWQ,hsmall,hnot,?_⟩
  intro hcentral
  apply hnot
  apply (Ltilde_le_stabilizer r.start).trans
  rw [←t.generation]
  apply sup_le _ ((le_centralizer_iff.mp hcentral).trans (Subgroup.centralizer_le_normalizer _))
  intro x hx
  apply mem_normalizer_iff_map_conj_eq.mpr
  change W.map (MulAut.conj x).toMonoidHom = W
  dsimp only [W]
  have hzmap : (Z d.radical t.start).map (MulAut.conj x).toMonoidHom = Z d.radical t.start :=
    mem_normalizer_iff_map_conj_eq.mp (Z_normalized d.radical t.start
      (hx.2 _ (adjacent_symm d.radical t.adjacent_shift)))
  have hqmap : (Q d.radical r.start).map (MulAut.conj x).toMonoidHom = Q d.radical r.start :=
    mem_normalizer_iff_map_conj_eq.mp (Q_normalized d.radical r.start
      (hx.2 _ (adjacent_symm d.radical t.adjacent_start)))
  rw [map_commutator,hzmap,hqmap]

include e hz hn in
/-- A seed actor fixed by the preceding endpoint and normalized by the
last seed cannot exhaust the neighboring whole-core product. This is the
saturation obstruction used for the two reverse seeds in MS93 (5.10). -/
theorem orbit_terminal_seed_actor_not_saturating_knownSimple
    (hb : 4 < replacementDistance h d)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (q : BackwardShift (h := h) p) (r : BackwardShift (h := h) q.path)
    (t : BackwardShift (h := h) r.path)
    (hr : SylowTerminalPath.OrbitPrefix (h := h) r.path (replacementDistance h d))
    (Y : Subgroup (FreeAmalgam d.radical)) (hY : Y ≤ Q d.radical r.start)
    (hYN : Z d.radical t.start ≤ normalizer (Y : Set (FreeAmalgam d.radical)))
    (hYC : Y ≤ centralizer (Z d.radical (q.path.walk.getVert (q.path.walk.length-2)) :
      Set (FreeAmalgam d.radical))) :
    Q d.radical t.start ⊔ Y ≠ Q d.radical t.start ⊔ Q d.radical r.start := by
  intro hsaturate
  have hnot := (orbit_terminal_core_commutator_not_normalized_knownSimple hb hcard p q r t hr).2.2.2
  apply hnot
  have hQY : Y ≤ normalizer (Z d.radical t.start : Set (FreeAmalgam d.radical)) := by
    have htcol : color d.radical t.edge = true := by
      have hh := adjacent_color_ne d.radical t.adjacent_start
      rw [r.path.start_color] at hh
      cases he : color d.radical t.edge <;> simp_all
    exact ((hY.trans (Q_le_adjacent_h d.radical htcol t.adjacent_start)).trans
      (fun _ hx => hx.2 _ (adjacent_symm d.radical t.adjacent_shift))).trans
        (Z_normalized d.radical t.start)
  let C := ⁅Z d.radical t.start,Y⁆
  have hCZ : C ≤ Z d.radical t.start := le_normalizer_iff_commutator_le_left.mp hQY
  have hnorm : Q d.radical t.start ⊔ Y ≤ normalizer (C : Set (FreeAmalgam d.radical)) := by
    apply sup_le _ (normalizer_commutator_ge_right _ _)
    exact ((le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q d.radical t.start t.path.start_color))).trans
        (centralizer_le hCZ)).trans (Subgroup.centralizer_le_normalizer _)
  have hbound := commutator_sup_le_of_relative_normal (Q d.radical t.start ⊔ Y)
    (Q d.radical t.start) Y (Z d.radical t.start) C hnorm le_sup_left le_sup_right
    (by rw [commutator_comm,Z_centralizes_Q d.radical t.start t.path.start_color]; exact bot_le)
    (by rw [commutator_comm])
  rw [hsaturate] at hbound
  have hCY : C ≤ Y := le_normalizer_iff_commutator_le_right.mp hYN
  rw [commutator_comm] at hbound
  exact ((commutator_mono le_rfl le_sup_right).trans hbound).trans (hCY.trans hYC)

include e hz hn in
/-- In the unequal-mover branch, an endpoint-fixed seed actor normalized
by the last seed has index strictly below four modulo the last whole core.
The proof uses the strict failure of whole-core saturation. -/
theorem four_shift_terminal_actor_index_lt_four_knownSimple
    (hb : 4 < replacementDistance h d)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (q : BackwardShift (h := h) p) (r : BackwardShift (h := h) q.path)
    (t : BackwardShift (h := h) r.path) (v : BackwardShift (h := h) t.path)
    (hr : SylowTerminalPath.OrbitPrefix (h := h) r.path (replacementDistance h d))
    (hv : act d.radical v.transporter (t.path.walk.getVert 1) = v.edge)
    (hne : SmallMover.join (U d.radical v.start) (Q d.radical v.start) (Q d.radical v.edge) 4 ≠
      SmallMover.join (U d.radical t.start) (Q d.radical t.start) (Q d.radical v.edge) 4)
    (Y : Subgroup (FreeAmalgam d.radical)) (hY : Y ≤ Q d.radical t.start)
    (hYN : Z d.radical v.start ≤ normalizer (Y : Set (FreeAmalgam d.radical)))
    (hYC : Y ≤ centralizer (Z d.radical (r.path.walk.getVert (r.path.walk.length-2)) :
      Set (FreeAmalgam d.radical))) :
    (Q d.radical v.start).relIndex (Q d.radical v.start ⊔ Y) < 4 ∧
      (Q d.radical v.start).relIndex Y < 4 := by
  have ht : SylowTerminalPath.OrbitPrefix (h := h) t.path (replacementDistance h d) := by
    intro i hi hl
    exact SylowTerminalPath.orbitPrefix_backwardShift hb r.path t hr i (Nat.lt_succ_of_lt hi) hl
  have hproper := orbit_terminal_seed_actor_not_saturating_knownSimple
    hb hcard q.path r t v ht Y hY hYN hYC
  let H := Q d.radical v.start ⊔ Y
  let B := Q d.radical v.start ⊔ Q d.radical t.start
  have hHB : H ≤ B := sup_le_sup_left hY _
  have hbounds := four_shift_unequal_core_indices_knownSimple hb hcard p q r t v hr hv hne
  have hbound : (Q d.radical v.start).relIndex B ≤ 4 := by
    change (Q d.radical v.start).relIndex (Q d.radical v.start ⊔ Q d.radical t.start) ≤ 4
    rw [sup_comm (Q d.radical v.start) (Q d.radical t.start)]
    exact hbounds.2
  have hBedge : B ≤ Q d.radical v.edge := by
    have hc := (four_shift_core_product_knownSimple hb hcard p q r t v hr hv).2.2
    have hj := SylowAdjacent.sixteen_edge_small_mover_knownSimple
      (e := e) (hz := hz) (hn := hn) hb hcard t.path.start_color v.adjacent_start
    exact (sup_comm _ _).le.trans (hc.trans (inf_le_left.trans hj.2.1))
  let := finite_stabilizer d.radical t.start
  let : Finite B := Finite.of_injective
    (inclusion (hBedge.trans (fun _ hx => hx.2 _ (adjacent_symm d.radical v.adjacent_start))))
    (inclusion_injective _)
  let : Finite H := Finite.of_injective (inclusion hHB) (inclusion_injective _)
  have hnotone : H.relIndex B ≠ 1 := by
    intro hone
    exact hproper (le_antisymm hHB (relIndex_eq_one.mp hone))
  have hpos : 0 < H.relIndex B := Nat.pos_of_ne_zero index_ne_zero_of_finite
  have hpos' : 0 < (Q d.radical v.start).relIndex H := Nat.pos_of_ne_zero index_ne_zero_of_finite
  have hmul := relIndex_mul_relIndex (Q d.radical v.start) H B le_sup_left hHB
  have hge := Nat.mul_le_mul_left ((Q d.radical v.start).relIndex H)
    (show 2 ≤ H.relIndex B by omega)
  have hlt : (Q d.radical v.start).relIndex H < 4 := by nlinarith
  exact ⟨hlt,lt_of_le_of_lt (relIndex_le_of_le_right
    (show Y ≤ H from le_sup_right) index_ne_zero_of_finite) hlt⟩

private theorem core_join_commutator_le {F : Type*} [Group F]
    (C V A B : Subgroup F) (hCV : C ≤ centralizer (V : Set F))
    (hAV : A ≤ normalizer (V : Set F)) (hB : B ≤ C ⊔ A) :
    ⁅V,B⁆ ≤ ⁅V,A⁆ := by
  have hDV : ⁅V,A⁆ ≤ V := le_normalizer_iff_commutator_le_left.mp hAV
  have hN : C ⊔ A ≤ normalizer ((⁅V,A⁆ : Subgroup F) : Set F) :=
    sup_le ((hCV.trans (centralizer_le hDV)).trans (Subgroup.centralizer_le_normalizer _))
      (normalizer_commutator_ge_right _ _)
  have hh := commutator_sup_le_of_relative_normal (C ⊔ A) C A V ⁅V,A⁆ hN
    le_sup_left le_sup_right
    (by rw [commutator_eq_bot_iff_le_centralizer.mpr hCV]; exact bot_le)
    (by rw [commutator_comm])
  rw [commutator_comm] at hh
  exact (commutator_mono le_rfl hB).trans hh

include e hz hn in
/-- Two actual critical seeds in the preceding whole core have the same
nonzero commutator line when their join is fixed by the preceding endpoint.
The unequal-mover core bound is sharpened before comparing either line. -/
theorem four_shift_terminal_seed_pair_knownSimple
    (hb : 4 < replacementDistance h d)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (q : BackwardShift (h := h) p) (r : BackwardShift (h := h) q.path)
    (t : BackwardShift (h := h) r.path) (v : BackwardShift (h := h) t.path)
    (hr : SylowTerminalPath.OrbitPrefix (h := h) r.path (replacementDistance h d))
    (hv : act d.radical v.transporter (t.path.walk.getVert 1) = v.edge)
    (hne : SmallMover.join (U d.radical v.start) (Q d.radical v.start) (Q d.radical v.edge) 4 ≠
      SmallMover.join (U d.radical t.start) (Q d.radical t.start) (Q d.radical v.edge) 4)
    {c₁ c₂ : Vertex d.radical}
    (p₁ : CriticalPath d.radical (replacementGeometry h d) c₁ v.start)
    (p₂ : CriticalPath d.radical (replacementGeometry h d) c₂ v.start)
    (h₁Q : Z d.radical c₁ ≤ Q d.radical t.start)
    (h₂Q : Z d.radical c₂ ≤ Q d.radical t.start)
    (h₁C : Z d.radical c₁ ≤ centralizer
      (Z d.radical (r.path.walk.getVert (r.path.walk.length-2)) : Set (FreeAmalgam d.radical)))
    (h₂C : Z d.radical c₂ ≤ centralizer
      (Z d.radical (r.path.walk.getVert (r.path.walk.length-2)) : Set (FreeAmalgam d.radical))) :
    (Q d.radical v.start).relIndex
      (Q d.radical v.start ⊔ (Z d.radical c₁ ⊔ Z d.radical c₂)) = 2 ∧
      Nat.card (⁅Z d.radical c₁,Z d.radical v.start⁆ : Subgroup (FreeAmalgam d.radical)) = 2 ∧
      ⁅Z d.radical c₁,Z d.radical v.start⁆ = ⁅Z d.radical c₂,Z d.radical v.start⁆ := by
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  let C := Q d.radical v.start
  let Y := Z d.radical c₁ ⊔ Z d.radical c₂
  let H := C ⊔ Y
  let A := C ⊔ Z d.radical c₁
  have hcrit {c : Vertex d.radical}
      (cp : CriticalPath d.radical (replacementGeometry h d) c v.start) :
      Z d.radical v.start ≤ stabilizer d.radical c :=
    critical_Z_le_stabilizer d.radical (replacementGeometry h d) c cp.start_color
      (by rw [(replacementGeometry h d).distance_constant c cp.start_color]
          exact replacementDistance_pos h d) cp.critical
  have hreverse {c : Vertex d.radical}
      (cp : CriticalPath d.radical (replacementGeometry h d) c v.start) :
      Z d.radical c ≤ stabilizer d.radical v.start :=
    critical_Z_le_stabilizer d.radical (replacementGeometry h d) v.start cp.end_color
      (by rw [(replacementGeometry h d).distance_constant v.start cp.end_color]
          exact replacementDistance_pos h d) (critical_reverse_pair s hc cp)
  have hYN : Z d.radical v.start ≤ normalizer (Y : Set (FreeAmalgam d.radical)) :=
    (le_inf ((hcrit p₁).trans (Z_normalized d.radical c₁))
      ((hcrit p₂).trans (Z_normalized d.radical c₂))).trans
        (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hbound := four_shift_terminal_actor_index_lt_four_knownSimple
    hb hcard p q r t v hr hv hne Y (sup_le h₁Q h₂Q) hYN (sup_le h₁C h₂C)
  have hHG : H ≤ stabilizer d.radical v.start :=
    sup_le (fun _ hx => hx.1) (sup_le (hreverse p₁) (hreverse p₂))
  let := finite_stabilizer d.radical v.start
  let : Finite H := Finite.of_injective (inclusion hHG) (inclusion_injective _)
  have hAH : A ≤ H := sup_le_sup_left le_sup_left C
  let : Finite A := Finite.of_injective (inclusion hAH) (inclusion_injective _)
  have hsmall₁ : C.relIndex (Z d.radical c₁) < 4 :=
    lt_of_le_of_lt (relIndex_le_of_le_right
      (show Z d.radical c₁ ≤ H from le_sup_left.trans le_sup_right) index_ne_zero_of_finite) hbound.1
  have hsmall₂ : C.relIndex (Z d.radical c₂) < 4 :=
    lt_of_le_of_lt (relIndex_le_of_le_right
      (show Z d.radical c₂ ≤ H from le_sup_right.trans le_sup_right) index_ne_zero_of_finite) hbound.1
  have hZC : Z d.radical c₁ ≤ normalizer (C : Set (FreeAmalgam d.radical)) :=
    (hreverse p₁).trans (Q_normalized d.radical v.start)
  have hCA : C.relIndex A = 2 := by
    let : (C.subgroupOf A).Normal := normal_subgroupOf_of_le_normalizer (sup_le C.le_normalizer hZC)
    have hi := relIndex_sup_left ((Z d.radical c₁).subgroupOf A) (C.subgroupOf A)
    rw [←subgroupOf_sup (show C ≤ A from le_sup_left) (show Z d.radical c₁ ≤ A from le_sup_right),
      relIndex_subgroupOf le_rfl,relIndex_subgroupOf (show Z d.radical c₁ ≤ A from le_sup_right)] at hi
    exact hi.trans (small_critical_indices s hc p₁ hsmall₁).1
  have hmul := relIndex_mul_relIndex C A H le_sup_left hAH
  rw [hCA] at hmul
  have hpos : 0 < A.relIndex H := Nat.pos_of_ne_zero index_ne_zero_of_finite
  have hH : C.relIndex H < 4 := hbound.1
  have hi : A.relIndex H = 1 := by omega
  have hAH' : H ≤ A := relIndex_eq_one.mp hi
  have hcard₁ := small_critical_commutator_card s hc p₁ hsmall₁
  have hcard₂ := small_critical_commutator_card s hc p₂ hsmall₂
  have hle : ⁅Z d.radical c₂,Z d.radical v.start⁆ ≤ ⁅Z d.radical c₁,Z d.radical v.start⁆ := by
    rw [commutator_comm (Z d.radical c₂),commutator_comm (Z d.radical c₁)]
    exact core_join_commutator_le C (Z d.radical v.start) (Z d.radical c₁) (Z d.radical c₂)
      (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
        (Z_centralizes_Q d.radical v.start v.path.start_color)))
      ((hreverse p₁).trans (Z_normalized d.radical v.start))
      ((show Z d.radical c₂ ≤ H from le_sup_right.trans le_sup_right).trans hAH')
  let := finite_Z d.radical c₁
  let : Finite (⁅Z d.radical c₁,Z d.radical v.start⁆ : Subgroup (FreeAmalgam d.radical)) :=
    Finite.of_injective (inclusion (((critical_Z_commutator_le_moving (h := h) p₁).trans inf_le_left).trans
      (DistanceEight.U_le_Z d.radical c₁))) (inclusion_injective _)
  refine ⟨?_,hcard₁,(eq_of_le_of_card_ge hle (by omega)).symm⟩
  change C.relIndex H = 2
  omega

include e hz hn in
/-- The original radical supplies the literal chain and the whole-core
commutator obstruction. Any two critical seeds on that chain satisfying the
source's core-containment and endpoint-fixedness conditions have the same
nonzero line. Selection of the two reverse seeds remains a separate step. -/
theorem original_radical_terminal_seed_comparison_knownSimple
    (hb : 4 < replacementDistance h d)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hfirst : p.walk.getVert 1 = beta d.radical) :
    let T := ((R.subgroupOf (L ⊔ R)).subgroupOf d.overgroup).map (embedM d.radical)
    ∃ q₀ : BackwardShift (h := h) p,
      act d.radical q₀.transporter (beta d.radical) = q₀.edge ∧
      T.map (MulAut.conj q₀.transporter⁻¹).toMonoidHom = Q d.radical q₀.edge ∧
      T.map (MulAut.conj q₀.transporter⁻¹).toMonoidHom ⊔ Z d.radical a' =
        stabilizer d.radical (alpha d.radical) ∧
      ∃ c c', ∃ p₀ : CriticalPath d.radical (replacementGeometry h d) c c',
      SylowTerminalPath.ShiftChain (h := h) q₀.path p₀ (replacementDistance h d) ∧
      ∃ (q : BackwardShift (h := h) p₀) (r : BackwardShift (h := h) q.path)
        (t : BackwardShift (h := h) r.path) (v : BackwardShift (h := h) t.path),
      SylowTerminalPath.OrbitPrefix (h := h) r.path (replacementDistance h d) ∧
      act d.radical v.transporter (t.path.walk.getVert 1) = v.edge ∧
      let W := ⁅Z d.radical v.start,Q d.radical t.start⁆
      W ≤ Q d.radical t.start ∧ Nat.card W ≤ 8 ∧
      (¬ Ltilde d.radical t.start ≤ normalizer (W : Set (FreeAmalgam d.radical))) ∧
      (¬ W ≤ centralizer (Z d.radical (r.path.walk.getVert (r.path.walk.length-2)) :
        Set (FreeAmalgam d.radical))) ∧
      (SmallMover.join (U d.radical v.start) (Q d.radical v.start) (Q d.radical v.edge) 4 ≠
        SmallMover.join (U d.radical t.start) (Q d.radical t.start) (Q d.radical v.edge) 4 →
        ∀ {c₁ c₂ : Vertex d.radical},
          CriticalPath d.radical (replacementGeometry h d) c₁ v.start →
          CriticalPath d.radical (replacementGeometry h d) c₂ v.start →
          Z d.radical c₁ ≤ Q d.radical t.start →
          Z d.radical c₂ ≤ Q d.radical t.start →
          Z d.radical c₁ ≤ centralizer
            (Z d.radical (r.path.walk.getVert (r.path.walk.length-2)) : Set (FreeAmalgam d.radical)) →
          Z d.radical c₂ ≤ centralizer
            (Z d.radical (r.path.walk.getVert (r.path.walk.length-2)) : Set (FreeAmalgam d.radical)) →
          (Q d.radical v.start).relIndex
            (Q d.radical v.start ⊔ (Z d.radical c₁ ⊔ Z d.radical c₂)) = 2 ∧
          Nat.card (⁅Z d.radical c₁,Z d.radical v.start⁆ : Subgroup (FreeAmalgam d.radical)) = 2 ∧
          ⁅Z d.radical c₁,Z d.radical v.start⁆ = ⁅Z d.radical c₂,Z d.radical v.start⁆) := by
  obtain ⟨q₀,hqe,hqT,hqgen,c,c',p₀,hchain,q,r,t,v,hr,hv,_⟩ :=
    original_radical_terminal_core_product_knownSimple hb hcard p hfirst
  have ht : SylowTerminalPath.OrbitPrefix (h := h) t.path (replacementDistance h d) := by
    intro i hi hl
    exact SylowTerminalPath.orbitPrefix_backwardShift hb r.path t hr i (Nat.lt_succ_of_lt hi) hl
  have hW := orbit_terminal_core_commutator_not_normalized_knownSimple hb hcard q.path r t v ht
  refine ⟨q₀,hqe,hqT,hqgen,c,c',p₀,hchain,q,r,t,v,hr,hv,hW.1,hW.2.1,hW.2.2.1,hW.2.2.2,?_⟩
  intro hne c₁ c₂ p₁ p₂ h₁Q h₂Q h₁C h₂C
  exact four_shift_terminal_seed_pair_knownSimple hb hcard p₀ q r t v hr hv hne p₁ p₂ h₁Q h₂Q h₁C h₂C

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
