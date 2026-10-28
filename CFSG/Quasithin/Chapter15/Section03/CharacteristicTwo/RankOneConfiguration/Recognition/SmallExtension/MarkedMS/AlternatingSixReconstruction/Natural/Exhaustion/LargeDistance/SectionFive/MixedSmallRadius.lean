module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.MixedSmallSeeds

/-!
# Small predecessor radii and relative backward selection in the mixed plane

At predecessor-radius image order at most two, the endpoint seed already
fills that image. The full radius therefore has the endpoint's commutator
line and centralizer kernel on the starting seed. This includes the entire
central attachment in the order-thirty-two cover.

Relative-normalizer generation supplies an element moving the full critical
kernel: the endpoint centralizes that kernel, whereas the whole starting
stabilizer cannot normalize it. The conjugate critical walk has a different
kernel and line. Mixed-plane rigidity forces its first edge to differ. In
the small-radius branch its conjugate predecessor radius has image order
two again, but escapes the old radius even modulo the starting two-core.

For the actual backward selection, span an eligible seed under the genuine
relative normalizer. If every conjugate stayed in the predecessor core and
fixed the reverse kernel, the small critical commutator estimate would make
the span locally normal modulo the starting seed. The existing residual
action theorem would put it in the Baumann slice, contradicting eligibility.
Holomorph realization turns the resulting conjugate into an actual neighbor
of the selected edge. It either gives the backward critical walk with every
overlap retained, or has nonzero commutator with the full reverse kernel.
In the latter case the order bound identifies this commutator with the full
predecessor-core commutator, of order exactly two; the moving kernel has the
same nonzero commutator.

The nonzero-kernel alternative still needs elimination. This module does
not assert the mixed-plane distance bound, the larger Sylow exclusions,
the distance-four residual estimates or the unconditional LargeDistanceInput.
Both moved covers, all central attachments, the original radical distinction
and the literal replacement graph and quotient maps are retained.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (3.3)(ii), printed pp.866--867, and the backward normalization and
kernel argument of (5.7)--(5.8), pp.919--920. The relative-normalizer and
holomorph conventions are those of the existing SylowNormalizer module.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.ChapterB.Offenders CFSG.Quasithin.ChapterB.Offenders.Six
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.MixedSmallRadius
local notation "S" => Equiv.Perm (Fin 6)

universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R}

private theorem index_two_sup_kernel {F : Type*} [Group F]
    (V Q A : Subgroup F) [Finite V] (hA : A ≤ V)
    (hi : Q.relIndex V = 2) (hne : ¬ A ≤ Q) :
    (V ⊓ Q) ⊔ A = V := by
  let K := V ⊓ Q
  let E := K ⊔ A
  have hEV : E ≤ V := sup_le inf_le_left hA
  let : Finite E := Finite.of_injective (inclusion hEV) (inclusion_injective _)
  have hKV : K.relIndex V = 2 := by simpa only [K, inf_relIndex_left] using hi
  have hne' : K.relIndex E ≠ 1 := by
    intro hh
    exact hne ((le_sup_right.trans (relIndex_eq_one.mp hh)).trans inf_le_right)
  have hpos : 0 < K.relIndex E := Nat.pos_of_ne_zero index_ne_zero_of_finite
  have hp : 0 < E.relIndex V := Nat.pos_of_ne_zero index_ne_zero_of_finite
  have ht := relIndex_mul_relIndex K E V le_sup_left hEV
  rw [hKV] at ht
  have htwo : 2 ≤ K.relIndex E := by omega
  have he : E.relIndex V=1 := by nlinarith
  exact le_antisymm hEV (relIndex_eq_one.mp he)

/-- A small predecessor radius has exactly the endpoint's image, full
centralizer kernel and commutator line at the original starting vertex. -/
theorem small_predecessor_radius_data
    (s : FullSymmetricAction h e hz hn d) (hc : DistanceTwo.CentralLayer d)
    (hb : 2 < replacementDistance h d) {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hp : (Q d.radical a').relIndex (Z d.radical a) < 4)
    (hr : (Q d.radical a).relIndex
      (V d.radical (p.walk.getVert (p.walk.length-2))) ≤ 2) :
    let W := V d.radical (p.walk.getVert (p.walk.length-2))
    (Q d.radical a).relIndex W = 2 ∧
      Q d.radical a ⊔ W = Q d.radical a ⊔ Z d.radical a' ∧
      ⁅Z d.radical a, W⁆ = ⁅Z d.radical a, Z d.radical a'⁆ ∧
      Z d.radical a ⊓ centralizer (W : Set (FreeAmalgam d.radical)) =
        Z d.radical a ⊓ Q d.radical a' := by
  let c := p.walk.getVert (p.walk.length-2)
  let W := V d.radical c
  have hl : p.walk.length = replacementDistance h d := p.length_eq_b
  have hc0 : color d.radical c = false := by
    apply (p.vertex_color (Nat.sub_le _ _)).mpr
    have he := replacementDistance_even h d
    rw [Nat.even_iff] at he ⊢
    omega
  have hd : (cosetGraph d.radical).dist a' c ≤ 2 := by
    rw [SimpleGraph.dist_comm, p.dist_end]
    omega
  have hAW : Z d.radical a' ≤ W := le_iSup_of_le a' (le_iSup_of_le hd le_rfl)
  have hWG : W ≤ stabilizer d.radical a := by
    apply (V_le_iff d.radical hc0 _).mpr
    intro v hv hvc
    apply Z_le_stabilizer_of_dist_le v _
    rw [(replacementGeometry h d).distance_constant v hv]
    have hca : (cosetGraph d.radical).dist c a = p.walk.length-2 := by
      rw [SimpleGraph.dist_comm, p.dist_start (Nat.sub_le _ _)]
    have hh := (cosetGraph_connected d.radical).dist_triangle (u := v) (v := c) (w := a)
    change _ ≤ replacementDistance h d
    omega
  let := finite_stabilizer d.radical a
  let : Finite W := Finite.of_injective (inclusion hWG) (inclusion_injective _)
  have hi : (Q d.radical a).relIndex W = 2 := by
    have hh := relIndex_le_of_le_right (H := Q d.radical a) hAW index_ne_zero_of_finite
    rw [(small_critical_indices s hc p hp).2] at hh
    exact Nat.le_antisymm hr hh
  have hdecomp := index_two_sup_kernel W (Q d.radical a) (Z d.radical a')
    hAW hi (critical_reverse_pair s hc p).2
  have hQ : Q d.radical a ≤ centralizer (Z d.radical a : Set (FreeAmalgam d.radical)) :=
    le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q d.radical a p.start_color))
  have hcomm : ⁅Z d.radical a, Z d.radical a'⁆ = ⁅Z d.radical a, W⁆ :=
    commutator_eq_of_centralizing_sup hdecomp (inf_le_right.trans hQ)
      ((hAW.trans hWG).trans (Z_normalized d.radical a))
  refine ⟨hi, ?_, hcomm.symm, ?_⟩
  · apply le_antisymm
    · apply sup_le le_sup_left
      change W ≤ _
      rw [←hdecomp]
      exact sup_le (inf_le_right.trans le_sup_left) le_sup_right
    · exact sup_le_sup_left hAW _
  · apply le_antisymm
    · apply le_inf inf_le_left
      rw [←C_eq_Q s hc a' p.end_color]
      exact le_inf (inf_le_left.trans (Z_le_stabilizer_of_dist_le a _ p.critical.1.le))
        (inf_le_right.trans (centralizer_le hAW))
    · apply le_inf inf_le_left
      apply le_centralizer_iff.mp
      change W ≤ _
      rw [←hdecomp]
      exact sup_le
        ((inf_le_right.trans hQ).trans (centralizer_le inf_le_left))
        ((commutator_eq_bot_iff_le_centralizer.mp
          (Z_centralizes_Q d.radical a' p.end_color)).trans (centralizer_le inf_le_right))

/-- Relative-normalizer generation selects a second small critical seed
with a different full kernel and line, on the same original graph. The
mixed-plane rigidity forces its first edge to differ as well. -/
theorem mixed_small_relative_seed_pair_knownSimple
    (hb : 2 < replacementDistance h d) (u : S)
    (him : d.radical.map (SourceReduction.projection h e hz hn d) =
      plus.map (MulAut.conj u).toMonoidHom)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hp : (Q d.radical a').relIndex (Z d.radical a) < 4) :
    ∃ t, Adjacent d.radical a t ∧
      (normalizer (Q d.radical t : Set (FreeAmalgam d.radical)) ⊓
        stabilizer d.radical a) ⊔ Z d.radical a' = stabilizer d.radical a ∧
      ∃ g ∈ normalizer (Q d.radical t : Set (FreeAmalgam d.radical)) ⊓
          stabilizer d.radical a,
        ∃ q : CriticalPath d.radical (replacementGeometry h d) a (act d.radical g⁻¹ a'),
          (∀ i, q.walk.getVert i = act d.radical g⁻¹ (p.walk.getVert i)) ∧
          (Q d.radical (act d.radical g⁻¹ a')).relIndex (Z d.radical a) = 2 ∧
          Z d.radical a ⊓ Q d.radical (act d.radical g⁻¹ a') ≠
            Z d.radical a ⊓ Q d.radical a' ∧
          ⁅Z d.radical a, Z d.radical (act d.radical g⁻¹ a')⁆ ≠
            ⁅Z d.radical a, Z d.radical a'⁆ ∧
          q.walk.getVert 1 ≠ p.walk.getVert 1 := by
  let s := fullSymmetricAction_knownSimple h e hz hn d hb
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  obtain ⟨P, hP⟩ := large_distance_mixed_original_sylow_knownSimple hb u him
  obtain ⟨t, hat, hgen⟩ := SylowNormalizer.sylow_critical_generating_neighbor_at_knownSimple
    (e := e) (hz := hz) (hn := hn) hb P hP p
  let N := normalizer (Q d.radical t : Set (FreeAmalgam d.radical)) ⊓ stabilizer d.radical a
  let K := Z d.radical a ⊓ Q d.radical a'
  have hex : ∃ g ∈ N, g ∉ normalizer (K : Set (FreeAmalgam d.radical)) := by
    by_contra! hall
    apply small_critical_kernel_not_normalized s hc p hp
    rw [←hgen]
    apply sup_le hall
    exact ((commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q d.radical a' p.end_color)).trans
        (centralizer_le inf_le_right)).trans (Subgroup.centralizer_le_normalizer _)
  obtain ⟨g, hg, hgK⟩ := hex
  have hga : act d.radical g⁻¹ a = a := (stabilizer d.radical a).inv_mem hg.2
  have hZa : (Z d.radical a).map (MulAut.conj g).toMonoidHom = Z d.radical a := by
    simpa only [inv_inv, hga] using (Z_act d.radical g⁻¹ a).symm
  have hexq : ∃ q : CriticalPath d.radical (replacementGeometry h d)
      (act d.radical g⁻¹ a) (act d.radical g⁻¹ a'),
      ∀ i, q.walk.getVert i = act d.radical g⁻¹ (p.walk.getVert i) := by
    refine ⟨p.act g⁻¹, ?_⟩
    intro i
    simp only [CriticalPath.act, actWalk_getVert]
  rw [hga] at hexq
  obtain ⟨q, hwalk⟩ := hexq
  have hq : (Q d.radical (act d.radical g⁻¹ a')).relIndex (Z d.radical a) = 2 := by
    rw [Q_act, inv_inv, ←hZa, relIndex_map_map_of_injective _ _ (MulAut.conj g).injective]
    exact (small_critical_indices s hc p hp).1
  have hkernel : Z d.radical a ⊓ Q d.radical (act d.radical g⁻¹ a') ≠ K := by
    intro he
    apply hgK
    apply mem_normalizer_iff_map_conj_eq.mpr
    change (Z d.radical a ⊓ Q d.radical a').map (MulAut.conj g).toMonoidHom = K
    rw [Subgroup.map_inf _ _ _ (MulAut.conj g).injective, hZa, ←inv_inv g, ←Q_act]
    exact he
  have hline : ⁅Z d.radical a, Z d.radical (act d.radical g⁻¹ a')⁆ ≠
      ⁅Z d.radical a, Z d.radical a'⁆ := by
    intro he
    exact hkernel (small_critical_equal_commutators_kernel s hc q p (by omega) hp he)
  refine ⟨t, hat, hgen, g, hg, q, hwalk, hq, hkernel, hline, ?_⟩
  intro he
  exact hkernel (MixedSmallSeeds.mixed_small_paths_same_first_knownSimple
    hb u him p q hp (by omega) he).2.2.symm

/-- In the remaining small-predecessor-radius branch, the generating
relative normalizer supplies an actual conjugate critical walk whose radius
escapes the original radius even modulo the starting core. Both radius
images have order two and their full starting kernels are different. -/
theorem mixed_small_radius_relative_escape_knownSimple
    (hb : 2 < replacementDistance h d) (u : S)
    (him : d.radical.map (SourceReduction.projection h e hz hn d) =
      plus.map (MulAut.conj u).toMonoidHom)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hp : (Q d.radical a').relIndex (Z d.radical a) < 4)
    (hr : (Q d.radical a).relIndex
      (V d.radical (p.walk.getVert (p.walk.length-2))) ≤ 2) :
    ∃ t, Adjacent d.radical a t ∧
      (normalizer (Q d.radical t : Set (FreeAmalgam d.radical)) ⊓
        stabilizer d.radical a) ⊔ Z d.radical a' = stabilizer d.radical a ∧
      ∃ g ∈ normalizer (Q d.radical t : Set (FreeAmalgam d.radical)) ⊓
          stabilizer d.radical a,
        ∃ q : CriticalPath d.radical (replacementGeometry h d) a (act d.radical g⁻¹ a'),
          (∀ i, q.walk.getVert i = act d.radical g⁻¹ (p.walk.getVert i)) ∧
          q.walk.getVert 1 ≠ p.walk.getVert 1 ∧
          (Q d.radical a).relIndex (V d.radical (q.walk.getVert (q.walk.length-2))) = 2 ∧
          ¬ V d.radical (q.walk.getVert (q.walk.length-2)) ≤
            Q d.radical a ⊔ V d.radical (p.walk.getVert (p.walk.length-2)) ∧
          Z d.radical a ⊓ centralizer
              (V d.radical (q.walk.getVert (q.walk.length-2)) : Set (FreeAmalgam d.radical)) ≠
            Z d.radical a ⊓ centralizer
              (V d.radical (p.walk.getVert (p.walk.length-2)) : Set (FreeAmalgam d.radical)) := by
  let s := fullSymmetricAction_knownSimple h e hz hn d hb
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  obtain ⟨t, hat, hgen, g, hg, q, hwalk, hqi, hkernel, hline, hfirst⟩ :=
    mixed_small_relative_seed_pair_knownSimple hb u him p hp
  have hpdata := small_predecessor_radius_data s hc hb p hp hr
  have hga : act d.radical g⁻¹ a = a := (stabilizer d.radical a).inv_mem hg.2
  have hQa : (Q d.radical a).map (MulAut.conj g).toMonoidHom = Q d.radical a := by
    simpa only [inv_inv, hga] using (Q_act d.radical g⁻¹ a).symm
  have hl : q.walk.length = p.walk.length := q.length_eq_b.trans p.length_eq_b.symm
  have hVq : V d.radical (q.walk.getVert (q.walk.length-2)) =
      (V d.radical (p.walk.getVert (p.walk.length-2))).map (MulAut.conj g).toMonoidHom := by
    rw [hl, hwalk, V_act, inv_inv]
  have hri : (Q d.radical a).relIndex (V d.radical (q.walk.getVert (q.walk.length-2))) = 2 := by
    rw [hVq, ←hQa, relIndex_map_map_of_injective _ _ (MulAut.conj g).injective]
    exact hpdata.1
  have hqsmall : (Q d.radical (act d.radical g⁻¹ a')).relIndex (Z d.radical a) < 4 := by omega
  have hqdata := small_predecessor_radius_data s hc hb q hqsmall hri.le
  refine ⟨t, hat, hgen, g, hg, q, hwalk, hfirst, hri, ?_, ?_⟩
  · intro hle
    have hcrit : Z d.radical (act d.radical g⁻¹ a') ≤
        V d.radical (q.walk.getVert (q.walk.length-2)) := by
      have hd : (cosetGraph d.radical).dist (act d.radical g⁻¹ a')
          (q.walk.getVert (q.walk.length-2)) ≤ 2 := by
        rw [SimpleGraph.dist_comm, q.dist_end]
        have hh : 2 < q.walk.length := q.length_eq_b ▸ hb
        omega
      exact le_iSup_of_le (act d.radical g⁻¹ a') (le_iSup_of_le hd le_rfl)
    have hQ : Q d.radical a ≤ centralizer (Z d.radical a : Set (FreeAmalgam d.radical)) :=
      le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
        (Z_centralizes_Q d.radical a p.start_color))
    have hA := critical_Z_le_stabilizer d.radical (replacementGeometry h d) a p.start_color
      (by rw [(replacementGeometry h d).distance_constant a p.start_color]
          exact replacementDistance_pos h d) p.critical
    have he := commutator_eq_of_centralizing_sup
      (show Q d.radical a ⊔ Z d.radical a' = Q d.radical a ⊔ Z d.radical a' from rfl)
      hQ (hA.trans (Z_normalized d.radical a))
    have hbound : ⁅Z d.radical a, Z d.radical (act d.radical g⁻¹ a')⁆ ≤
        ⁅Z d.radical a, Z d.radical a'⁆ := by
      apply (commutator_mono le_rfl (hcrit.trans hle)).trans
      rw [hpdata.2.1]
      exact he.symm.le
    apply hline
    let : Finite (⁅Z d.radical a, Z d.radical a'⁆ : Subgroup (FreeAmalgam d.radical)) :=
      Nat.finite_of_card_ne_zero (by rw [small_critical_commutator_card s hc p hp]; decide)
    exact eq_of_le_of_card_ge hbound (by
      rw [small_critical_commutator_card s hc p hp,
        small_critical_commutator_card s hc q hqsmall])
  · rw [hpdata.2.2.2, hqdata.2.2.2]
    exact hkernel

private theorem relative_small_orbit_witness
    (s : FullSymmetricAction h e hz hn d) (hc : DistanceTwo.CentralLayer d)
    (hb : 2 < replacementDistance h d)
    {a' c t : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hp : (Q d.radical a').relIndex (Z d.radical (alpha d.radical)) < 4)
    (hat : Adjacent d.radical (alpha d.radical) t) (hct : Adjacent d.radical c t)
    (hgen : (normalizer (Q d.radical t : Set (FreeAmalgam d.radical)) ⊓
        stabilizer d.radical (alpha d.radical)) ⊔ Z d.radical a' =
          stabilizer d.radical (alpha d.radical))
    (hel : ¬ U d.radical c ≤ B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)) :
    ∃ g ∈ normalizer (Q d.radical t : Set (FreeAmalgam d.radical)) ⊓
        stabilizer d.radical (alpha d.radical),
      ¬ (Z d.radical c).map (MulAut.conj g).toMonoidHom ≤
        Q d.radical (p.walk.getVert (p.walk.length-2)) ∨
      ¬ (Z d.radical c).map (MulAut.conj g).toMonoidHom ≤ centralizer
        (Z d.radical a' ⊓ Q d.radical (alpha d.radical) : Set (FreeAmalgam d.radical)) := by
  let N := normalizer (Q d.radical t : Set (FreeAmalgam d.radical)) ⊓
    stabilizer d.radical (alpha d.radical)
  let D := conjugateSpanBy (Z d.radical c) N
  have hdist : (cosetGraph d.radical).dist c (alpha d.radical) ≤ 2 := by
    have h1 : (cosetGraph d.radical).dist c t = 1 :=
      SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj d.radical _ _).mpr hct)
    have h2 : (cosetGraph d.radical).dist t (alpha d.radical) = 1 :=
      SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj d.radical _ _).mpr (adjacent_symm d.radical hat))
    simpa only [h1, h2] using (cosetGraph_connected d.radical).dist_triangle
      (u := c) (v := t) (w := alpha d.radical)
  have hDV : D ≤ V d.radical (alpha d.radical) :=
    conjugateSpanBy_le (le_iSup_of_le c (le_iSup_of_le hdist le_rfl))
      (inf_le_right.trans (DistanceEight.V_normalized d.radical _))
  by_contra! hbad
  have hDP : D ≤ Q d.radical (p.walk.getVert (p.walk.length-2)) := by
    rw [show D = conjugateSpanBy (Z d.radical c) N from rfl, conjugateSpanBy_eq_iSup_conj]
    exact iSup_le (fun g => (hbad g g.property).1)
  have hDF : D ≤ centralizer
      (Z d.radical a' ⊓ Q d.radical (alpha d.radical) : Set (FreeAmalgam d.radical)) := by
    rw [show D = conjugateSpanBy (Z d.radical c) N from rfl, conjugateSpanBy_eq_iSup_conj]
    exact iSup_le (fun g => (hbad g g.property).2)
  have hmove : ⁅D, Z d.radical a'⁆ ≤ Z d.radical (alpha d.radical) :=
    small_critical_predecessor_commutator s hc hb p hp D hDP hDF
  let Y := D ⊔ Z d.radical (alpha d.radical)
  have hYV : Y ≤ V d.radical (alpha d.radical) := sup_le hDV (Z_le_VBall d.radical _ 2)
  have hYmove : ⁅Y, Z d.radical a'⁆ ≤ Z d.radical (alpha d.radical) :=
    commutator_sup_le_of_relative_normal (stabilizer d.radical (alpha d.radical))
      D (Z d.radical (alpha d.radical)) (Z d.radical a') (Z d.radical (alpha d.radical))
      (Z_normalized d.radical _) (hDV.trans ((replacementGeometry h d).V_local _ rfl hb))
      (Z_le_stabilizer d.radical _) hmove
      (((critical_Z_commutator_le_moving (h := h) p).trans inf_le_left).trans
        (DistanceEight.U_le_Z d.radical _))
  have hYN : stabilizer d.radical (alpha d.radical) ≤ normalizer (Y : Set (FreeAmalgam d.radical)) := by
    rw [←hgen]
    exact sup_le
      ((le_inf (le_normalizer_conjugateSpanBy (Z d.radical c) N)
        (inf_le_right.trans (Z_normalized d.radical _))).trans
          (normalizer_inf_normalizer_le_normalizer_sup _ _))
      (le_normalizer_iff_commutator_le_left.mpr (hYmove.trans le_sup_right))
  exact hel ((DistanceEight.U_le_Z d.radical c).trans
    ((le_conjugateSpanBy (Z d.radical c) N).trans (le_sup_left.trans
      (normalized_radius_le_slice_of_critical_commutator s hc hb p Y hYV hYN hYmove))))


/-- The small-image mixed-plane branch supplies an eligible actual backward
neighbor. Either it gives the complete backward critical walk, or its
commutator with the full reverse kernel is exactly the nontrivial order-two
predecessor-core commutator. This keeps the original endpoint and graph. -/
theorem mixed_small_backward_or_kernel_knownSimple
    (hb : 2 < replacementDistance h d) (u : S)
    (him : d.radical.map (SourceReduction.projection h e hz hn d) =
      plus.map (MulAut.conj u).toMonoidHom)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hp : (Q d.radical a').relIndex (Z d.radical (alpha d.radical)) < 4) :
    ∃ t, Adjacent d.radical (alpha d.radical) t ∧
      (normalizer (Q d.radical t : Set (FreeAmalgam d.radical)) ⊓
        stabilizer d.radical (alpha d.radical)) ⊔ Z d.radical a' =
          stabilizer d.radical (alpha d.radical) ∧
      ∃ c, Adjacent d.radical c t ∧
        ¬ U d.radical c ≤ B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _) ∧
        ((∃ q : CriticalPath d.radical (replacementGeometry h d) c
            (p.walk.getVert (p.walk.length-2)),
          q.walk.getVert 1 = t ∧
          ∀ i ≤ p.walk.length-2, q.walk.getVert (i+2) = p.walk.getVert i) ∨
        (Z d.radical c ≤ Q d.radical (p.walk.getVert (p.walk.length-2)) ∧
          Nat.card (⁅Z d.radical a' ⊓ Q d.radical (alpha d.radical), Z d.radical c⁆ :
            Subgroup (FreeAmalgam d.radical)) = 2 ∧
          ⁅Z d.radical a' ⊓ Q d.radical (alpha d.radical), Z d.radical c⁆ =
            ⁅Z d.radical a' ⊓ Q d.radical (alpha d.radical),
              Q d.radical (p.walk.getVert (p.walk.length-2))⁆ ∧
          ⁅U d.radical a' ⊓ Q d.radical (alpha d.radical), Z d.radical c⁆ ≠ ⊥)) := by
  let s := fullSymmetricAction_knownSimple h e hz hn d hb
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  obtain ⟨P, hP⟩ := large_distance_mixed_original_sylow_knownSimple hb u him
  obtain ⟨t, hat, hgen⟩ := SylowNormalizer.sylow_critical_generating_neighbor_knownSimple
    (e := e) (hz := hz) (hn := hn) hb P hP p
  obtain ⟨c, hct, hel⟩ := exists_eligible_neighbor_at_edge s hc hb rfl hat
  obtain ⟨g, hg, horbit⟩ := relative_small_orbit_witness s hc hb p hp hat hct hgen hel
  have hcol : color d.radical c = false := by
    have h1 := adjacent_color_ne d.radical hat
    have h2 := adjacent_color_ne d.radical hct
    change false ≠ color d.radical t at h1
    cases hc : color d.radical c <;> cases ht : color d.radical t <;> simp_all
  have ht : color d.radical t = true := by
    have hh := adjacent_color_ne d.radical hat
    change false ≠ color d.radical t at hh
    cases he : color d.radical t <;> simp_all
  have hZt : Z d.radical c ≤ Q d.radical t :=
    ((Z_le_VBall d.radical c 2).trans ((replacementGeometry h d).V_le_Q hb c hcol)).trans
      (Q_le_adjacent_h d.radical ht hct)
  obtain ⟨j, hj, he⟩ := Escape.Propagation.Backward.Products.holomorph_realizes t c hcol hct g hg.1
  have hZ : Z d.radical (act d.radical j⁻¹ c) =
      (Z d.radical c).map (MulAut.conj g).toMonoidHom := by
    rw [Z_act, inv_inv]
    exact Escape.Propagation.Backward.Products.map_conj_eq_of_agree hZt he
  have hU : U d.radical (act d.radical j⁻¹ c) =
      (U d.radical c).map (MulAut.conj g).toMonoidHom := by
    rw [U_act, inv_inv]
    exact Escape.Propagation.Backward.Products.map_conj_eq_of_agree
      ((DistanceEight.U_le_Z d.radical c).trans hZt) he
  have hct' : Adjacent d.radical (act d.radical j⁻¹ c) t := by
    have hfix : act d.radical j⁻¹ t = t := (stabilizer d.radical t).inv_mem hj
    simpa only [hfix] using (adjacent_act_iff d.radical j⁻¹ c t).mpr hct
  have hB : (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).map
      (MulAut.conj g).toMonoidHom = B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _) :=
    mem_normalizer_iff_map_conj_eq.mp (Escape.Propagation.Rigidity.B_normalized hb _ rfl hg.2)
  have hel' : ¬ U d.radical (act d.radical j⁻¹ c) ≤
      B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _) := by
    rw [hU, ←hB]
    exact fun hh => hel ((map_le_map_iff_of_injective (MulAut.conj g).injective).mp hh)
  refine ⟨t, hat, hgen, act d.radical j⁻¹ c, hct', hel', ?_⟩
  by_cases hbad : Z d.radical (act d.radical j⁻¹ c) ≤
      Q d.radical (p.walk.getVert (p.walk.length-2))
  · right
    have hnf : ¬ Z d.radical (act d.radical j⁻¹ c) ≤ centralizer
        (Z d.radical a' ⊓ Q d.radical (alpha d.radical) : Set (FreeAmalgam d.radical)) := by
      rw [hZ] at hbad ⊢
      exact horbit.resolve_left (not_not.mpr hbad)
    have hne : ⁅Z d.radical a' ⊓ Q d.radical (alpha d.radical),
        Z d.radical (act d.radical j⁻¹ c)⁆ ≠ ⊥ := by
      intro hh
      exact hnf (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hh))
    have hR : d.radical.map s.projection ≤ pointCore.map (MulAut.conj u).toMonoidHom := by
      rw [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s, him]
      exact map_mono (plus_le_exceptional.trans
        CFSG.Quasithin.ChapterC.NaturalSixControl.Model.pointCore_eq_exceptional.symm.le)
    have hbound := small_critical_kernel_predecessor_card s hc hb u hR p hp
    let K := Z d.radical a' ⊓ Q d.radical (alpha d.radical)
    let H := ⁅K, Z d.radical (act d.radical j⁻¹ c)⁆
    let D := Q d.radical (p.walk.getVert (p.walk.length-2))
    have hKD : K ≤ D := by
      apply inf_le_left.trans
      apply Z_le_Q_of_dist_lt d.radical _ ((replacementGeometry h d).exists_critical _ p.end_color)
      rw [(replacementGeometry h d).distance_constant _ p.end_color, SimpleGraph.dist_comm, p.dist_end]
      have hh : p.walk.length = replacementDistance h d := p.length_eq_b
      change p.walk.length-(p.walk.length-2) < replacementDistance h d
      omega
    let := finite_stabilizer d.radical (p.walk.getVert (p.walk.length-2))
    let : Finite (⁅K, D⁆ : Subgroup (FreeAmalgam d.radical)) :=
      Finite.of_injective (inclusion ((Subgroup.commutator_le_sup _ _).trans
        ((sup_le hKD le_rfl).trans (fun _ hx => hx.1)))) (inclusion_injective _)
    have hHD : H ≤ ⁅K, D⁆ := commutator_mono le_rfl hbad
    let : Finite H := Finite.of_injective (inclusion hHD) (inclusion_injective _)
    have hHupper : Nat.card H ≤ 2 := (card_le_of_le hHD).trans hbound
    have hHlower : 1 < Nat.card H := (one_lt_card_iff_ne_bot H).mpr hne
    have hcard : Nat.card H = 2 := by omega
    refine ⟨hbad, hcard, eq_of_le_of_card_ge hHD (by rw [hcard]; exact hbound), ?_⟩
    rwa [←(critical_kernel_predecessor_moving s hc hb p).2.2
      (Z d.radical (act d.radical j⁻¹ c)) hbad]
  · left
    let w : (cosetGraph d.radical).Walk (act d.radical j⁻¹ c) (alpha d.radical) :=
      .cons ((cosetGraph_adj d.radical _ _).mpr hct')
        (.cons ((cosetGraph_adj d.radical _ _).mpr (adjacent_symm d.radical hat)) .nil)
    have hw : w.length = 2 := rfl
    have hcolor : color d.radical (act d.radical j⁻¹ c) = false := by
      rw [action_preserves_color, hcol]
    let q := p.prepend_two (Nat.le_of_lt hb) hcolor w hw hbad
    have hqt : q.walk.getVert 1 = t := by
      simp only [q, CriticalPath.prepend_two_walk, SimpleGraph.Walk.getVert_append,
        hw, show 1<2 from by decide, ite_true, w, SimpleGraph.Walk.getVert_cons_succ,
        SimpleGraph.Walk.getVert_zero]
    exact ⟨q, hqt, fun i hi => p.prepend_two_overlap _ _ _ _ _ hi⟩

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.MixedSmallRadius
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
