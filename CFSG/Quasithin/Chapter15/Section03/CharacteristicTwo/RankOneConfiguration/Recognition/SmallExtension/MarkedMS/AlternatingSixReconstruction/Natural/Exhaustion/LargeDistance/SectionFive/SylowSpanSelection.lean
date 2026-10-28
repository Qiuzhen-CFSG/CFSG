module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowTrappedKernel
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowKernelDecomposition
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CubeSmallSeeds

/-!
# A generating edge for a prescribed strict backward slice

At every component vertex, the full seed has index at most eight over an
incident edge seed. Indeed its edge-fixed elements belong to the literal
edge omega center, and the checked full-cover fixed-index bound applies.
Consequently two seeds on one edge span a section of order at most eight
over the starting seed. If the starting stabilizer normalized that span,
the symmetric-six small-section theorem would put it in the Baumann slice.

In the radical-image-order-sixteen branch, a generating relative edge
normalizer is the edge core itself. Transporting a prescribed eligible
neighbor to this edge therefore produces a span that the critical endpoint
does not normalize. The same transporter preserves the exact slice index.
For a strict slice and small critical image, the selected seed either gives
a backward critical path with every overlapping vertex retained, or is
trapped and moves the full reverse seed kernel and the larger source
X-kernel. The moving kernel has the same commutator as the full seed kernel;
the X-kernel commutator is only asserted nonzero and contained in the
selected seed. No central-generation or kernel identification is assumed.

The final consumer uses the actual restriction of the original MS radical
and its replacement embedding. Both cover orders and central attachments
are retained. The trapped alternative still needs the simultaneous paired
small-mover generation and fixer identities of (5.5)--(5.7), followed by the
residual transport and same-commutator alignment of (5.8). This module does
not assert strict backward escape, terminal exclusion or the distance bound.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (5.5)--(5.8), printed pp.915--920.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open scoped commutatorElement Pointwise
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowSpanSelection
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R}

include e hz hn in
/-- The full seed has index at most eight over the actual incident edge seed. -/
theorem edge_seed_index_le_eight
    (hb : 4 < replacementDistance h d)
    {a t : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t) :
    (Z d.radical t).relIndex (Z d.radical a) ≤ 8 := by
  let := finite_Z d.radical a
  let := (replacementGeometry h d).Z_elementary (replacementDistance_pos h d) a ha
  have ht : color d.radical t = true := by
    have hh := adjacent_color_ne d.radical hat
    cases he : color d.radical t <;> simp_all
  have hZaQ : Z d.radical a ≤ Q d.radical a := by
    apply Z_le_Q_of_dist_lt d.radical _ ((replacementGeometry h d).exists_critical _ ha)
    rw [SimpleGraph.dist_self,(replacementGeometry h d).distance_constant _ ha]
    exact replacementDistance_pos h d
  have hZaT := hZaQ.trans (Q_le_adjacent_h d.radical ht hat)
  have hCZ : Z d.radical a ⊓ centralizer (Q d.radical t : Set (FreeAmalgam d.radical)) ≤
      Z d.radical t := by
    intro z hz
    rw [Z,if_neg (by simp [ht])]
    exact mem_omegaCenter_iff.mpr ⟨hZaT hz.1,
      elemPow_eq_one_of_isElementaryAbelian z hz.1,hz.2⟩
  have hi := SylowKernelDecomposition.edge_fixed_index_bound
    (e := e) (hz := hz) (hn := hn) hb ha hat
  have hle := relIndex_le_of_le_left hCZ
    (index_ne_zero_of_finite : (Z d.radical a ⊓ centralizer
      (Q d.radical t : Set (FreeAmalgam d.radical))).relIndex (Z d.radical a) ≠ 0)
  rw [inf_relIndex_left] at hle
  exact hle.trans hi

include e hz hn in
/-- The adjacent-seed span has index at most eight over the starting seed. -/
theorem adjacent_seed_span_index_le_eight
    (hb : 4 < replacementDistance h d)
    {a c t : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t) (hct : Adjacent d.radical c t) :
    (Z d.radical a).relIndex (Z d.radical c ⊔ Z d.radical a) ≤ 8 := by
  have hc : color d.radical c = false := by
    have h1 := adjacent_color_ne d.radical hat
    have h2 := adjacent_color_ne d.radical hct
    rw [ha] at h1
    cases hc : color d.radical c <;> cases ht : color d.radical t <;> simp_all
  have ht : color d.radical t = true := by
    have hh := adjacent_color_ne d.radical hat
    cases he : color d.radical t <;> simp_all
  have hZaQ : Z d.radical a ≤ Q d.radical a := by
    apply Z_le_Q_of_dist_lt d.radical _ ((replacementGeometry h d).exists_critical _ ha)
    rw [SimpleGraph.dist_self,(replacementGeometry h d).distance_constant _ ha]
    exact replacementDistance_pos h d
  have hZaN : Z d.radical a ≤ normalizer (Z d.radical c : Set (FreeAmalgam d.radical)) :=
    (hZaQ.trans (Q_le_adjacent_h d.radical ht hat)).trans
      ((show Q d.radical t ≤ stabilizer d.radical c from
        fun _ hx => hx.2 _ (adjacent_symm d.radical hct)).trans (Z_normalized d.radical c))
  let := finite_Z d.radical c
  let := finite_Z d.radical a
  rw [relIndex_sup_of_normalizes _ _ hZaN]
  exact (relIndex_le_of_le_left (adjacent_Z_le d.radical ha hat)
    index_ne_zero_of_finite).trans (edge_seed_index_le_eight (e := e) (hz := hz) (hn := hn) hb hc hct)

private theorem normal_small_radius_le_slice_at
    (s : FullSymmetricAction h e hz hn d) (hb : 2 < replacementDistance h d)
    {a : Vertex d.radical} (ha : color d.radical a = false)
    (Y : Subgroup (FreeAmalgam d.radical)) (hYV : Y ≤ V d.radical a)
    (hYN : stabilizer d.radical a ≤ normalizer (Y : Set (FreeAmalgam d.radical)))
    (hindex : (Z d.radical a).relIndex Y ≤ 8) :
    Y ≤ B d.radical a ((replacementGeometry h d).Z_normal _) := by
  obtain ⟨g,rfl⟩ := exists_mVertex_of_color d.radical ha
  have hbase : act d.radical g⁻¹ (mVertex d.radical g) = alpha d.radical := by
    simp only [act_mVertex,mul_inv_cancel]
    rfl
  let j := (MulAut.conj (g⁻¹)⁻¹).toMonoidHom
  have hh := normal_small_radius_le_slice s hb
  rw [←hbase] at hh
  have hm := hh (Y.map j)
    (by rw [V_act]; exact map_mono hYV)
    (by rw [stabilizer_act]; exact (map_mono hYN).trans (Y.le_normalizer_map j))
    (by rw [Z_act,relIndex_map_map_of_injective _ _ (MulAut.conj (g⁻¹)⁻¹).injective]; exact hindex)
  rw [Escape.PairingControl.FirstPairing.B_act hb g⁻¹ (mVertex d.radical g) ha] at hm
  exact (map_le_map_iff_of_injective (MulAut.conj (g⁻¹)⁻¹).injective).mp hm

include e hz hn in
/-- Select a generating edge and transport the prescribed eligible seed to it.
The endpoint fails to normalize this same span, and the slice index is preserved. -/
theorem sixteen_eligible_span_selection_knownSimple
    (hb : 4 < replacementDistance h d)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {a a' delta : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hdelta : Adjacent d.radical delta (p.walk.getVert 1))
    (hel : ¬ U d.radical delta ≤ B d.radical a ((replacementGeometry h d).Z_normal _)) :
    ∃ t, Adjacent d.radical a t ∧
      ∃ g ∈ stabilizer d.radical a,
        act d.radical g (p.walk.getVert 1) = t ∧
        Adjacent d.radical (act d.radical g delta) t ∧
        Q d.radical t ⊔ Z d.radical a' = stabilizer d.radical a ∧
        (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
            (U d.radical (act d.radical g delta)) =
          (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex (U d.radical delta) ∧
        ¬ Z d.radical a' ≤ normalizer
          ((Z d.radical (act d.radical g delta) ⊔ Z d.radical a :
            Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)) := by
  have hb2 : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  obtain ⟨⟨P,hP⟩,_,_⟩ := SylowTerminal.four_lt_original_sylow_non_elementary_image_knownSimple
    (e := e) (hz := hz) (hn := hn) hb
  obtain ⟨t,hat,hgen⟩ := SylowNormalizer.sylow_critical_generating_neighbor_at_knownSimple
    (e := e) (hz := hz) (hn := hn) hb2 P hP p
  rw [SylowLarge.sixteen_edge_relative_normalizer_knownSimple
    (e := e) (hz := hz) (hn := hn) hb2 hcard p.start_color hat] at hgen
  have hl : 0 < p.walk.length := p.length_eq_b ▸ replacementDistance_pos h d
  have hfirst : Adjacent d.radical a (p.walk.getVert 1) := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) hl
  obtain ⟨g,hg,hgt⟩ := stabilizer_transitive_neighbors d.radical a hfirst hat
  let c := act d.radical g delta
  have hct : Adjacent d.radical c t := by
    rw [←hgt]
    exact (adjacent_act_iff d.radical g delta (p.walk.getVert 1)).mpr hdelta
  have hB : (B d.radical a ((replacementGeometry h d).Z_normal _)).map
      (MulAut.conj g⁻¹).toMonoidHom = B d.radical a ((replacementGeometry h d).Z_normal _) :=
    mem_normalizer_iff_map_conj_eq.mp (Escape.Propagation.Rigidity.B_normalized
      hb2 a p.start_color ((stabilizer d.radical a).inv_mem hg))
  have hi : (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex (U d.radical c) =
      (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex (U d.radical delta) := by
    change (B d.radical a _).relIndex (U d.radical (act d.radical g delta)) = _
    rw [U_act,←hB,relIndex_map_map_of_injective _ _ (MulAut.conj g⁻¹).injective,hB]
  have helc : ¬ U d.radical c ≤ B d.radical a ((replacementGeometry h d).Z_normal _) := by
    intro hh
    apply hel
    change U d.radical (act d.radical g delta) ≤ _ at hh
    rw [U_act,←hB] at hh
    exact (map_le_map_iff_of_injective (MulAut.conj g⁻¹).injective).mp hh
  refine ⟨t,hat,g,hg,hgt,hct,hgen,hi,?_⟩
  intro hnorm
  apply helc
  let Y := Z d.radical c ⊔ Z d.radical a
  have hYN : stabilizer d.radical a ≤ normalizer (Y : Set (FreeAmalgam d.radical)) := by
    rw [←hgen]
    refine sup_le ?_ hnorm
    apply le_trans (le_inf _ _) (normalizer_inf_normalizer_le_normalizer_sup _ _)
    · exact (show Q d.radical t ≤ stabilizer d.radical c from
        fun _ hx => hx.2 _ (adjacent_symm d.radical hct)).trans (Z_normalized d.radical c)
    · exact (show Q d.radical t ≤ stabilizer d.radical a from
        fun _ hx => hx.2 _ (adjacent_symm d.radical hat)).trans (Z_normalized d.radical a)
  have hdist : (cosetGraph d.radical).dist c a ≤ 2 := by
    have h1 : (cosetGraph d.radical).dist c t = 1 :=
      SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj d.radical _ _).mpr hct)
    have h2 : (cosetGraph d.radical).dist t a = 1 :=
      SimpleGraph.dist_eq_one_iff_adj.mpr
        ((cosetGraph_adj d.radical _ _).mpr (adjacent_symm d.radical hat))
    simpa only [h1,h2] using (cosetGraph_connected d.radical).dist_triangle
      (u := c) (v := t) (w := a)
  have hYV : Y ≤ V d.radical a :=
    sup_le ((Z_le_localZSpan d.radical _ _).trans (localZSpan_le_V d.radical hdist))
      (Z_le_VBall d.radical _ 2)
  exact (DistanceEight.U_le_Z d.radical c).trans (le_sup_left.trans
    (normal_small_radius_le_slice_at s hb2 p.start_color Y hYV hYN
      (adjacent_seed_span_index_le_eight (e := e) (hz := hz) (hn := hn) hb p.start_color hat hct)))

include e hz hn in
/-- A strict slice supplies either a literal backward path or a trapped
selected seed with nonzero full seed-kernel and full X-kernel commutators. -/
theorem sixteen_strict_backward_alternative_knownSimple
    (hb : 4 < replacementDistance h d)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {a a' delta : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical a) < 4)
    (hdelta : Adjacent d.radical delta (p.walk.getVert 1))
    (hstrict : 2 < (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical delta)) :
    ∃ t, Adjacent d.radical a t ∧
      ∃ g ∈ stabilizer d.radical a,
        act d.radical g (p.walk.getVert 1) = t ∧
        Adjacent d.radical (act d.radical g delta) t ∧
        Q d.radical t ⊔ Z d.radical a' = stabilizer d.radical a ∧
        2 < (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
          (U d.radical (act d.radical g delta)) ∧
        ¬ Z d.radical a' ≤ normalizer
          ((Z d.radical (act d.radical g delta) ⊔ Z d.radical a :
            Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)) ∧
        ((∃ q : CriticalPath d.radical (replacementGeometry h d)
            (act d.radical g delta) (p.walk.getVert (p.walk.length-2)),
          q.walk.getVert 1 = t ∧
          ∀ i ≤ p.walk.length-2, q.walk.getVert (i+2) = p.walk.getVert i) ∨
        (Z d.radical (act d.radical g delta) ≤ Q d.radical (p.walk.getVert (p.walk.length-2)) ∧
          ⁅Z d.radical a' ⊓ Q d.radical a,Z d.radical (act d.radical g delta)⁆ ≠ ⊥ ∧
          ⁅U d.radical a' ⊓ Q d.radical a,Z d.radical (act d.radical g delta)⁆ =
            ⁅Z d.radical a' ⊓ Q d.radical a,Z d.radical (act d.radical g delta)⁆ ∧
          ⁅X d.radical a' ⊓ Q d.radical a,Z d.radical (act d.radical g delta)⁆ ≠ ⊥ ∧
          ⁅X d.radical a' ⊓ Q d.radical a,Z d.radical (act d.radical g delta)⁆ ≤
            Z d.radical (act d.radical g delta))) := by
  have hb2 : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hcent := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hel : ¬ U d.radical delta ≤ B d.radical a ((replacementGeometry h d).Z_normal _) := by
    intro hh
    have he := relIndex_eq_one.mpr hh
    omega
  obtain ⟨t,hat,g,hg,hgt,hct,hgen,hi,hnorm⟩ := sixteen_eligible_span_selection_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hcard p hdelta hel
  let c := act d.radical g delta
  have hc : color d.radical c = false := by
    have h1 := adjacent_color_ne d.radical hat
    have h2 := adjacent_color_ne d.radical hct
    rw [p.start_color] at h1
    change color d.radical c ≠ color d.radical t at h2
    cases hc : color d.radical c <;> cases ht : color d.radical t <;> simp_all
  refine ⟨t,hat,g,hg,hgt,hct,hgen,(by rwa [hi]),hnorm,?_⟩
  by_cases htrap : Z d.radical c ≤ Q d.radical (p.walk.getVert (p.walk.length-2))
  · apply Or.inr
    have hdist : (cosetGraph d.radical).dist c a ≤ 2 := by
      have h1 : (cosetGraph d.radical).dist c t = 1 :=
        SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj d.radical _ _).mpr hct)
      have h2 : (cosetGraph d.radical).dist t a = 1 :=
        SimpleGraph.dist_eq_one_iff_adj.mpr
          ((cosetGraph_adj d.radical _ _).mpr (adjacent_symm d.radical hat))
      simpa only [h1,h2] using (cosetGraph_connected d.radical).dist_triangle
        (u := c) (v := t) (w := a)
    have hZG : Z d.radical c ≤ stabilizer d.radical a :=
      ((Z_le_localZSpan d.radical _ _).trans (localZSpan_le_V d.radical hdist)).trans
        ((replacementGeometry h d).V_local a p.start_color (by
          rw [(replacementGeometry h d).distance_constant a p.start_color]; exact hb2))
    have hne : ⁅Z d.radical a' ⊓ Q d.radical a,Z d.radical c⁆ ≠ ⊥ := by
      intro hzero
      apply hnorm
      rw [commutator_comm] at hzero
      have hmove := small_critical_predecessor_commutator s hcent hb2 p hsmall
        (Z d.radical c) htrap (commutator_eq_bot_iff_le_centralizer.mp hzero)
      have hZmove : ⁅Z d.radical a,Z d.radical a'⁆ ≤ Z d.radical a :=
        ((critical_Z_commutator_le_moving (h := h) p).trans inf_le_left).trans
          (DistanceEight.U_le_Z d.radical a)
      have hh := commutator_sup_le_of_relative_normal (stabilizer d.radical a)
        (Z d.radical c) (Z d.radical a) (Z d.radical a') (Z d.radical a)
        (Z_normalized d.radical a) hZG (Z_le_stabilizer d.radical a) hmove hZmove
      exact le_normalizer_iff_commutator_le_left.mpr (hh.trans le_sup_right)
    have hZX : Z d.radical a' ≤ X d.radical a' := by
      apply (replacementGeometry h d).omega_bound a' p.end_color
      rw [(replacementGeometry h d).distance_constant a' p.end_color]
      exact replacementDistance_pos h d
    have hXne : ⁅X d.radical a' ⊓ Q d.radical a,Z d.radical c⁆ ≠ ⊥ := by
      intro hh
      exact hne (le_bot_iff.mp ((commutator_mono (inf_le_inf_right _ hZX) le_rfl).trans_eq hh))
    have ht : color d.radical t = true := by
      have hh := adjacent_color_ne d.radical hat
      rw [p.start_color] at hh
      cases he : color d.radical t <;> simp_all
    have hXG : X d.radical a' ⊓ Q d.radical a ≤ stabilizer d.radical c :=
      (inf_le_right.trans (Q_le_adjacent_h d.radical ht hat)).trans
        (fun _ hx => hx.2 _ (adjacent_symm d.radical hct))
    exact ⟨htrap,hne,(critical_kernel_predecessor_moving s hcent hb2 p).2.2
      (Z d.radical c) htrap |>.symm,hXne,
      le_normalizer_iff_commutator_le_right.mp (hXG.trans (Z_normalized d.radical c))⟩
  · let w : (cosetGraph d.radical).Walk c a :=
      .cons ((cosetGraph_adj d.radical _ _).mpr hct)
        (.cons ((cosetGraph_adj d.radical _ _).mpr (adjacent_symm d.radical hat)) .nil)
    have hw : w.length = 2 := rfl
    let q := p.prepend_two (Nat.le_of_lt hb2) hc w hw htrap
    have hqt : q.walk.getVert 1 = t := by
      simp only [q,CriticalPath.prepend_two_walk,SimpleGraph.Walk.getVert_append,
        hw,show 1<2 from by decide,ite_true,w,SimpleGraph.Walk.getVert_cons_succ,
        SimpleGraph.Walk.getVert_zero]
    exact Or.inl ⟨q,hqt,fun i hi => p.prepend_two_overlap _ _ _ _ _ hi⟩

include e hz hn in
/-- The same selection for the literal restricted original radical. Its
conjugate under the chosen transporter generates with the critical endpoint. -/
theorem original_radical_strict_backward_alternative_knownSimple
    (hb : 4 < replacementDistance h d)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {a' delta : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical (alpha d.radical)) < 4)
    (hfirst : p.walk.getVert 1 = beta d.radical)
    (hdelta : Adjacent d.radical delta (beta d.radical))
    (hstrict : 2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical delta)) :
    let T := ((R.subgroupOf (L ⊔ R)).subgroupOf d.overgroup).map (embedM d.radical)
    ∃ t, Adjacent d.radical (alpha d.radical) t ∧
      ∃ g ∈ stabilizer d.radical (alpha d.radical),
        act d.radical g (p.walk.getVert 1) = t ∧
        Adjacent d.radical (act d.radical g delta) t ∧
        T.map (MulAut.conj g⁻¹).toMonoidHom ⊔ Z d.radical a' = stabilizer d.radical (alpha d.radical) ∧
        2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
          (U d.radical (act d.radical g delta)) ∧
        ¬ Z d.radical a' ≤ normalizer
          ((Z d.radical (act d.radical g delta) ⊔ Z d.radical (alpha d.radical) :
            Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)) ∧
        ((∃ q : CriticalPath d.radical (replacementGeometry h d)
            (act d.radical g delta) (p.walk.getVert (p.walk.length-2)),
          q.walk.getVert 1 = t ∧
          ∀ i ≤ p.walk.length-2, q.walk.getVert (i+2) = p.walk.getVert i) ∨
        (Z d.radical (act d.radical g delta) ≤ Q d.radical (p.walk.getVert (p.walk.length-2)) ∧
          ⁅Z d.radical a' ⊓ Q d.radical (alpha d.radical),Z d.radical (act d.radical g delta)⁆ ≠ ⊥ ∧
          ⁅U d.radical a' ⊓ Q d.radical (alpha d.radical),Z d.radical (act d.radical g delta)⁆ =
            ⁅Z d.radical a' ⊓ Q d.radical (alpha d.radical),Z d.radical (act d.radical g delta)⁆ ∧
          ⁅X d.radical a' ⊓ Q d.radical (alpha d.radical),Z d.radical (act d.radical g delta)⁆ ≠ ⊥ ∧
          ⁅X d.radical a' ⊓ Q d.radical (alpha d.radical),Z d.radical (act d.radical g delta)⁆ ≤
            Z d.radical (act d.radical g delta))) := by
  have hrestriction := (SylowLarge.sixteen_original_restriction_knownSimple
    (e := e) (hz := hz) (hn := hn) (by omega : 2 < replacementDistance h d) hcard).2.1
  obtain ⟨t,hat,g,hg,hgt,hct,hgen,hi,hnorm,halt⟩ := sixteen_strict_backward_alternative_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hcard p hsmall (by rwa [hfirst]) hstrict
  refine ⟨t,hat,g,hg,hgt,hct,?_,hi,hnorm,halt⟩
  have hT : ((R.subgroupOf (L ⊔ R)).subgroupOf d.overgroup).map (embedM d.radical) =
      Q d.radical (beta d.radical) := by
    rw [Q_beta]
    exact congrArg (Subgroup.map (embedM d.radical)) hrestriction.symm
  rw [hT,←Q_act,←hfirst,hgt]
  exact hgen

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowSpanSelection
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
