module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.PairExclusion
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.Backward.Products.RelativeNormalizer
public import Theory.GroupTheory.ConjugateSpanSylow

/-!
# Relative-normalizer generation and shifts in the original Sylow branches

The original Sylow radical restricts to a Sylow subgroup of the replacement
overgroup and normalizes its characteristic radical. Its symmetric image
contains a conjugate full point core. The critical endpoint supplies either
an even involution or a transposition, and the proved six-letter generation
then selects an incident edge whose relative normalizer generates the whole
starting stabilizer with that endpoint. This works at every original vertex
and does not identify the replacement radical with the restricted Sylow.

For a large critical image in the point-contained branch, take the orbit
span of a prescribed eligible seed under this relative normalizer. If the
whole span lay in the predecessor core, the original commutator estimate
would make its join with the starting seed locally normal and place it in
the Baumann slice. This contradicts eligibility. A holomorph representative
of an escaping orbit element gives an actual neighboring critical walk,
retaining the slice index and every overlapping vertex. The mixed-plane
application supplies its original Sylow witness and generating edge.

The four mixed-plane elements have distinct support sizes, so the entire
normalizer centralizes that plane. Pullback and transport to each actual
edge put its relative-normalizer commutator in the starting two-core.
Consequently the full relative normalizer fixes every small critical line
and normalizes its full seed kernel, including the central attachment.

Both moved covers remain intact. These are the generation, backward-shift
and small-kernel estimates needed for the mixed and larger Sylow branches;
the small-image shifts and terminal distance exclusions remain unproved.
In particular this module does not assert LargeDistanceInput.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), the relative-normalizer convention on printed p.881, (5.5)--(5.9),
pp.915--922, and the characteristic replacement on pp.932--933. Holomorph
realization uses the existing source correction in
`Reduction/Escape/Propagation/Backward/Products/RelativeNormalizer`.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
open CFSG.Quasithin.ChapterB.Offenders CFSG.Quasithin.ChapterB.Offenders.Six
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowNormalizer
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R}
local notation "M" => (L ⊔ R : Subgroup G)
local notation "T" => R.subgroupOf (L ⊔ R)
local notation "S" => Equiv.Perm (Fin 6)

private theorem point_core_in_normalizer
    (s : FullSymmetricAction h e hz hn d) (hb : 2 < replacementDistance h d)
    (P : Sylow 2 M) (hP : (P : Subgroup M) = T) :
    ∃ u : S, pointCore.map (MulAut.conj u).toMonoidHom ≤
      (normalizer (d.radical : Set d.overgroup)).map s.projection := by
  obtain ⟨⟨W,hW⟩,hN,_,_⟩ := SylowRestriction.original_sylow_restriction_knownSimple
    (e := e) (hz := hz) (hn := hn) hb P hP
  let W' := W.mapSurjective s.surjective
  obtain ⟨u,hu⟩ := MulAction.exists_smul_eq S sylow W'
  have hpc : pointCore ≤ sylowCarrier :=
    CFSG.Quasithin.ChapterC.NaturalSixControl.Model.pointCore_eq_exceptional.le.trans
      exceptional_le_sylowCarrier
  refine ⟨u,?_⟩
  have hle : pointCore.map (MulAut.conj u).toMonoidHom ≤ (W' : Subgroup S) := by
    rw [←hu]
    exact map_mono hpc
  exact hle.trans (map_mono (hW ▸ hN))

omit [Finite G] in
private theorem normalizer_embed (A : Subgroup d.overgroup) :
    (normalizer (A : Set d.overgroup)).map (embedM d.radical) =
      normalizer (A.map (embedM d.radical) : Set (FreeAmalgam d.radical)) ⊓
        stabilizer d.radical (alpha d.radical) := by
  have hc : (normalizer (A.map (embedM d.radical) : Set (FreeAmalgam d.radical))).comap
      (embedM d.radical) = normalizer (A : Set d.overgroup) := by
    rw [comap_normalizer_eq_of_le_range (map_le_range _ _),
      comap_map_eq_self_of_injective (embedM_injective d.radical)]
  have hbase : stabilizer d.radical (alpha d.radical) = (embedM d.radical).range :=
    stabilizer_m_base d.radical
  rw [←hc,map_comap_eq,hbase,inf_comm]

include e hz hn in
/-- The genuine relative normalizer and the endpoint generate the starting
stabilizer in every original Sylow branch. -/
theorem sylow_critical_generating_neighbor_knownSimple
    (hb : 2 < replacementDistance h d)
    (P : Sylow 2 M) (hP : (P : Subgroup M) = T)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a') :
    ∃ t, Adjacent d.radical (alpha d.radical) t ∧
      (normalizer (Q d.radical t : Set (FreeAmalgam d.radical)) ⊓
        stabilizer d.radical (alpha d.radical)) ⊔ Z d.radical a' =
          stabilizer d.radical (alpha d.radical) := by
  let s := fullSymmetricAction_knownSimple h e hz hn d hb
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  obtain ⟨u,hu⟩ := point_core_in_normalizer s hb P hP
  let A := (Z d.radical a').comap (embedM d.radical)
  obtain ⟨k,hk⟩ : ∃ k : alternatingGroup (Fin 6),
      ((normalizer (d.radical : Set d.overgroup)).map s.projection).map
        (MulAut.conj k.val).toMonoidHom ⊔ A.map s.projection = ⊤ := by
    by_cases hlarge : 4 ≤ (Q d.radical a').relIndex (Z d.radical (alpha d.radical))
    · obtain ⟨a,ha,hao,heven⟩ := exists_even_involution_reverse_critical_image s hc
        (replacementDistance_pos h d) p hlarge
      obtain ⟨k,hk⟩ := PointCoreEvenGeneration.exists_even_conjugate_pointCore_generates
        u ⟨a,heven⟩ (by rwa [←orderOf_submonoid])
      refine ⟨k,top_unique ?_⟩
      rw [←hk]
      exact sup_le_sup (map_mono hu) (zpowers_le.mpr ha)
    · obtain ⟨a,ha,hs⟩ := small_critical_image_swap s hc p (Nat.lt_of_not_ge hlarge)
      obtain ⟨k,hk⟩ := PointCoreEvenGeneration.exists_even_conjugate_pointCore_generates_swap u a hs
      refine ⟨k,top_unique ?_⟩
      rw [←hk]
      exact sup_le_sup (map_mono hu) (zpowers_le.mpr ha)
  have hkL : k.val ∈ (replacementComponent d).map s.projection := by
    rw [s.component_image]
    exact k.property
  obtain ⟨g,hg,hgk⟩ := hkL
  let D := d.radical.map (MulAut.conj g).toMonoidHom
  have hm : (normalizer (D : Set d.overgroup)).map s.projection =
      ((normalizer (d.radical : Set d.overgroup)).map s.projection).map
        (MulAut.conj k.val).toMonoidHom := by
    rw [←map_normalizer_eq_of_bijective _ (MulAut.conj g).bijective,map_map,map_map]
    congr 1
    apply MonoidHom.ext
    intro x
    change s.projection (g*x*g⁻¹) = k.val*s.projection x*k.val⁻¹
    rw [map_mul,map_mul,map_inv,hgk]
  have hQ : (pCore 2 d.overgroup).map (MulAut.conj g).toMonoidHom = pCore 2 d.overgroup :=
    mem_normalizer_iff_map_conj_eq.mp (by rw [normalizer_eq_top]; exact mem_top g)
  have hker : s.projection.ker ≤ normalizer (D : Set d.overgroup) := by
    rw [s.projection_kernel,←hQ]
    exact (map_mono (replacement_core_le_radical h d)).trans D.le_normalizer
  have hgen : normalizer (D : Set d.overgroup) ⊔ A = ⊤ := by
    apply map_injective_of_ker_le s.projection (hker.trans le_sup_left) le_top
    rw [Subgroup.map_sup,hm,map_top_of_surjective s.projection s.surjective]
    exact hk
  let f := (embedM d.radical g)⁻¹
  have hbase : stabilizer d.radical (alpha d.radical) = (embedM d.radical).range :=
    stabilizer_m_base d.radical
  have hf : f ∈ stabilizer d.radical (alpha d.radical) := by
    rw [hbase]
    exact ⟨g⁻¹,by simp only [map_inv,f]⟩
  have hfix : act d.radical f (alpha d.radical) = alpha d.radical := hf
  have hmapD : D.map (embedM d.radical) = Q d.radical (act d.radical f (beta d.radical)) := by
    rw [Q_act,Q_beta,map_map,map_map]
    congr 1
    ext x
    simp only [f,inv_inv,map_mul,map_inv,MulEquiv.coe_toMonoidHom,MulAut.conj_apply,
      MonoidHom.coe_comp,Function.comp_apply]
  refine ⟨act d.radical f (beta d.radical),?_,?_⟩
  · rw [←hfix]
    exact (adjacent_act_iff d.radical f _ _).mpr (base_adjacent d.radical)
  · have hmapA : A.map (embedM d.radical) = Z d.radical a' :=
      map_comap_eq_self ((critical_Z_le_stabilizer d.radical (replacementGeometry h d)
        (alpha d.radical) rfl (replacementDistance_pos h d) p.critical).trans_eq
          (stabilizer_m_base d.radical))
    have hh := congrArg (Subgroup.map (embedM d.radical)) hgen
    rwa [Subgroup.map_sup,normalizer_embed,hmapD,hmapA,←MonoidHom.range_eq_map,
      ←hbase] at hh

include e hz hn in
/-- The same relative-normalizer generation is available at every original
component vertex, with the given critical walk transported literally. -/
theorem sylow_critical_generating_neighbor_at_knownSimple
    (hb : 2 < replacementDistance h d)
    (P : Sylow 2 M) (hP : (P : Subgroup M) = T)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a') :
    ∃ t, Adjacent d.radical a t ∧
      (normalizer (Q d.radical t : Set (FreeAmalgam d.radical)) ⊓
        stabilizer d.radical a) ⊔ Z d.radical a' = stabilizer d.radical a := by
  obtain ⟨g,hg⟩ := exists_mVertex_of_color d.radical p.start_color
  have hbase : act d.radical g⁻¹ a = alpha d.radical := by
    rw [hg,act_mVertex,mul_inv_cancel]
    rfl
  have hrestore (v : Vertex d.radical) : act d.radical g (act d.radical g⁻¹ v) = v := by
    rw [←act_mul,inv_mul_cancel,act_one]
  have q := p.act g⁻¹
  rw [hbase] at q
  obtain ⟨t,hat,hgen⟩ := sylow_critical_generating_neighbor_knownSimple
    (e := e) (hz := hz) (hn := hn) hb P hP q
  have he : act d.radical g (alpha d.radical) = a := by rw [←hbase,hrestore]
  refine ⟨act d.radical g t,?_,?_⟩
  · simpa only [he] using (adjacent_act_iff d.radical g _ _).mpr hat
  · have hm := congrArg (Subgroup.map (MulAut.conj g⁻¹).toMonoidHom) hgen
    rw [Subgroup.map_sup,Subgroup.map_inf _ _ _ (MulAut.conj g⁻¹).injective,
      map_normalizer_eq_of_bijective _ (MulAut.conj g⁻¹).bijective,
      ←Q_act,←stabilizer_act,←Z_act,he,hrestore] at hm
    exact hm

/-- A prescribed eligible neighbor has a conjugate, under the genuine
relative normalizer, whose full seed escapes the predecessor core. -/
private theorem relative_orbit_escapes
    (s : FullSymmetricAction h e hz hn d) (hc : DistanceTwo.CentralLayer d)
    (hb : 2 < replacementDistance h d) (u : S)
    (hR : d.radical.map s.projection ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    {a' c t : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hlarge : 4 ≤ (Q d.radical a').relIndex (Z d.radical (alpha d.radical)))
    (hat : Adjacent d.radical (alpha d.radical) t) (hct : Adjacent d.radical c t)
    (hgen : (normalizer (Q d.radical t : Set (FreeAmalgam d.radical)) ⊓
        stabilizer d.radical (alpha d.radical)) ⊔ Z d.radical a' =
          stabilizer d.radical (alpha d.radical))
    (hel : ¬ U d.radical c ≤ B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)) :
    ∃ g ∈ normalizer (Q d.radical t : Set (FreeAmalgam d.radical)) ⊓
        stabilizer d.radical (alpha d.radical),
      ¬ (Z d.radical c).map (MulAut.conj g).toMonoidHom ≤
        Q d.radical (p.walk.getVert (p.walk.length-2)) := by
  let N := normalizer (Q d.radical t : Set (FreeAmalgam d.radical)) ⊓
    stabilizer d.radical (alpha d.radical)
  let D := conjugateSpanBy (Z d.radical c) N
  have hdist : (cosetGraph d.radical).dist c (alpha d.radical) ≤ 2 := by
    have h1 : (cosetGraph d.radical).dist c t = 1 :=
      SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj d.radical _ _).mpr hct)
    have h2 : (cosetGraph d.radical).dist t (alpha d.radical) = 1 :=
      SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj d.radical _ _).mpr (adjacent_symm d.radical hat))
    simpa only [h1,h2] using (cosetGraph_connected d.radical).dist_triangle
      (u := c) (v := t) (w := alpha d.radical)
  have hDV : D ≤ V d.radical (alpha d.radical) :=
    conjugateSpanBy_le (le_iSup_of_le c (le_iSup_of_le hdist le_rfl))
      (inf_le_right.trans (DistanceEight.V_normalized d.radical _))
  by_contra! hbad
  have hDP : D ≤ Q d.radical (p.walk.getVert (p.walk.length-2)) := by
    rw [show D = conjugateSpanBy (Z d.radical c) N from rfl,conjugateSpanBy_eq_iSup_conj]
    exact iSup_le (fun g => hbad g g.property)
  have hmove : ⁅D,Z d.radical a'⁆ ≤ Z d.radical (alpha d.radical) :=
    (commutator_mono (le_inf hDV hDP) le_rfl).trans
      (critical_radius_commutator_le_Z s hc u hR hb p hlarge)
  let Y := D ⊔ Z d.radical (alpha d.radical)
  have hYV : Y ≤ V d.radical (alpha d.radical) := sup_le hDV (Z_le_VBall d.radical _ 2)
  have hYmove : ⁅Y,Z d.radical a'⁆ ≤ Z d.radical (alpha d.radical) :=
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

/-- The source backward shift for a large critical image uses the actual
relative normalizer. Holomorph realization retains the selected neighbor,
its slice index and every overlapping vertex of the original walk. -/
theorem relative_large_backward_shift
    (s : FullSymmetricAction h e hz hn d) (hc : DistanceTwo.CentralLayer d)
    (hb : 2 < replacementDistance h d) (u : S)
    (hR : d.radical.map s.projection ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    {a' c t : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hlarge : 4 ≤ (Q d.radical a').relIndex (Z d.radical (alpha d.radical)))
    (hat : Adjacent d.radical (alpha d.radical) t) (hct : Adjacent d.radical c t)
    (hgen : (normalizer (Q d.radical t : Set (FreeAmalgam d.radical)) ⊓
        stabilizer d.radical (alpha d.radical)) ⊔ Z d.radical a' =
          stabilizer d.radical (alpha d.radical))
    (hel : ¬ U d.radical c ≤ B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)) :
    ∃ k ∈ stabilizer d.radical t,
      ∃ q : CriticalPath d.radical (replacementGeometry h d) (act d.radical k c)
          (p.walk.getVert (p.walk.length-2)),
        q.walk.getVert 1 = t ∧
        (∀ i ≤ p.walk.length-2, q.walk.getVert (i+2) = p.walk.getVert i) ∧
        (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
          (U d.radical (act d.radical k c)) =
        (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
          (U d.radical c) := by
  obtain ⟨g,hg,hout⟩ := relative_orbit_escapes s hc hb u hR p hlarge hat hct hgen hel
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
  obtain ⟨j,hj,he⟩ := Escape.Propagation.Backward.Products.holomorph_realizes t c hcol hct g hg.1
  have hZ : Z d.radical (act d.radical j⁻¹ c) =
      (Z d.radical c).map (MulAut.conj g).toMonoidHom := by
    rw [Z_act,inv_inv]
    exact Escape.Propagation.Backward.Products.map_conj_eq_of_agree hZt he
  have hU : U d.radical (act d.radical j⁻¹ c) =
      (U d.radical c).map (MulAut.conj g).toMonoidHom := by
    rw [U_act,inv_inv]
    exact Escape.Propagation.Backward.Products.map_conj_eq_of_agree
      ((DistanceEight.U_le_Z d.radical c).trans hZt) he
  have hct' : Adjacent d.radical (act d.radical j⁻¹ c) t := by
    have hfix : act d.radical j⁻¹ t = t := (stabilizer d.radical t).inv_mem hj
    simpa only [hfix] using (adjacent_act_iff d.radical j⁻¹ c t).mpr hct
  let w : (cosetGraph d.radical).Walk (act d.radical j⁻¹ c) (alpha d.radical) :=
    .cons ((cosetGraph_adj d.radical _ _).mpr hct')
      (.cons ((cosetGraph_adj d.radical _ _).mpr (adjacent_symm d.radical hat)) .nil)
  have hw : w.length = 2 := rfl
  have hbad : ¬ Z d.radical (act d.radical j⁻¹ c) ≤
      Q d.radical (p.walk.getVert (p.walk.length-2)) := by rwa [hZ]
  have hcolor : color d.radical (act d.radical j⁻¹ c) = false := by
    rw [action_preserves_color,hcol]
  let q := p.prepend_two (Nat.le_of_lt hb) hcolor w hw hbad
  have hqt : q.walk.getVert 1 = t := by
    simp only [q,CriticalPath.prepend_two_walk,SimpleGraph.Walk.getVert_append,
      hw,show 1<2 from by decide,ite_true,w,SimpleGraph.Walk.getVert_cons_succ,
      SimpleGraph.Walk.getVert_zero]
  refine ⟨j⁻¹,(stabilizer d.radical t).inv_mem hj,q,hqt,
    fun i hi => p.prepend_two_overlap _ _ _ _ _ hi,?_⟩
  have hB : (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).map
      (MulAut.conj g).toMonoidHom = B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _) :=
    mem_normalizer_iff_map_conj_eq.mp (Escape.Propagation.Rigidity.B_normalized hb _ rfl hg.2)
  rw [hU,←hB,relIndex_map_map_of_injective _ _ (MulAut.conj g).injective,hB]

/-- In the mixed-plane branch, both the original Sylow witness and the
relative generating edge are constructed. The large critical-image shift
therefore retains no separate generation or normalizer premise. -/
theorem mixed_large_backward_shift_knownSimple
    (hb : 2 < replacementDistance h d) (u : S)
    (him : d.radical.map (SourceReduction.projection h e hz hn d) =
      plus.map (MulAut.conj u).toMonoidHom)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hlarge : 4 ≤ (Q d.radical a').relIndex (Z d.radical (alpha d.radical))) :
    ∃ t, Adjacent d.radical (alpha d.radical) t ∧
      (normalizer (Q d.radical t : Set (FreeAmalgam d.radical)) ⊓
        stabilizer d.radical (alpha d.radical)) ⊔ Z d.radical a' =
          stabilizer d.radical (alpha d.radical) ∧
      ∃ c, Adjacent d.radical c t ∧
        ∃ q : CriticalPath d.radical (replacementGeometry h d) c
          (p.walk.getVert (p.walk.length-2)),
          q.walk.getVert 1 = t ∧
          (∀ i ≤ p.walk.length-2, q.walk.getVert (i+2) = p.walk.getVert i) ∧
          ¬ U d.radical c ≤ B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _) := by
  let s := fullSymmetricAction_knownSimple h e hz hn d hb
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hR : d.radical.map s.projection ≤ pointCore.map (MulAut.conj u).toMonoidHom := by
    rw [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s,him]
    exact map_mono (plus_le_exceptional.trans
      CFSG.Quasithin.ChapterC.NaturalSixControl.Model.pointCore_eq_exceptional.symm.le)
  obtain ⟨P,hP⟩ := large_distance_mixed_original_sylow_knownSimple hb u him
  obtain ⟨t,hat,hgen⟩ := sylow_critical_generating_neighbor_knownSimple
    (e := e) (hz := hz) (hn := hn) hb P hP p
  obtain ⟨c,hct,hel⟩ := exists_eligible_neighbor_at_edge s hc hb rfl hat
  obtain ⟨k,hk,q,hqt,hover,hidx⟩ := relative_large_backward_shift s hc hb u hR p hlarge hat hct hgen hel
  have hfix : act d.radical k t = t := hk
  refine ⟨t,hat,hgen,act d.radical k c,?_,q,hqt,hover,?_⟩
  · simpa only [hfix] using (adjacent_act_iff d.radical k c t).mpr hct
  · intro hle
    exact hel (relIndex_eq_one.mp (hidx.symm.trans (relIndex_eq_one.mpr hle)))

private theorem mixed_normalizer_centralizes :
    normalizer (plus : Set S) ≤ centralizer (plus : Set S) := by
  have huniq : ∀ i j : Fin 4,
      (planeWords 0 i).support.card = (planeWords 0 j).support.card →
        planeWords 0 i = planeWords 0 j := by decide +kernel
  intro g hg x hx
  obtain ⟨i,rfl⟩ := (mem_plus_iff x).mp hx
  have hconj := (mem_normalizer_iff.mp hg (planeWords 0 i)).mp
    ((mem_plus_iff _).mpr ⟨i,rfl⟩)
  obtain ⟨j,hj⟩ := (mem_plus_iff _).mp hconj
  have he : g * planeWords 0 i * g⁻¹ = planeWords 0 i := by
    rw [←hj]
    exact huniq j i (by rw [hj,Equiv.Perm.card_support_conj])
  exact (mul_inv_eq_iff_eq_mul.mp he).symm

private theorem mixed_conjugate_normalizer_centralizes (u : S) :
    normalizer (plus.map (MulAut.conj u).toMonoidHom : Set S) ≤
      centralizer (plus.map (MulAut.conj u).toMonoidHom : Set S) := by
  rw [←map_normalizer_eq_of_bijective _ (MulAut.conj u).bijective]
  exact (map_mono mixed_normalizer_centralizes).trans (map_centralizer_le_centralizer_image _ _)

/-- In the mixed-plane branch the full relative normalizer acts trivially
on the actual edge kernel modulo the starting two-core. -/
theorem mixed_relative_normalizer_commutator_knownSimple
    (hb : 2 < replacementDistance h d) (u : S)
    (him : d.radical.map (SourceReduction.projection h e hz hn d) =
      plus.map (MulAut.conj u).toMonoidHom)
    {a t : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t) :
    ⁅normalizer (Q d.radical t : Set (FreeAmalgam d.radical)) ⊓ stabilizer d.radical a,
      Q d.radical t⁆ ≤ Q d.radical a := by
  let s := fullSymmetricAction_knownSimple h e hz hn d hb
  have hc : (normalizer (d.radical : Set d.overgroup)).map s.projection ≤
      centralizer (d.radical.map s.projection : Set S) := by
    apply (le_normalizer_map s.projection).trans
    rw [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s,him]
    exact mixed_conjugate_normalizer_centralizes u
  have hr : ⁅normalizer (d.radical : Set d.overgroup),d.radical⁆ ≤ pCore 2 d.overgroup := by
    rw [←s.projection_kernel,←Subgroup.map_eq_bot_iff,map_commutator]
    exact commutator_eq_bot_iff_le_centralizer.mpr hc
  have hbase :
      ⁅normalizer (Q d.radical (beta d.radical) : Set (FreeAmalgam d.radical)) ⊓
          stabilizer d.radical (alpha d.radical),Q d.radical (beta d.radical)⁆ ≤
        Q d.radical (alpha d.radical) := by
    rw [Q_beta,←normalizer_embed,Q_alpha d.radical (replacement_radical_isPGroup h d)
      (replacement_core_le_radical h d),←map_commutator]
    exact map_mono hr
  obtain ⟨g,hg|hg⟩ := (adjacent_iff_exists_common d.radical a t).mp hat
  · rcases hg with ⟨rfl,rfl⟩
    have hh := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hbase
    rw [map_commutator,Subgroup.map_inf _ _ _ (MulAut.conj g⁻¹).injective,
      map_normalizer_eq_of_bijective _ (MulAut.conj g⁻¹).bijective,
      ←Q_act,←stabilizer_act,←Q_act] at hh
    simpa only [alpha,beta,act_mVertex,act_hVertex,one_mul] using hh
  · rw [hg.1] at ha
    cases ha

private theorem fixed_mod_central_normalizes {H : Type*} [Group H]
    (A Q D : Subgroup H) (hAQ : A ≤ normalizer (Q : Set H))
    (hDQ : D ≤ normalizer (Q : Set H))
    (hDA : ⁅D,A⁆ ≤ centralizer (Q : Set H)) :
    D ≤ normalizer ((⁅A,Q⁆ : Subgroup H) : Set H) := by
  apply le_normalizer_closure_iff.mpr
  rintro d hd _ ⟨a,ha,q,hq,rfl⟩
  have hq' : d*q*d⁻¹ ∈ Q := (mem_normalizer_iff.mp (hDQ hd) q).mp hq
  have hk : ⁅d,a⁆ ∈ centralizer (Q : Set H) := hDA (commutator_mem_commutator hd ha)
  have hcomm : ⁅a,d*q*d⁻¹⁆ ∈ Q :=
    le_normalizer_iff_commutator_le_right.mp hAQ (commutator_mem_commutator ha hq')
  have hzero : ⁅⁅d,a⁆,d*q*d⁻¹⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.mpr (hk _ hq').symm
  rw [conjugate_commutatorElement,show d*a*d⁻¹ = ⁅d,a⁆*a by
    simp [commutatorElement_def,mul_assoc],commutatorElement_mul_left_eq_conj_mul,
    hzero,mul_one,←hk _ hcomm,mul_inv_cancel_right]
  exact commutator_mem_commutator ha hq'

/-- The mixed-plane relative normalizer fixes the small critical line and
normalizes the full critical seed kernel. Both claims use the whole actor,
not only the edge kernel, and retain the order-thirty-two central attachment. -/
theorem mixed_small_critical_relative_control_knownSimple
    (hb : 2 < replacementDistance h d) (u : S)
    (him : d.radical.map (SourceReduction.projection h e hz hn d) =
      plus.map (MulAut.conj u).toMonoidHom)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical a) < 4) :
    let N := normalizer (Q d.radical (p.walk.getVert 1) : Set (FreeAmalgam d.radical)) ⊓
      stabilizer d.radical a
    ⁅Z d.radical a,Z d.radical a'⁆ ≤ centralizer (N : Set (FreeAmalgam d.radical)) ∧
      N ≤ normalizer ((Z d.radical a ⊓ Q d.radical a' : Subgroup (FreeAmalgam d.radical)) :
        Set (FreeAmalgam d.radical)) := by
  let s := fullSymmetricAction_knownSimple h e hz hn d hb
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  let t := p.walk.getVert 1
  let N := normalizer (Q d.radical t : Set (FreeAmalgam d.radical)) ⊓ stabilizer d.radical a
  have hpos : 0 < p.walk.length := p.length_eq_b ▸ replacementDistance_pos h d
  have hat : Adjacent d.radical a t := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) hpos
  have hAe : Z d.radical a' ≤ Q d.radical t := by
    apply Z_le_Q_of_dist_lt d.radical a' ((replacementGeometry h d).exists_critical a' p.end_color)
    rw [SimpleGraph.dist_comm,p.dist_end,(replacementGeometry h d).distance_constant a' p.end_color]
    change p.walk.length-1 < replacementDistance h d
    have hl : p.walk.length = replacementDistance h d := p.length_eq_b
    omega
  have hAG : Z d.radical a' ≤ stabilizer d.radical a :=
    hAe.trans (fun _ hx => hx.2 _ (adjacent_symm d.radical hat))
  have hcomm : ⁅N,Z d.radical a'⁆ ≤ centralizer (Z d.radical a : Set (FreeAmalgam d.radical)) :=
    ((commutator_mono le_rfl hAe).trans
      (mixed_relative_normalizer_commutator_knownSimple hb u him p.start_color hat)).trans
      (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
        (Z_centralizes_Q d.radical a p.start_color)))
  have hnorm : N ≤ normalizer ((⁅Z d.radical a,Z d.radical a'⁆ :
      Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)) := by
    rw [commutator_comm (Z d.radical a)]
    exact fixed_mod_central_normalizes (Z d.radical a') (Z d.radical a) N
      (hAG.trans (Z_normalized d.radical a)) (inf_le_right.trans (Z_normalized d.radical a)) hcomm
  have hfix : N ≤ centralizer ((⁅Z d.radical a,Z d.radical a'⁆ :
      Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)) :=
    hnorm.trans (normalizer_le_centralizer_of_card_two _ (small_critical_commutator_card s hc p hsmall))
  refine ⟨le_centralizer_iff.mp hfix,?_⟩
  have hn := le_inf (show N ≤ stabilizer d.radical a from inf_le_right) hfix
  rw [←small_critical_kernel_normalizer_eq_line_centralizer s hc p hsmall] at hn
  exact hn.trans inf_le_right

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowNormalizer
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
