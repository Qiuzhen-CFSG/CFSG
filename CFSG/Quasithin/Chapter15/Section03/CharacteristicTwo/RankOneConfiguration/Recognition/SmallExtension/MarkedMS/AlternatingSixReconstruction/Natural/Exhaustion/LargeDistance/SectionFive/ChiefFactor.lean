module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.RestrictedActor

/-!
# The unique noncentral chief factor of the actual radius quotient

For a critical pair whose forward seed image has order at least four, the
actual reverse even actor and the radius index bound imply that V/Z has at
most one noncentral chief factor. Here V and Z are pulled back through the
original free-amalgam embedding, and V/Z is realized inside the literal
quotient of the replacement group by Z. No elementary-abelian or splitting
assumption is imposed on this quotient.

The count is nonzero: if the residual movement of V lay in Z, the abelian
edge radius would equal V. Both adjacent vertex groups would normalize it,
contradicting the characteristic condition and the nonzero moved cover.
Thus every chief series has exactly one noncentral factor. Refining through
an arbitrary normal subgroup gives the fixed-or-covering residual alternative
used in the large-image branch of (5.12). For the two-kernel commutator,
the covering alternative would again force equality with the edge radius
by nilpotent saturation. Thus its residual commutator lies in the full
Z-seed. This last conclusion is also transported back to the literal graph
commutators. The known-simple applications
discharge the earlier action and central-layer premises for the original
minimum characteristic replacement, without a Sylow assumption.

This completes the binary S₆ form of (5.2)(i), including its noncentrality
clause, for both moved
cover orders and every radical image. The shifted-path proof of (5.11), and
all cases of (5.12), remain with qt-e-ms-small-a6-exhaustion-large-distance.
Source: Meierfrankenfeld--Stellmacher (1993), (5.2)(i), printed p.914,
and its use in (5.12)(2), pp.925--926; the noncentrality argument uses
(2.1)(iii), p.855.
-/

@[expose] public noncomputable section
open Subgroup NoncentralChiefRefinement
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.NaturalStructure.Exclusion
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}} {L R : Subgroup G}
  {h : SmallMSPair κ L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R} (s : FullSymmetricAction h e hz hn d)

/-- The full radius in the original replacement group, through `embedM`. -/
abbrev radiusPreimage (d : Replacement L R) : Subgroup d.overgroup :=
  (V d.radical (alpha d.radical)).comap (embedM d.radical)

/-- The full initial Z-seed in the same replacement group. -/
abbrev radiusSeed (d : Replacement L R) : Subgroup d.overgroup :=
  (Z d.radical (alpha d.radical)).comap (embedM d.radical)

instance radiusPreimage_normal (d : Replacement L R) : (radiusPreimage d).Normal :=
  radius_comap_normal

instance radiusSeed_normal (d : Replacement L R) : (radiusSeed d).Normal :=
  CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSeed.Z_comap_normal d.radical

/-- The actual radius image in the quotient by the full Z-seed. -/
def radiusQuotient (d : Replacement L R) : Subgroup (d.overgroup ⧸ radiusSeed d) :=
  (radiusPreimage d).map (QuotientGroup.mk' (radiusSeed d))

instance radiusQuotient_normal (d : Replacement L R) : (radiusQuotient d).Normal :=
  Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)

omit [Finite G] in
theorem radiusSeed_le_radiusPreimage : radiusSeed d ≤ radiusPreimage d :=
  comap_mono (Z_le_VBall d.radical (alpha d.radical) 2)

omit [Finite G] in
private theorem radiusSeed_le_edge_preimage :
    radiusSeed d ≤ (V d.radical (beta d.radical)).comap (embedM d.radical) := by
  apply comap_mono
  apply le_iSup_of_le (alpha d.radical)
  apply le_iSup_of_le (show (cosetGraph d.radical).dist (alpha d.radical)
    (beta d.radical) ≤ 2 from ?_)
  · exact le_rfl
  · exact (SimpleGraph.dist_eq_one_iff_adj.mpr
      ((cosetGraph_adj d.radical (alpha d.radical) (beta d.radical)).mpr
        (base_adjacent d.radical))).le.trans (by decide)

include s in
private theorem radius_not_le_edge_preimage (hc : DistanceTwo.CentralLayer d)
    (hb : 2 < replacementDistance h d) :
    ¬ radiusPreimage d ≤ (V d.radical (beta d.radical)).comap (embedM d.radical) := by
  intro hVE
  have hVeq : V d.radical (alpha d.radical) = V d.radical (beta d.radical) := by
    apply le_antisymm _ (edge_radius_le_radius rfl (base_adjacent d.radical))
    have hh := map_mono (f := embedM d.radical) hVE
    rwa [radius_comap_map (h := h) hb,edge_radius_comap_map (h := h) hb] at hh
  have hVQ : V d.radical (alpha d.radical) ≤ Q d.radical (alpha d.radical) :=
    V_le_Q d.radical rfl hb
  have hbot := no_common_normal_at_edge d.radical (replacement_characteristic h d)
    (alpha d.radical) (beta d.radical) rfl (base_adjacent d.radical)
    (V d.radical (alpha d.radical))
    (le_inf (hVQ.trans (fun _ hx => hx.1))
      (hVQ.trans (fun _ hx => hx.2 _ (base_adjacent d.radical))))
    (normal_subgroupOf_of_le_normalizer (V_normalized (alpha d.radical)))
    (by rw [hVeq]; exact normal_subgroupOf_of_le_normalizer (V_normalized (beta d.radical)))
  have hU : U d.radical (alpha d.radical) = ⊥ := le_bot_iff.mp
    (((DistanceEight.U_le_Z d.radical _).trans (Z_le_VBall d.radical _ 2)).trans hbot.le)
  have hcard := graph_U_card s hc
  rw [hU,card_bot] at hcard
  omega

include s in
/-- Residual movement of the full radius cannot be confined to the initial seed. -/
theorem radius_moving_not_le_seed (hc : DistanceTwo.CentralLayer d)
    (hb : 2 < replacementDistance h d) :
    ¬ ⁅radiusPreimage d,replacementComponent d⁆ ≤ radiusSeed d := by
  intro hsmall
  apply radius_not_le_edge_preimage s hc hb
  exact (radius_comap_le_edge_sup_commutator (h := h) hb).trans
    (sup_le le_rfl (hsmall.trans radiusSeed_le_edge_preimage))

include s in
/-- A controlled reverse even actor for either central cover, in the original
marked symmetric quotient. -/
theorem critical_radius_even_actor
    (hc : DistanceTwo.CentralLayer d) (hb : 2 < replacementDistance h d)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hforward : 4 ≤ (Q d.radical a').relIndex (Z d.radical (alpha d.radical))) :
    ∃ W : Subgroup (FreeAmalgam d.radical), W ≤ U d.radical a' ∧
      ⁅V d.radical (alpha d.radical) ⊓ Q d.radical (p.walk.getVert (p.walk.length-2)),W⁆ ≤
        Z d.radical (alpha d.radical) ∧
      ∃ a ∈ (W.comap (embedM d.radical)).map s.projection,
        orderOf a = 2 ∧ a ∈ alternatingGroup (Fin 6) := by
  rcases moved_card s with hnat | hcore
  · obtain ⟨a,ha,ha2,heven⟩ := critical_moving_even_actor s hc p hforward
    exact ⟨U d.radical a',le_rfl,
      critical_radius_moving_commutator_le_Z_of_natural s hc hnat hb p hforward,
      a,ha,ha2,heven⟩
  · exact critical_radius_restricted_even_actor s hc hcore hb p hforward

include s in
/-- The literal radius quotient has nontrivial two-residual action. -/
theorem radiusQuotient_moving_ne_bot (hc : DistanceTwo.CentralLayer d)
    (hb : 2 < replacementDistance h d) :
    ⁅radiusQuotient d,pResidual 2 (d.overgroup ⧸ radiusSeed d)⁆ ≠ ⊥ := by
  intro hzq
  apply radius_moving_not_le_seed s hc hb
  let π := QuotientGroup.mk' (radiusSeed d)
  have hm : (⁅radiusPreimage d,replacementComponent d⁆).map π = ⊥ := by
    rw [map_commutator,show replacementComponent d = pResidual 2 d.overgroup from (replacement_residual h d).symm,map_pResidual_quotient]
    exact hzq
  have hh := (Subgroup.map_eq_bot_iff _).mp hm
  simpa only [π,QuotientGroup.ker_mk'] using hh

include s in
/-- The binary S₆ form of MS93 (5.2)(i): every chief series of the actual radius
quotient has exactly one noncentral factor under the source critical-index hypothesis. -/
theorem critical_radius_unique_noncentral_factor
    (hc : DistanceTwo.CentralLayer d) (hb : 2 < replacementDistance h d)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hforward : 4 ≤ (Q d.radical a').relIndex (Z d.radical (alpha d.radical)))
    (c : SeriesOn (radiusQuotient d)) : c.noncentralCount = 1 := by
  obtain ⟨W,hWU,hcomm,a,haW,ha,heven⟩ := critical_radius_even_actor s hc hb p hforward
  let f := embedM d.radical
  let A := W.comap f
  let K := (Q d.radical (p.walk.getVert (p.walk.length-2))).comap f
  let π := QuotientGroup.mk' (radiusSeed d)
  have hV : radiusPreimage d ≤ s.projection.ker := by
    rw [s.projection_kernel]
    have hh := comap_mono (f := f) (V_le_Q d.radical
      (geometry := replacementGeometry h d) (a := alpha d.radical) rfl hb)
    rwa [Q_alpha_comap d.radical (replacement_radical_isPGroup h d)
      (replacement_core_le_radical h d)] at hh
  have hZ := radiusSeed_le_radiusPreimage (d := d)
  have hWrange : W ≤ f.range := by
    change W ≤ Mbar d.radical
    rw [←stabilizer_m_base]
    exact (hWU.trans (DistanceEight.U_le_Z d.radical a')).trans
      (critical_Z_le_stabilizer d.radical (replacementGeometry h d) (alpha d.radical) rfl
        (replacementDistance_pos h d) p.critical)
  have hWmap : A.map f = W := map_comap_eq_self hWrange
  have hcomm₀ : ⁅radiusPreimage d ⊓ K,A⁆ ≤ radiusSeed d := by
    apply (map_le_map_iff_of_injective (embedM_injective d.radical)).mp
    rw [map_commutator,Subgroup.map_inf _ _ _ (embedM_injective d.radical),
      radius_comap_map (h := h) hb,hWmap]
    exact ((commutator_mono (inf_le_inf_left _ (map_comap_le _ _)) le_rfl).trans
      hcomm).trans (map_comap_eq_self ((Z_le_stabilizer d.radical _).trans_eq
        (stabilizer_m_base d.radical))).ge
  have hindex : K.relIndex (radiusPreimage d) ≤ 8 := by
    rw [relIndex_comap,radius_comap_map (h := h) hb]
    exact critical_radius_image_index_le_eight_general s hc hb p
  have hfixed := (SymmetricSixBudget.centralizerModulo_relIndex_le_of_commutator
    (radiusPreimage d) A (radiusSeed d) K hcomm₀).trans hindex
  let q := QuotientGroup.lift (radiusSeed d) s.projection (hZ.trans hV)
  have hq : Function.Surjective q :=
    QuotientGroup.lift_surjective_of_surjective _ _ s.surjective _
  have hker : q.ker = s.projection.ker.map π := QuotientGroup.ker_lift _ _ _
  have htwo : IsPGroup 2 s.projection.ker := by
    rw [s.projection_kernel]
    exact pCore_isPGroup
  have hqtwo : IsPGroup 2 q.ker := by rw [hker]; exact htwo.map π
  have hVq : radiusQuotient d ≤ q.ker := by rw [hker]; exact map_mono hV
  have himage : (A.map π).map q = A.map s.projection := by rw [map_map]; rfl
  have hfixedq : (centralizer (A.map π : Set (d.overgroup ⧸ radiusSeed d))).relIndex
      (radiusQuotient d) ≤ 8 := by
    rwa [SymmetricSixBudget.centralizerModulo_relIndex_eq] at hfixed
  have hcount := SymmetricSixBudget.noncentralCount_le_one_of_le_ker q hq hqtwo
    (radiusQuotient d) hVq (A.map π) a ha heven (himage.symm ▸ haW) hfixedq c
  have hpos : c.noncentralCount ≠ 0 := by
    intro hzero
    have hh := c.series.residual_commutator_le_head_of_central_steps
      (show IsPGroup 2 c.series.last.val by rw [c.last_eq]; exact hqtwo.to_le hVq)
      (c.noncentralCount_eq_zero_iff.mp hzero)
    rw [c.last_eq,c.head_eq] at hh
    exact radiusQuotient_moving_ne_bot s hc hb (le_bot_iff.mp hh)
  omega

include s in
/-- Apply the unique chief factor to an arbitrary subgroup normal in the
replacement vertex group, retaining the actual commutators and seed. -/
theorem critical_radius_normal_subgroup_dichotomy
    (hc : DistanceTwo.CentralLayer d) (hb : 2 < replacementDistance h d)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hforward : 4 ≤ (Q d.radical a').relIndex (Z d.radical (alpha d.radical)))
    (Y : Subgroup d.overgroup) [Y.Normal] (hY : Y ≤ radiusPreimage d) :
    ⁅Y,replacementComponent d⁆ ≤ radiusSeed d ∨
      ⁅radiusPreimage d,replacementComponent d⁆ ≤ Y ⊔ radiusSeed d := by
  let π := QuotientGroup.mk' (radiusSeed d)
  let : (Y.map π).Normal := Subgroup.Normal.map inferInstance π (QuotientGroup.mk'_surjective _)
  obtain ⟨c⟩ := SeriesOn.exists_series (radiusQuotient d)
  have hc1 := critical_radius_unique_noncentral_factor s hc hb p hforward c
  have hV : radiusPreimage d ≤ pCore 2 d.overgroup := by
    have hh := comap_mono (f := embedM d.radical) (V_le_Q d.radical
      (geometry := replacementGeometry h d) (a := alpha d.radical) rfl hb)
    rwa [Q_alpha_comap d.radical (replacement_radical_isPGroup h d)
      (replacement_core_le_radical h d)] at hh
  have htwo : IsPGroup 2 (radiusQuotient d) :=
    ((pCore_isPGroup (p := 2) (G := d.overgroup)).to_le hV).map π
  have hres : (replacementComponent d).map π = pResidual 2 (d.overgroup ⧸ radiusSeed d) := by
    rw [show replacementComponent d = pResidual 2 d.overgroup from (replacement_residual h d).symm,map_pResidual_quotient]
  rcases c.residual_dichotomy_of_count_one htwo hc1 (Y.map π) (map_mono hY) with hfixed | hcover
  · left
    have hh : (⁅Y,replacementComponent d⁆).map π = ⊥ := by
      rwa [map_commutator,hres]
    have hk := (Subgroup.map_eq_bot_iff _).mp hh
    simpa only [π,QuotientGroup.ker_mk'] using hk
  · right
    have hh : (⁅radiusPreimage d,replacementComponent d⁆).map π ≤ Y.map π := by
      rwa [map_commutator,hres]
    have hk := (map_le_iff_le_comap).mp hh
    simpa only [comap_map_eq,π,QuotientGroup.ker_mk'] using hk

include s in
/-- The radius has genuine residual movement beyond its seed at every
component vertex, before any choice of a critical pair. -/
theorem radius_moving_not_le_Z (hc : DistanceTwo.CentralLayer d)
    (hb : 2 < replacementDistance h d) (a : Vertex d.radical)
    (ha : color d.radical a = false) : ¬ Vcirc d.radical a ≤ Z d.radical a := by
  have hbase : ¬ Vcirc d.radical (alpha d.radical) ≤ Z d.radical (alpha d.radical) := by
    intro hsmall
    apply radius_moving_not_le_seed s hc hb
    apply (map_le_map_iff_of_injective (embedM_injective d.radical)).mp
    have hL : (replacementComponent d).map (embedM d.radical) = Ltilde d.radical (alpha d.radical) := by
      rw [Ltilde_alpha]
      exact congrArg (Subgroup.map (embedM d.radical)) (replacement_residual h d).symm
    have hZ : (radiusSeed d).map (embedM d.radical) = Z d.radical (alpha d.radical) :=
      map_comap_eq_self ((Z_le_stabilizer d.radical _).trans_eq (stabilizer_m_base d.radical))
    rwa [map_commutator,radius_comap_map (h := h) hb,hL,hZ]
  obtain ⟨g,rfl⟩ := exists_mVertex_of_color d.radical ha
  have hV : Vcirc d.radical (mVertex d.radical g) =
      (Vcirc d.radical (alpha d.radical)).map (MulAut.conj g⁻¹).toMonoidHom := by
    simpa only [alpha,act_mVertex,one_mul] using Vcirc_act d.radical g (alpha d.radical)
  have hZ : Z d.radical (mVertex d.radical g) =
      (Z d.radical (alpha d.radical)).map (MulAut.conj g⁻¹).toMonoidHom := by
    simpa only [alpha,act_mVertex,one_mul] using Z_act d.radical g (alpha d.radical)
  rw [hV,hZ,map_le_map_iff_of_injective (MulAut.conj g⁻¹).injective]
  exact hbase

/-- Source (5.2)(i) on every original characteristic replacement. The full
symmetric action and central-layer identification are supplied by their
proved known-simple constructors. -/
theorem critical_radius_unique_noncentral_factor_knownSimple
    {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
    {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
    {d : Replacement L R} (hb : 2 < replacementDistance h d)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hforward : 4 ≤ (Q d.radical a').relIndex (Z d.radical (alpha d.radical)))
    (c : SeriesOn (radiusQuotient d)) : c.noncentralCount = 1 :=
  critical_radius_unique_noncentral_factor (fullSymmetricAction_knownSimple h e hz hn d hb)
    (DistanceTwo.centralLayer_knownSimple G L R h e hz hn d) hb p hforward c

/-- The unique-factor consequence used in (5.12): every actual normal
subgroup of the radius either has fixed residual action modulo the seed or
contains all radius movement modulo that seed. No chief-factor or actor
premise remains. The critical-index hypothesis is the source's own case
split, which the terminal distance-four argument must handle. -/
theorem critical_radius_normal_subgroup_dichotomy_knownSimple
    {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
    {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
    {d : Replacement L R} (hb : 2 < replacementDistance h d)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hforward : 4 ≤ (Q d.radical a').relIndex (Z d.radical (alpha d.radical)))
    (Y : Subgroup d.overgroup) [Y.Normal] (hY : Y ≤ radiusPreimage d) :
    ⁅Y,replacementComponent d⁆ ≤ radiusSeed d ∨
      ⁅radiusPreimage d,replacementComponent d⁆ ≤ Y ⊔ radiusSeed d :=
  critical_radius_normal_subgroup_dichotomy (fullSymmetricAction_knownSimple h e hz hn d hb)
    (DistanceTwo.centralLayer_knownSimple G L R h e hz hn d) hb p hforward Y hY

include s in
/-- In the actual source radius the covering alternative for its two-kernel
commutator is impossible: nilpotent saturation would identify the full
radius with its edge radius. -/
theorem critical_radius_kernel_residual_le_seed
    (hc : DistanceTwo.CentralLayer d) (hb : 2 < replacementDistance h d)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hforward : 4 ≤ (Q d.radical a').relIndex (Z d.radical (alpha d.radical))) :
    ⁅⁅radiusPreimage d,pCore 2 d.overgroup⁆,replacementComponent d⁆ ≤ radiusSeed d := by
  rcases critical_radius_normal_subgroup_dichotomy s hc hb p hforward
      ⁅radiusPreimage d,pCore 2 d.overgroup⁆ (commutator_le_left _ _) with hfixed | hcover
  · exact hfixed
  · exfalso
    let E := (V d.radical (beta d.radical)).comap (embedM d.radical)
    have hV : radiusPreimage d ≤ pCore 2 d.overgroup := by
      have hh := comap_mono (f := embedM d.radical) (V_le_Q d.radical
        (geometry := replacementGeometry h d) (a := alpha d.radical) rfl hb)
      rwa [Q_alpha_comap d.radical (replacement_radical_isPGroup h d)
        (replacement_core_le_radical h d)] at hh
    have hEV : E ≤ radiusPreimage d := comap_mono
      (edge_radius_le_radius rfl (base_adjacent d.radical))
    have hbound : radiusPreimage d ≤ E ⊔ ⁅radiusPreimage d,pCore 2 d.overgroup⁆ := by
      apply (radius_comap_le_edge_sup_commutator (h := h) hb).trans
      apply sup_le le_sup_left
      exact hcover.trans (sup_le le_sup_right (radiusSeed_le_edge_preimage.trans le_sup_left))
    have hVE : radiusPreimage d ≤ E :=
      le_of_le_sup_commutator_of_isNilpotent (pCore 2 d.overgroup) (radiusPreimage d) E
        (pCore 2 d.overgroup) (pCore_isPGroup (p := 2) (G := d.overgroup)).isNilpotent
        hV (hEV.trans hV) le_rfl
        ((replacement_core_le_radical h d).trans (radical_normalizes_edge_radius_comap (r := d))) hbound
    exact radius_not_le_edge_preimage s hc hb hVE

include s in
/-- The strengthened large-image conclusion on the literal graph radius,
with the original component and kernel embeddings. -/
theorem critical_radius_kernel_residual_le_Z
    (hc : DistanceTwo.CentralLayer d) (hb : 2 < replacementDistance h d)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hforward : 4 ≤ (Q d.radical a').relIndex (Z d.radical (alpha d.radical))) :
    ⁅⁅V d.radical (alpha d.radical),Q d.radical (alpha d.radical)⁆,
      Ltilde d.radical (alpha d.radical)⁆ ≤ Z d.radical (alpha d.radical) := by
  have hh := map_mono (f := embedM d.radical)
    (critical_radius_kernel_residual_le_seed s hc hb p hforward)
  have hL : (replacementComponent d).map (embedM d.radical) = Ltilde d.radical (alpha d.radical) := by
    rw [Ltilde_alpha]
    exact congrArg (Subgroup.map (embedM d.radical)) (replacement_residual h d).symm
  have hZ : (radiusSeed d).map (embedM d.radical) = Z d.radical (alpha d.radical) :=
    map_comap_eq_self ((Z_le_stabilizer d.radical _).trans_eq (stabilizer_m_base d.radical))
  rwa [map_commutator,map_commutator,radius_comap_map (h := h) hb,
    ←Q_alpha d.radical (replacement_radical_isPGroup h d) (replacement_core_le_radical h d),hL,hZ] at hh

/-- The original minimum characteristic replacement supplies the earlier
source inputs of the kernel-residual bound in the large-image case. -/
theorem critical_radius_kernel_residual_le_Z_knownSimple
    {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
    {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
    {d : Replacement L R} (hb : 2 < replacementDistance h d)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hforward : 4 ≤ (Q d.radical a').relIndex (Z d.radical (alpha d.radical))) :
    ⁅⁅V d.radical (alpha d.radical),Q d.radical (alpha d.radical)⁆,
      Ltilde d.radical (alpha d.radical)⁆ ≤ Z d.radical (alpha d.radical) :=
  critical_radius_kernel_residual_le_Z (fullSymmetricAction_knownSimple h e hz hn d hb)
    (DistanceTwo.centralLayer_knownSimple G L R h e hz hn d) hb p hforward

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
