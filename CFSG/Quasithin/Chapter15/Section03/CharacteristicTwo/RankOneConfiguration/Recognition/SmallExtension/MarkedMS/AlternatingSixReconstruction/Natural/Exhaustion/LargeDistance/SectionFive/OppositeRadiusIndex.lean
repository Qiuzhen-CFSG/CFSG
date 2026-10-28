module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.ChiefFactor

/-!
# Strict radius indices at opposite critical endpoints

The full radius has residual movement both in its initial Z-seed and beyond
that seed. An actor with an even involution in the marked S₆ image therefore
has fixed index greater than eight: otherwise the chief-factor budget would
allow only one noncentral factor, and its residual dichotomy would kill one
of these two movements.

For a critical pair whose seed image has order at least four, the proved
reverse-index estimate supplies such an actor. Its opposite kernel centralizes
the seed, so the same strict bound holds for the actual radius index. Graph
conjugation and reversal give the estimate at both endpoints. In particular,
a small opposite-radius index forces the critical seed image to have order
two. The original-replacement applications discharge the full symmetric
marking and central-layer premises.

This proves the large-image case of the strict opposite-endpoint estimates
used in MS93 (5.11)(1), printed pp.923--924. It holds already for b > 2,
retains both central covers and all radical images, and does not replace an
opposite endpoint by the vertex two steps earlier. The selected index-two
paths, their noncentral R₄/R₆, and the selected natural section in (5.12)
remain with qt-e-ms-small-a6-exhaustion-large-distance. The final unconditional
reconstruction remains with qt-e-ms-small-a6-reconstruction.
-/

public section
open Subgroup
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}} {L R : Subgroup G}
  {h : SmallMSPair κ L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R} (s : FullSymmetricAction h e hz hn d)


include s in
private theorem radiusSeed_movement_ne_bot (hc : DistanceTwo.CentralLayer d) :
    ⁅radiusSeed d,replacementComponent d⁆ ≠ ⊥ := by
  intro hz0
  have hmap := congrArg (Subgroup.map (embedM d.radical)) hz0
  rw [map_commutator,Subgroup.map_bot] at hmap
  have hZ : (radiusSeed d).map (embedM d.radical) = Z d.radical (alpha d.radical) :=
    map_comap_eq_self ((Z_le_stabilizer d.radical _).trans_eq
      (stabilizer_m_base d.radical))
  have hL : (replacementComponent d).map (embedM d.radical) =
      Ltilde d.radical (alpha d.radical) := by
    rw [Ltilde_alpha]
    exact congrArg (Subgroup.map (embedM d.radical)) (replacement_residual h d).symm
  rw [hZ,hL] at hmap
  change U d.radical (alpha d.radical) = ⊥ at hmap
  have hcard := graph_U_card s hc
  rw [hmap,card_bot] at hcard
  omega

include s in
/-- The full radius has two distinct sources of noncentral residual movement,
so an even involution in the actor image forces fixed index greater than eight. -/
theorem radius_even_actor_fixed_index_gt_eight
    (hc : DistanceTwo.CentralLayer d) (hb : 2 < replacementDistance h d)
    (A : Subgroup d.overgroup) (a : Equiv.Perm (Fin 6))
    (ha : orderOf a = 2) (heven : a ∈ alternatingGroup (Fin 6))
    (haA : a ∈ A.map s.projection) :
    8 < (centralizer (A : Set d.overgroup)).relIndex (radiusPreimage d) := by
  by_contra! hsmall
  have hV : radiusPreimage d ≤ s.projection.ker := by
    rw [s.projection_kernel]
    have hh := comap_mono (f := embedM d.radical) (V_le_Q d.radical
      (geometry := replacementGeometry h d) (a := alpha d.radical) rfl hb)
    rwa [Q_alpha_comap d.radical (replacement_radical_isPGroup h d)
      (replacement_core_le_radical h d)] at hh
  have hp : IsPGroup 2 s.projection.ker := by
    rw [s.projection_kernel]
    exact pCore_isPGroup
  have hfixed : (centralizerModulo (radiusPreimage d) A ⊥).relIndex
      (radiusPreimage d) ≤ 8 := by
    apply (NoncentralChiefRefinement.SymmetricSixBudget.centralizerModulo_relIndex_le_of_commutator
      (radiusPreimage d) A ⊥ (centralizer (A : Set d.overgroup)) ?_).trans hsmall
    exact (commutator_mono inf_le_right le_rfl).trans
      (commutator_eq_bot_iff_le_centralizer.mpr le_rfl).le
  have hh := NoncentralChiefRefinement.SymmetricSixBudget.residual_dichotomy_modulo
    s.projection s.surjective hp (radiusPreimage d) ⊥ bot_le hV A a ha heven haA
    hfixed (radiusSeed d) radiusSeed_le_radiusPreimage
  rw [replacement_residual h d,sup_bot_eq,le_bot_iff] at hh
  rcases hh with hf | hm
  · exact radiusSeed_movement_ne_bot s hc hf
  · exact radius_moving_not_le_seed s hc hb hm

include s in
private theorem critical_radius_index_gt_eight_base
    (hc : DistanceTwo.CentralLayer d) (hb : 2 < replacementDistance h d)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hforward : 4 ≤ (Q d.radical a').relIndex (Z d.radical (alpha d.radical))) :
    8 < (Q d.radical a').relIndex (V d.radical (alpha d.radical)) := by
  obtain ⟨a,haA,ha,heven⟩ := exists_even_involution_reverse_critical_image s hc
    (replacementDistance_pos h d) p hforward
  let A := (Z d.radical a').comap (embedM d.radical)
  let K := (Q d.radical a').comap (embedM d.radical)
  have hKA : K ≤ centralizer (A : Set d.overgroup) := by
    intro x hx y hy
    apply embedM_injective d.radical
    simp only [map_mul]
    exact (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q d.radical a' p.end_color))) hx _ hy
  have hi := (radius_even_actor_fixed_index_gt_eight s hc hb A a ha heven haA).trans_le
    (relIndex_le_of_le_left hKA index_ne_zero_of_finite)
  rw [relIndex_comap,radius_comap_map (h := h) hb] at hi
  exact hi


include s in
/-- A large critical seed image forces a strict radius index at the other
endpoint, with the original starting radius retained. -/
theorem critical_radius_index_gt_eight
    (hc : DistanceTwo.CentralLayer d) (hb : 2 < replacementDistance h d)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hforward : 4 ≤ (Q d.radical a').relIndex (Z d.radical a)) :
    8 < (Q d.radical a').relIndex (V d.radical a) := by
  obtain ⟨g,hg⟩ := exists_mVertex_of_color d.radical p.start_color
  have hbase : act d.radical g⁻¹ a = alpha d.radical := by
    rw [hg,act_mVertex]
    simp only [mul_inv_cancel]
    rfl
  have pc := p.act g⁻¹
  rw [hbase] at pc
  have hf : 4 ≤ (Q d.radical (act d.radical g⁻¹ a')).relIndex
      (Z d.radical (alpha d.radical)) := by
    rw [←hbase,Q_act,Z_act,relIndex_map_map_of_injective _ _
      (MulAut.conj (g⁻¹)⁻¹).injective]
    exact hforward
  have hi := critical_radius_index_gt_eight_base s hc hb pc hf
  rw [←hbase,Q_act,V_act,relIndex_map_map_of_injective _ _
    (MulAut.conj (g⁻¹)⁻¹).injective] at hi
  exact hi

include s in
/-- Reversal gives the strict bound for the opposite radius itself. -/
theorem opposite_radius_index_gt_eight
    (hc : DistanceTwo.CentralLayer d) (hb : 2 < replacementDistance h d)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hforward : 4 ≤ (Q d.radical a').relIndex (Z d.radical a)) :
    8 < (Q d.radical a).relIndex (V d.radical a') := by
  let q := CriticalPath.ofPair (geometry := replacementGeometry h d) p.end_color (critical_reverse_pair s hc p)
  exact critical_radius_index_gt_eight s hc hb q
    (reverse_critical_image_four_le s hc (replacementDistance_pos h d) p hforward)

include s in
/-- The large-image cases are excluded by a small opposite-radius index;
criticality and the two-group order constraint leave exactly index two. -/
theorem critical_index_two_of_small_opposite_radius
    (hc : DistanceTwo.CentralLayer d) (hb : 2 < replacementDistance h d)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hsmall : (Q d.radical a).relIndex (V d.radical a') ≤ 8) :
    (Q d.radical a').relIndex (Z d.radical a) = 2 := by
  have hl : (Q d.radical a').relIndex (Z d.radical a) < 4 := by
    by_contra! hlarge
    exact (not_lt_of_ge hsmall) (opposite_radius_index_gt_eight s hc hb p hlarge)
  let := (replacementGeometry h d).Z_elementary (replacementDistance_pos h d) a p.start_color
  let := finite_stabilizer d.radical a
  let : Finite (Z d.radical a) := Finite.of_injective
    (inclusion (Z_le_stabilizer d.radical a)) (inclusion_injective _)
  obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup 2 (Z d.radical a)).index
    ((Q d.radical a').subgroupOf (Z d.radical a))
  change (Q d.radical a').relIndex (Z d.radical a) = 2^n at hn
  have hne : (Q d.radical a').relIndex (Z d.radical a) ≠ 1 := by
    intro hi
    exact p.critical.2 (relIndex_eq_one.mp hi)
  have hn2 : n < 2 := by
    by_contra! hn2
    have hpow := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hn2
    rw [←hn] at hpow
    omega
  have hn1 : n = 1 := by
    by_contra hh
    have hz : n = 0 := by omega
    rw [hz] at hn
    exact hne hn
  simpa only [hn1,pow_one] using hn

/-- The strict opposite-endpoint estimate on the original characteristic
replacement, with both earlier source producers discharged. -/
theorem opposite_radius_index_gt_eight_knownSimple
    {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
    {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
    {d : Replacement L R} (hb : 2 < replacementDistance h d)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hforward : 4 ≤ (Q d.radical a').relIndex (Z d.radical a)) :
    8 < (Q d.radical a).relIndex (V d.radical a') :=
  opposite_radius_index_gt_eight (fullSymmetricAction_knownSimple h e hz hn d hb)
    (DistanceTwo.centralLayer_knownSimple G L R h e hz hn d) hb p hforward

/-- Only the index-two critical-seed case can survive a small opposite radius. -/
theorem critical_index_two_of_small_opposite_radius_knownSimple
    {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
    {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
    {d : Replacement L R} (hb : 2 < replacementDistance h d)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hsmall : (Q d.radical a).relIndex (V d.radical a') ≤ 8) :
    (Q d.radical a').relIndex (Z d.radical a) = 2 :=
  critical_index_two_of_small_opposite_radius
    (fullSymmetricAction_knownSimple h e hz hn d hb)
    (DistanceTwo.centralLayer_knownSimple G L R h e hz hn d) hb p hsmall

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
