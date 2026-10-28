module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CoreRestriction

/-!
# The exact exceptional endpoint in a noncentral radius

The natural moved plane controls every fixer. On the augmentation cover,
the same conclusion holds whenever the critical actor is not the two
independent transpositions. These controls are transported through the
literal endpoint embedding of the original characteristic replacement.
The radius chief-factor argument therefore confines any failure of
centrality to distance four, cover order thirty-two, and this specific
critical image. No point-core or Sylow condition on the radical is used.

Source: MS93 (3.3)(ii)(1), pp.866--867, and (5.2), pp.914--915.
The remaining exceptional radius argument and the distance exclusions
(5.11)--(5.12) remain with qt-e-ms-small-a6-exhaustion-large-distance.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender BinaryPermutation
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
universe u

variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}} {L R : Subgroup G}
  {h : SmallMSPair κ L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R} (s : FullSymmetricAction h e hz hn d)

/-- The two-transposition image in literal coordinates on the endpoint.
The maps of the two-core and original moved cover are retained together.
The existential body is exposed so later source arguments can use these
literal endpoint coordinates. -/
@[expose] def ExceptionalEndpoint (a : Vertex d.radical) (A : Subgroup (FreeAmalgam d.radical)) : Prop :=
  ∃ i : d.overgroup →* FreeAmalgam d.radical, Function.Injective i ∧
    i.range = stabilizer d.radical a ∧
    (pCore 2 d.overgroup).map i = Q d.radical a ∧
    (replacementMoved d).map i = U d.radical a ∧ A ≤ i.range ∧
    CFSG.Quasithin.ChapterB.Offenders.IsConjugateTo ((A.comap i).map s.projection)
      (CFSG.Quasithin.ChapterB.Offenders.disjointTranspositions 6 2)

private theorem endpoint_image_card {a : Vertex d.radical}
    (i : d.overgroup →* FreeAmalgam d.radical) (hi : Function.Injective i)
    (hiQ : (pCore 2 d.overgroup).map i = Q d.radical a)
    (A : Subgroup (FreeAmalgam d.radical)) (hA : A ≤ i.range) :
    Nat.card ((A.comap i).map s.projection) = (Q d.radical a).relIndex A := by
  rw [←relIndex_ker,s.projection_kernel,
    ←relIndex_map_map_of_injective _ _ hi,map_comap_eq_self hA,hiQ]

/-- The exceptional endpoint has exact forward image order four, in the
original two-core convention. -/
theorem exceptionalEndpoint_index {a : Vertex d.radical}
    {A : Subgroup (FreeAmalgam d.radical)} (he : ExceptionalEndpoint s a A) :
    (Q d.radical a).relIndex A = 4 := by
  obtain ⟨i,hi,_,hiQ,_,hA,g,hg⟩ := he
  rw [←endpoint_image_card s i hi hiQ A hA,hg,card_map_of_injective (MulAut.conj g).injective]
  exact CFSG.Quasithin.ChapterB.Offenders.Six.card_disjointTranspositions (2 : Fin 4)

include s in
/-- Reversing the critical pair twice shows that the original moving layer,
not just its full seed, has forward image of order at least four. -/
theorem critical_forward_moving_image_four_le (hc : DistanceTwo.CentralLayer d)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hforward : 4 ≤ (Q d.radical a').relIndex (Z d.radical a)) :
    4 ≤ (Q d.radical a').relIndex (U d.radical a) := by
  let q : CriticalPath d.radical (replacementGeometry h d) a' a :=
    CriticalPath.ofPair p.end_color (critical_reverse_pair s hc p)
  exact reverse_critical_moving_image_four_le s hc q
    (reverse_critical_image_four_le s hc (replacementDistance_pos h d) p hforward)

include s in
/-- At the exceptional endpoint the moving layer and the full critical seed
have the very same image under the literal projection. -/
theorem exceptional_endpoint_moving (hc : DistanceTwo.CentralLayer d)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (he : ExceptionalEndpoint s a' (Z d.radical a)) :
    ExceptionalEndpoint s a' (U d.radical a) := by
  have hforward := (exceptionalEndpoint_index s he).ge
  have hUfour := critical_forward_moving_image_four_le s hc p hforward
  obtain ⟨i,hi,hir,hiQ,hiU,hA,hconj⟩ := he
  have hUi : U d.radical a ≤ i.range := (DistanceEight.U_le_Z d.radical a).trans hA
  have hcard : Nat.card (((Z d.radical a).comap i).map s.projection) = 4 := by
    obtain ⟨g,hg⟩ := hconj
    rw [hg,card_map_of_injective (MulAut.conj g).injective]
    exact CFSG.Quasithin.ChapterB.Offenders.Six.card_disjointTranspositions (2 : Fin 4)
  have heq : ((U d.radical a).comap i).map s.projection =
      ((Z d.radical a).comap i).map s.projection := by
    apply eq_of_le_of_card_ge (map_mono (comap_mono (DistanceEight.U_le_Z d.radical a)))
    rw [hcard,endpoint_image_card s i hi hiQ _ hUi]
    exact hUfour
  refine ⟨i,hi,hir,hiQ,hiU,hUi,?_⟩
  rwa [heq]


include s in
theorem embedded_nonexceptional_commutator_control
    {H : Type*} [Group H] (i : d.overgroup →* H) (hi : Function.Injective i)
    (A Y : Subgroup H) [IsElementaryAbelian 2 A]
    (hA : A ≤ i.range) (hY : Y ≤ i.range)
    (hcard : 4 ≤ ((pCore 2 d.overgroup).map i).relIndex A)
    (hnot : ¬ CFSG.Quasithin.ChapterB.Offenders.IsConjugateTo
      ((A.comap i).map s.projection)
      (CFSG.Quasithin.ChapterB.Offenders.disjointTranspositions 6 2))
    (hAA : ⁅(replacementMoved d).map i,A⁆ ≤ centralizer (A : Set H))
    (hAY : ⁅(replacementMoved d).map i,A⁆ ≤ centralizer (Y : Set H)) :
    ⁅(replacementMoved d).map i,Y⁆ ≤ ⁅(replacementMoved d).map i,A⁆ := by
  let A₀ := A.comap i
  let Y₀ := Y.comap i
  let := IsElementaryAbelian.comap_of_injective (p := 2) i hi A
  have hmA : A₀.map i = A := map_comap_eq_self hA
  have hmY : Y₀.map i = Y := map_comap_eq_self hY
  have hcard₀ : 4 ≤ Nat.card (A₀.map s.projection) := by
    rw [←hmA,relIndex_map_map_of_injective _ _ hi,←s.projection_kernel,relIndex_ker] at hcard
    exact hcard
  have hfix (B : Subgroup H)
      (hc : ⁅(replacementMoved d).map i,A⁆ ≤ centralizer (B : Set H)) :
      ⁅replacementMoved d,A₀⁆ ≤ centralizer (B.comap i : Set d.overgroup) := by
    intro x hx b hb
    apply hi
    simp only [map_mul]
    apply hc
    · rw [←hmA,←map_commutator]
      exact mem_map_of_mem i hx
    · exact hb
  have hh := map_mono (f := i) (cover_commutator_control_of_nonexceptional s A₀ Y₀ hcard₀ hnot
    (hfix A hAA) (hfix Y hAY))
  rwa [map_commutator,map_commutator,hmA,hmY] at hh

include s in
/-- Every nonexceptional critical image controls the original radius
commutator for either cover order. -/
theorem critical_radius_moving_commutator_le_Z_of_nonexceptional
    (hc : DistanceTwo.CentralLayer d)
    (hb : 2 < replacementDistance h d) {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hnot : ¬ ExceptionalEndpoint s a' (Z d.radical a))
    (hcard : 4 ≤ (Q d.radical a').relIndex (Z d.radical a)) :
    ⁅V d.radical a ⊓ Q d.radical (p.walk.getVert (p.walk.length-2)),U d.radical a'⁆ ≤
      Z d.radical a := by
  have hl : 2 < p.walk.length := by rw [p.length_eq_b]; exact hb
  let t := p.walk.getVert (p.walk.length-1)
  have hct : Adjacent d.radical a' t := by
    have hh := p.walk.adj_getVert_succ (i := p.walk.length-1) (by omega)
    rw [show p.walk.length-1+1 = p.walk.length by omega,p.walk.getVert_length] at hh
    exact adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp hh)
  have ht : color d.radical t = true := by
    have hh := adjacent_color_ne d.radical hct
    rw [p.end_color] at hh
    cases he : color d.radical t <;> simp_all
  have het : Adjacent d.radical (p.walk.getVert (p.walk.length-2)) t := by
    have hh := p.walk.adj_getVert_succ (i := p.walk.length-2) (by omega)
    rw [show p.walk.length-2+1 = p.walk.length-1 by omega] at hh
    exact (cosetGraph_adj d.radical _ _).mp hh
  let Y := V d.radical a ⊓ Q d.radical (p.walk.getVert (p.walk.length-2))
  have hYt : Y ≤ Q d.radical t := inf_le_right.trans (Q_le_adjacent_h d.radical ht het)
  have hY : Y ≤ stabilizer d.radical a' := fun _ hx =>
    (hYt hx).2 _ (adjacent_symm d.radical hct)
  have hcomm : ⁅U d.radical a',Z d.radical a⁆ ≤ ⁅Z d.radical a,Z d.radical a'⁆ := by
    rw [commutator_comm]
    exact commutator_mono le_rfl (DistanceEight.U_le_Z d.radical a')
  have hRZa : ⁅Z d.radical a,Z d.radical a'⁆ ≤ Z d.radical a :=
    ((critical_Z_commutator_le_moving (h := h) p).trans inf_le_left).trans
      (DistanceEight.U_le_Z d.radical a)
  let := (replacementGeometry h d).Z_elementary (replacementDistance_pos h d) a p.start_color
  have hAA : ⁅U d.radical a',Z d.radical a⁆ ≤
      centralizer (Z d.radical a : Set (FreeAmalgam d.radical)) :=
    (hcomm.trans hRZa).trans (le_centralizer_iff_isMulCommutative.mpr inferInstance)
  have hAY : ⁅U d.radical a',Z d.radical a⁆ ≤
      centralizer (Y : Set (FreeAmalgam d.radical)) :=
    hcomm.trans (le_centralizer_iff.mp (critical_radius_intersection_centralizes (h := h) p hb))
  obtain ⟨i,hi,hir,hiQ,hiU⟩ := vertex_coordinates (h := h) hc a' p.end_color
  have hA : Z d.radical a ≤ i.range := by
    rw [hir]
    exact Z_le_stabilizer_of_dist_le a _ p.critical.1.le
  have hcontrol : ⁅U d.radical a',Y⁆ ≤ ⁅U d.radical a',Z d.radical a⁆ := by
    rw [←hiU]
    apply embedded_nonexceptional_commutator_control s i hi (Z d.radical a) Y hA
      (hY.trans_eq hir.symm)
    · rwa [hiQ]
    · intro hh
      exact hnot ⟨i,hi,hir,hiQ,hiU,hA,hh⟩
    · rwa [hiU]
    · rwa [hiU]
  rw [commutator_comm]
  exact hcontrol.trans (hcomm.trans hRZa)

include s in
/-- A failure of radius centrality forces precisely the source exceptional
actor, at distance four and on the order-thirty-two cover. -/
theorem noncentral_radius_exceptional_endpoint
    (hc : DistanceTwo.CentralLayer d) (hb : 2 < replacementDistance h d)
    (hnon : ¬ ⁅V d.radical (alpha d.radical),Q d.radical (alpha d.radical)⁆ ≤
      centralizer (V d.radical (alpha d.radical) : Set (FreeAmalgam d.radical))) :
    replacementDistance h d = 4 ∧ Nat.card (replacementMoved d) = 32 ∧
      ∃ a' : Vertex d.radical,
        ∃ _p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a',
          (Q d.radical a').relIndex (Z d.radical (alpha d.radical)) = 4 ∧
          ExceptionalEndpoint s a' (Z d.radical (alpha d.radical)) ∧
          ExceptionalEndpoint s a' (U d.radical (alpha d.radical)) := by
  have hfour := CFSG.Quasithin.ChapterC.BinaryMS.MS93.SectionFive.distance_eq_four_of_radius_commutator_not_central
    d.radical (replacementGeometry h d) hb rfl hnon
  have hcore : Nat.card (replacementMoved d) = 32 := by
    rcases moved_card s with hn | hn
    · exact (hnon (radius_commutator_central_of_natural s hc hn hb)).elim
    · exact hn
  obtain ⟨a',p,hforward⟩ := exists_base_large_critical_path (h:=h) (r:=d) hfour hnon
  have he : ExceptionalEndpoint s a' (Z d.radical (alpha d.radical)) := by
    by_contra hnot
    obtain ⟨a,haA,ha,heven⟩ := critical_moving_even_actor s hc p hforward
    apply hnon
    apply radius_commutator_central_of_residual_dichotomy (h:=h) (r:=d) hb
    apply radius_residual_dichotomy_of_index s hb s.surjective
      (U d.radical a') (Q d.radical (p.walk.getVert (p.walk.length-2)))
      ((DistanceEight.U_le_Z d.radical a').trans
        (critical_Z_le_stabilizer d.radical (replacementGeometry h d) (alpha d.radical) rfl
          (replacementDistance_pos h d) p.critical)) a ha heven haA
    · exact critical_radius_moving_commutator_le_Z_of_nonexceptional s hc hb p hnot hforward
    · exact critical_radius_image_index_le_eight_general s hc hb p
  exact ⟨hfour,hcore,a',p,exceptionalEndpoint_index s he,he,exceptional_endpoint_moving s hc p he⟩

/-- The reduction applied to the original minimum characteristic replacement;
the symmetric action and all-distance central layer are discharged. -/
theorem noncentral_radius_exceptional_endpoint_knownSimple
    {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
    {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
    {d : Replacement L R} (hb : 2 < replacementDistance h d)
    (hnon : ¬ ⁅V d.radical (alpha d.radical),Q d.radical (alpha d.radical)⁆ ≤
      centralizer (V d.radical (alpha d.radical) : Set (FreeAmalgam d.radical))) :
    replacementDistance h d = 4 ∧ Nat.card (replacementMoved d) = 32 ∧
      ∃ a' : Vertex d.radical,
        ∃ _p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a',
          (Q d.radical a').relIndex (Z d.radical (alpha d.radical)) = 4 ∧
          ExceptionalEndpoint (fullSymmetricAction_knownSimple h e hz hn d hb)
            a' (Z d.radical (alpha d.radical)) ∧
          ExceptionalEndpoint (fullSymmetricAction_knownSimple h e hz hn d hb)
            a' (U d.radical (alpha d.radical)) :=
  noncentral_radius_exceptional_endpoint (fullSymmetricAction_knownSimple h e hz hn d hb)
    (DistanceTwo.centralLayer_knownSimple G L R h e hz hn d) hb hnon

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
