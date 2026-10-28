module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.RestrictedSeed
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.ControlledBackward
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowActor
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CubePaths

/-!
# Full endpoint restrictions on the generating backward path

Join the exact full endpoint restriction to the controlled even subactor.
Both lie in the same endpoint seed; their commutators on the whole radius
intersection lie in the original critical commutator. The construction keeps
this sharper bound from the two cover calculations.
Their join retains the last-edge attachment, index at most two, the entire
critical commutator, and a marked even involution. Choose the generating
relative edge normalizer using that same join. The relative holomorph then
constructs a compatible backward path with its original slice index.

The commutator of the full backward seed kernel joined with the starting
seed is exactly the original critical commutator. This gives normalization
by the same endpoint restriction. Its entire critical commutator is fixed by
the restriction. For a small backward image, normalization by the other
generator is obstructed by the strict slice. In the nonsylow branch the
edge image is abelian and supplies that normalization, so the same backward
image is large.

This supplies compatible full-seed data in the large-image branch of MS93
(5.12)(1)--(2). The terminal contradiction and chosen full-seed slice bound
remain separate mathematical obligations. Both cover orders, all radical
images and the literal natural characteristic replacement are retained.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (5.2)(i), (5.12)(1)--(3), printed pp.913--914,924--927,
and the relative edge holomorph of Section 7, pp.932--933.

The internal imports of SylowActor and CubePaths deliberately reuse their
selectors with this prescribed full endpoint restriction. They preserve the
existing public boundaries. The two private cover arguments sharpen the
bounds in NaturalRadius and RestrictedActor without editing those shared
modules or changing their public interfaces.
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
private theorem natural_radius_exact_control
    (hc : DistanceTwo.CentralLayer d) (hnat : Nat.card (replacementMoved d) = 16)
    (hb : 2 < replacementDistance h d) {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hcard : 4 ≤ (Q d.radical a').relIndex (Z d.radical a)) :
    ⁅V d.radical a ⊓ Q d.radical (p.walk.getVert (p.walk.length-2)),U d.radical a'⁆ ≤
      ⁅Z d.radical a,Z d.radical a'⁆ := by
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
    apply embedded_natural_commutator_control s hnat i hi (Z d.radical a) Y hA
      (hY.trans_eq hir.symm)
    · rwa [hiQ]
    · rwa [hiU]
    · rwa [hiU]
  rw [commutator_comm]
  exact hcontrol.trans hcomm

include s in
private theorem core_radius_exact_even_control
    (hc : DistanceTwo.CentralLayer d) (hcore : Nat.card (replacementMoved d) = 32)
    (hb : 2 < replacementDistance h d) {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hforward : 4 ≤ (Q d.radical a').relIndex (Z d.radical (alpha d.radical))) :
    ∃ W : Subgroup (FreeAmalgam d.radical), W ≤ U d.radical a' ∧
      ⁅V d.radical (alpha d.radical) ⊓ Q d.radical (p.walk.getVert (p.walk.length-2)),W⁆ ≤
        ⁅Z d.radical (alpha d.radical),Z d.radical a'⁆ ∧
      ∃ a ∈ (W.comap (embedM d.radical)).map s.projection,
        orderOf a = 2 ∧ a ∈ alternatingGroup (Fin 6) := by
  let a := alpha d.radical
  have hl : 2 < p.walk.length := by rw [p.length_eq_b]; exact hb
  let t := p.walk.getVert (p.walk.length-1)
  have hct : Adjacent d.radical a' t := by
    have hh := p.walk.adj_getVert_succ (i:=p.walk.length-1) (by omega)
    rw [show p.walk.length-1+1=p.walk.length by omega,p.walk.getVert_length] at hh
    exact adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp hh)
  have ht : color d.radical t = true := by
    have hh := adjacent_color_ne d.radical hct
    rw [p.end_color] at hh
    cases he : color d.radical t <;> simp_all
  have het : Adjacent d.radical (p.walk.getVert (p.walk.length-2)) t := by
    have hh := p.walk.adj_getVert_succ (i:=p.walk.length-2) (by omega)
    rw [show p.walk.length-2+1=p.walk.length-1 by omega] at hh
    exact (cosetGraph_adj d.radical _ _).mp hh
  let Y := V d.radical a ⊓ Q d.radical (p.walk.getVert (p.walk.length-2))
  have hYt : Y ≤ Q d.radical t := inf_le_right.trans (Q_le_adjacent_h d.radical ht het)
  have hY : Y ≤ stabilizer d.radical a' := fun _ hx =>
    (hYt hx).2 _ (adjacent_symm d.radical hct)
  have hcomm : ⁅U d.radical a',U d.radical a⁆ ≤ ⁅Z d.radical a,Z d.radical a'⁆ := by
    rw [commutator_comm]
    exact commutator_mono (DistanceEight.U_le_Z d.radical a) (DistanceEight.U_le_Z d.radical a')
  have hRZa : ⁅Z d.radical a,Z d.radical a'⁆ ≤ Z d.radical a :=
    ((critical_Z_commutator_le_moving (h:=h) p).trans inf_le_left).trans (DistanceEight.U_le_Z d.radical a)
  let := (replacementGeometry h d).Z_elementary (replacementDistance_pos h d) a p.start_color
  let : IsElementaryAbelian 2 (U d.radical a) := IsElementaryAbelian.of_le (DistanceEight.U_le_Z d.radical a)
  have hAA : ⁅U d.radical a',U d.radical a⁆ ≤
      centralizer (U d.radical a : Set (FreeAmalgam d.radical)) :=
    (hcomm.trans hRZa).trans ((le_centralizer_iff_isMulCommutative.mpr inferInstance).trans
      (centralizer_le (show (U d.radical a : Set (FreeAmalgam d.radical)) ⊆ Z d.radical a from DistanceEight.U_le_Z d.radical a)))
  have hAY : ⁅U d.radical a',U d.radical a⁆ ≤ centralizer (Y : Set (FreeAmalgam d.radical)) :=
    hcomm.trans (le_centralizer_iff.mp (critical_radius_intersection_centralizes (h:=h) p hb))
  obtain ⟨i,hi,hir,hiQ,hiU⟩ := vertex_coordinates (h:=h) hc a' p.end_color
  have hA : U d.radical a ≤ i.range := by
    rw [hir]
    exact (DistanceEight.U_le_Z d.radical a).trans (Z_le_stabilizer_of_dist_le a _ p.critical.1.le)
  have hforwardU := critical_forward_moving_image_four_le s hc p hforward
  obtain ⟨W,hW,_,hpres,hcontrol⟩ := embedded_cover_restriction_preserving s i hi (U d.radical a) hA
    (hiQ.symm ▸ hforwardU) (hiU.symm ▸ hAA)
  have hWU : W ≤ U d.radical a' := hiU ▸ hW
  have hbound : ⁅Y,W⁆ ≤ ⁅Z d.radical a,Z d.radical a'⁆ := by
    rw [commutator_comm]
    have hh := hcontrol Y (hY.trans_eq hir.symm) (hiU.symm ▸ hAY)
    rw [hiU] at hh
    exact hh.trans hcomm
  have hUbase : U d.radical a' ≤ (embedM d.radical).range := by
    change U d.radical a' ≤ Mbar d.radical
    rw [←stabilizer_m_base d.radical]
    exact (DistanceEight.U_le_Z d.radical a').trans
      (critical_Z_le_stabilizer d.radical (replacementGeometry h d) (alpha d.radical) rfl
        (replacementDistance_pos h d) p.critical)
  let := (replacementGeometry h d).Z_elementary (replacementDistance_pos h d) a' p.end_color
  let : IsElementaryAbelian 2 (U d.radical a') := IsElementaryAbelian.of_le (DistanceEight.U_le_Z d.radical a')
  have hqreverse : ⁅U d.radical a,U d.radical a'⁆ ≤
      centralizer (U d.radical a' : Set (FreeAmalgam d.radical)) :=
    ((commutator_mono (DistanceEight.U_le_Z d.radical a) (DistanceEight.U_le_Z d.radical a')).trans
      ((critical_Z_commutator_le_moving (h := h) p).trans inf_le_right)).trans
        (le_centralizer_iff_isMulCommutative.mpr inferInstance)
  have hpresreverse : ⁅U d.radical a,W⁆ = ⁅U d.radical a,U d.radical a'⁆ := by
    rw [commutator_comm,commutator_comm (U d.radical a)]
    exact hiU ▸ hpres
  have hr := reverse_critical_moving_image_four_le s hc p hforward
  have hQbase := Q_alpha d.radical (replacement_radical_isPGroup h d) (replacement_core_le_radical h d)
  have hU := hc.U_eq_moved
  obtain ⟨c,hcW,hc2,hceven⟩ := embedded_preserving_actor_even s hcore
    (embedM d.radical) (embedM_injective d.radical) (U d.radical a') W hUbase hWU
    (hQbase ▸ hr) (hU ▸ hqreverse) (hU ▸ hpresreverse)
  exact ⟨W,hWU,hbound,c,hcW,hc2,hceven⟩


include s in
private theorem radius_exact_even_control
    (hc : DistanceTwo.CentralLayer d) (hb : 2 < replacementDistance h d)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hlarge : 4 ≤ (Q d.radical a').relIndex (Z d.radical (alpha d.radical))) :
    ∃ W : Subgroup (FreeAmalgam d.radical), W ≤ U d.radical a' ∧
      ⁅V d.radical (alpha d.radical) ⊓ Q d.radical (p.walk.getVert (p.walk.length-2)),W⁆ ≤
        ⁅Z d.radical (alpha d.radical),Z d.radical a'⁆ ∧
      ∃ a ∈ (W.comap (embedM d.radical)).map s.projection,
        orderOf a = 2 ∧ a ∈ alternatingGroup (Fin 6) := by
  rcases moved_card s with hnat | hcore
  · obtain ⟨a,ha,hao,haeven⟩ := critical_moving_even_actor s hc p hlarge
    exact ⟨U d.radical a',le_rfl,natural_radius_exact_control s hc hnat hb p hlarge,
      a,ha,hao,haeven⟩
  · exact core_radius_exact_even_control s hc hcore hb p hlarge

include s in
/-- A single full endpoint restriction retains index, attachment, critical
commutator and an even involution, while controlling the whole radius kernel. -/
theorem large_image_full_seed_even_control
    (hc : DistanceTwo.CentralLayer d) (hb : replacementDistance h d = 4)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hlarge : 4 ≤ (Q d.radical a').relIndex (Z d.radical (alpha d.radical))) :
    ∃ E : Subgroup (FreeAmalgam d.radical),
      Z d.radical (p.walk.getVert 3) ≤ E ∧ E ≤ Z d.radical a' ∧
      E.relIndex (Z d.radical a') ≤ 2 ∧
      ⁅Z d.radical (alpha d.radical),E⁆ =
        ⁅Z d.radical (alpha d.radical),Z d.radical a'⁆ ∧
      ⁅V d.radical (alpha d.radical) ⊓ Q d.radical (p.walk.getVert 2),E⁆ =
        ⁅Z d.radical (alpha d.radical),Z d.radical a'⁆ ∧
      ∃ a ∈ (E.comap (embedM d.radical)).map s.projection,
        orderOf a = 2 ∧ a ∈ alternatingGroup (Fin 6) := by
  have hb2 : 2 < replacementDistance h d := by omega
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  obtain ⟨E,hFE,hEZ,hi,_,hcomm,hcontrol⟩ :=
    large_image_full_seed_control s hc hb2 p hlarge
  obtain ⟨W,hWU,hWcontrol,a,ha,hao,haeven⟩ := radius_exact_even_control s hc hb2 p hlarge
  rw [hl] at hFE hcontrol hWcontrol
  have hWZ : W ≤ Z d.radical a' := hWU.trans (DistanceEight.U_le_Z d.radical _)
  have hRZe : ⁅Z d.radical (alpha d.radical),Z d.radical a'⁆ ≤ Z d.radical a' :=
    ((critical_Z_commutator_le_moving (h := h) p).trans inf_le_right).trans
      (DistanceEight.U_le_Z d.radical _)
  let := (replacementGeometry h d).Z_elementary (replacementDistance_pos h d) a' p.end_color
  have hRN : Z d.radical a' ≤ normalizer
      ((⁅Z d.radical (alpha d.radical),Z d.radical a'⁆ : Subgroup (FreeAmalgam d.radical)) : Set _) :=
    ((le_centralizer_iff_isMulCommutative.mpr inferInstance).trans
      (centralizer_le hRZe)).trans (Subgroup.centralizer_le_normalizer _)
  let := finite_Z d.radical a'
  refine ⟨E ⊔ W,hFE.trans le_sup_left,sup_le hEZ hWZ,
    (relIndex_le_of_le_left (show E ≤ E ⊔ W from le_sup_left)
      index_ne_zero_of_finite).trans hi,?_,?_,a,?_,hao,haeven⟩
  · exact le_antisymm (commutator_mono le_rfl (sup_le hEZ hWZ))
      (hcomm.ge.trans (commutator_mono le_rfl le_sup_left))
  · apply le_antisymm
    · rw [commutator_comm]
      exact commutator_sup_le_of_relative_normal (Z d.radical a') E W _
        ⁅Z d.radical (alpha d.radical),Z d.radical a'⁆ hRN hEZ hWZ
        (by rw [commutator_comm]; exact hcontrol.le)
        (by rwa [commutator_comm])
    · exact hcontrol.ge.trans (commutator_mono le_rfl le_sup_left)
  · exact map_mono (comap_mono (show W ≤ E ⊔ W from le_sup_right)) ha

include s in
private theorem full_seed_generating_neighbor
    (hc : DistanceTwo.CentralLayer d) (hb : replacementDistance h d = 4)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hlarge : 4 ≤ (Q d.radical a').relIndex (Z d.radical (alpha d.radical))) :
    ∃ E : Subgroup (FreeAmalgam d.radical),
      Z d.radical (p.walk.getVert 3) ≤ E ∧ E ≤ Z d.radical a' ∧
      E.relIndex (Z d.radical a') ≤ 2 ∧
      ⁅Z d.radical (alpha d.radical),E⁆ =
        ⁅Z d.radical (alpha d.radical),Z d.radical a'⁆ ∧
      ⁅V d.radical (alpha d.radical) ⊓ Q d.radical (p.walk.getVert 2),E⁆ =
        ⁅Z d.radical (alpha d.radical),Z d.radical a'⁆ ∧
      (¬ E ≤ Q d.radical (alpha d.radical)) ∧
      ∃ t, Adjacent d.radical (alpha d.radical) t ∧
        (normalizer (Q d.radical t : Set (FreeAmalgam d.radical)) ⊓
          stabilizer d.radical (alpha d.radical)) ⊔ E = stabilizer d.radical (alpha d.radical) ∧
        ((¬ ∃ P : Sylow 2 (L ⊔ R : Subgroup G),
          (P : Subgroup (L ⊔ R : Subgroup G)) = R.subgroupOf (L ⊔ R)) →
          Q d.radical t ⊔ E = stabilizer d.radical (alpha d.radical)) := by
  have hb2 : 2 < replacementDistance h d := by omega
  obtain ⟨E,hFE,hEZ,hi,hcomm,hcontrol,a,ha,hao,haeven⟩ :=
    large_image_full_seed_even_control s hc hb p hlarge
  have hEG : E ≤ stabilizer d.radical (alpha d.radical) := hEZ.trans
    (critical_Z_le_stabilizer d.radical (replacementGeometry h d) _ rfl
      (replacementDistance_pos h d) p.critical)
  have hEn : ¬ E ≤ Q d.radical (alpha d.radical) := by
    intro hEQ
    have hker : E.comap (embedM d.radical) ≤ s.projection.ker := by
      rw [s.projection_kernel]
      have hh := comap_mono (f := embedM d.radical) hEQ
      rwa [Q_alpha_comap d.radical (replacement_radical_isPGroup h d)
        (replacement_core_le_radical h d)] at hh
    have he := (Subgroup.map_eq_bot_iff (E.comap (embedM d.radical))).mpr hker
    have ha1 : a = 1 := mem_bot.mp (he ▸ ha)
    rw [ha1,orderOf_one] at hao
    omega
  refine ⟨E,hFE,hEZ,hi,hcomm,hcontrol,hEn,?_⟩
  by_cases hs : ∃ P : Sylow 2 (L ⊔ R : Subgroup G),
      (P : Subgroup (L ⊔ R : Subgroup G)) = R.subgroupOf (L ⊔ R)
  · obtain ⟨P,hP⟩ := hs
    obtain ⟨t,hat,hgen⟩ := SylowActor.generating_neighbor_of_even_actor
      s hb2 P hP E hEG a ha hao haeven
    exact ⟨t,hat,hgen,fun hn => (hn ⟨P,hP⟩).elim⟩
  · have himages := nonsylow_radical_image_maximal_knownSimple
      (e := e) (hz := hz) (hn := hn) hb2 hs
    rw [←SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s] at himages
    obtain ⟨t,hat,hgen⟩ := generating_neighbor_of_even_actor s himages E hEG a ha hao haeven
    have hQG : Q d.radical t ≤ stabilizer d.radical (alpha d.radical) :=
      fun _ hx => hx.2 _ (adjacent_symm d.radical hat)
    refine ⟨t,hat,le_antisymm (sup_le inf_le_right hEG) ?_,fun _ => hgen⟩
    exact hgen.symm.le.trans
      (sup_le_sup_right (le_inf (Q d.radical t).le_normalizer hQG) E)

include e hz hn in
/-- The generating backward selector retains the same full endpoint
restriction, its attachment, index and entire critical commutator. For an
original nonsylow radical, this very backward path has large critical image. -/
theorem large_image_full_seed_backward_knownSimple
    (hb : replacementDistance h d = 4)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hlarge : 4 ≤ (Q d.radical a').relIndex (Z d.radical (alpha d.radical))) :
    ∃ W : Subgroup (FreeAmalgam d.radical),
      Z d.radical (p.walk.getVert 3) ≤ W ∧ W ≤ Z d.radical a' ∧
      W.relIndex (Z d.radical a') ≤ 2 ∧
      ⁅Z d.radical (alpha d.radical),W⁆ =
        ⁅Z d.radical (alpha d.radical),Z d.radical a'⁆ ∧
      (¬ W ≤ Q d.radical (alpha d.radical)) ∧
      ⁅V d.radical (alpha d.radical) ⊓ Q d.radical (p.walk.getVert 2), W⁆ =
        ⁅Z d.radical (alpha d.radical),Z d.radical a'⁆ ∧
      ∃ t c, Adjacent d.radical (alpha d.radical) t ∧ Adjacent d.radical c t ∧
        (normalizer (Q d.radical t : Set (FreeAmalgam d.radical)) ⊓
          stabilizer d.radical (alpha d.radical)) ⊔ W = stabilizer d.radical (alpha d.radical) ∧
        ((¬ ∃ P : Sylow 2 (L ⊔ R : Subgroup G),
          (P : Subgroup (L ⊔ R : Subgroup G)) = R.subgroupOf (L ⊔ R)) →
          Q d.radical t ⊔ W = stabilizer d.radical (alpha d.radical)) ∧
        ∃ q : CriticalPath d.radical (replacementGeometry h d) c (p.walk.getVert 2),
          q.walk.getVert 1 = t ∧ q.walk.getVert 2 = alpha d.radical ∧
          q.walk.getVert 3 = p.walk.getVert 1 ∧
          (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
            (U d.radical c) =
          (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
            (U d.radical (p.walk.getVert 2)) ∧
          2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
            (U d.radical c) ∧
          (∃ x ∈ stabilizer d.radical (alpha d.radical), act d.radical x (p.walk.getVert 1) = t ∧
            ∃ k ∈ stabilizer d.radical t, c = act d.radical k (act d.radical x (p.walk.getVert 2)) ∧
              ∃ g ∈ normalizer (Q d.radical t : Set (FreeAmalgam d.radical)) ⊓
                  stabilizer d.radical (alpha d.radical),
                ∀ v ∈ Q d.radical t, (MulAut.conj k⁻¹) v = (MulAut.conj g) v) ∧
          ⁅Z d.radical c ⊓ Q d.radical (p.walk.getVert 2), W⁆ ≤
            ⁅Z d.radical (alpha d.radical),Z d.radical a'⁆ ∧
          ⁅(Z d.radical c ⊓ Q d.radical (p.walk.getVert 2)) ⊔ Z d.radical (alpha d.radical),W⁆ =
            ⁅Z d.radical (alpha d.radical),Z d.radical a'⁆ ∧
          W ≤ normalizer (((Z d.radical c ⊓ Q d.radical (p.walk.getVert 2) ⊔
            Z d.radical (alpha d.radical)) : Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)) ∧
          ⁅Z d.radical c, Z d.radical (p.walk.getVert 2)⁆ ≤
            centralizer (W : Set (FreeAmalgam d.radical)) ∧
          ((Q d.radical (p.walk.getVert 2)).relIndex (Z d.radical c) < 4 →
            ¬ normalizer (Q d.radical t : Set (FreeAmalgam d.radical)) ⊓
                stabilizer d.radical (alpha d.radical) ≤
              normalizer (((Z d.radical c ⊓ Q d.radical (p.walk.getVert 2) ⊔
                Z d.radical (alpha d.radical)) : Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical))) ∧
          ((¬ ∃ P : Sylow 2 (L ⊔ R : Subgroup G),
            (P : Subgroup (L ⊔ R : Subgroup G)) = R.subgroupOf (L ⊔ R)) →
            4 ≤ (Q d.radical (p.walk.getVert 2)).relIndex (Z d.radical c)) := by
  have hb2 : 2 < replacementDistance h d := by omega
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  obtain ⟨W,hFE,hWZ,hindex,hcritical,hexact,hWne,t,hat,hgen,hgenNS⟩ :=
    full_seed_generating_neighbor s hc hb p hlarge
  have hRZ : ⁅Z d.radical (alpha d.radical),Z d.radical a'⁆ ≤ Z d.radical (alpha d.radical) :=
    ((critical_Z_commutator_le_moving (h := h) p).trans inf_le_left).trans
      (DistanceEight.U_le_Z d.radical _)
  have hbound' := hexact.le.trans hRZ
  have hbound : ⁅V d.radical (alpha d.radical) ⊓
      Q d.radical (p.walk.getVert (p.walk.length-2)),W⁆ ≤ Z d.radical (alpha d.radical) := by
    simpa only [hl,show 4-2=2 from rfl] using hbound'
  have hWG : W ≤ stabilizer d.radical (alpha d.radical) := le_sup_right.trans_eq hgen
  have ha1 : Adjacent d.radical (alpha d.radical) (p.walk.getVert 1) := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) (by omega)
  have hd1 : Adjacent d.radical (p.walk.getVert 2) (p.walk.getVert 1) := by
    exact adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp
      (p.walk.adj_getVert_succ (i := 1) (by omega)))
  obtain ⟨x,hx,hxt⟩ := stabilizer_transitive_neighbors d.radical (alpha d.radical) ha1 hat
  have hct : Adjacent d.radical (act d.radical x (p.walk.getVert 2)) t := by
    rw [←hxt]
    exact (adjacent_act_iff d.radical x _ _).mpr hd1
  have hB : (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).map
      (MulAut.conj x⁻¹).toMonoidHom = B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _) :=
    mem_normalizer_iff_map_conj_eq.mp (Escape.Propagation.Rigidity.B_normalized
      hb2 (alpha d.radical) rfl ((stabilizer d.radical (alpha d.radical)).inv_mem hx))
  have hi : (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (act d.radical x (p.walk.getVert 2))) =
      (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
        (U d.radical (p.walk.getVert 2)) := by
    rw [U_act,←hB,relIndex_map_map_of_injective _ _ (MulAut.conj x⁻¹).injective,hB]
  have hstrict := large_image_forward_slice_gt_two_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p hlarge
  have hel : ¬ U d.radical (act d.radical x (p.walk.getVert 2)) ≤
      B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _) := by
    intro hh
    have he := relIndex_eq_one.mpr hh
    rw [hi] at he
    omega
  obtain ⟨k,hk,g,hg,hagree,q,hq1,hover,hidx⟩ := SylowActor.relative_controlled_backward_shift
    s hb2 p W hWG hWne hbound hat hct hgen hel
  have hc't : Adjacent d.radical (act d.radical k (act d.radical x (p.walk.getVert 2))) t := by
    have hfix : act d.radical k t = t := hk
    simpa only [hfix] using (adjacent_act_iff d.radical k _ t).mpr hct
  have hq2 : q.walk.getVert 2 = alpha d.radical := by
    simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using hover 0 (by omega)
  have hq3 : q.walk.getVert 3 = p.walk.getVert 1 := hover 1 (by omega)
  have hidx' := hidx.trans hi
  have hstrict' : 2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (act d.radical k (act d.radical x (p.walk.getVert 2)))) := by
    rw [hidx']
    exact hstrict
  have hout : ∃ q' : CriticalPath d.radical (replacementGeometry h d)
      (act d.radical k (act d.radical x (p.walk.getVert 2))) (p.walk.getVert 2),
      q'.walk.getVert 1 = t ∧ q'.walk.getVert 2 = alpha d.radical ∧
      q'.walk.getVert 3 = p.walk.getVert 1 := by
    have hex : ∃ q' : CriticalPath d.radical (replacementGeometry h d)
        (act d.radical k (act d.radical x (p.walk.getVert 2))) (p.walk.getVert (p.walk.length-2)),
        q'.walk.getVert 1 = t ∧ q'.walk.getVert 2 = alpha d.radical ∧
        q'.walk.getVert 3 = p.walk.getVert 1 := ⟨q,hq1,hq2,hq3⟩
    have he : p.walk.length-2 = 2 := by omega
    rw [he] at hex
    exact hex
  obtain ⟨q',hq1',hq2',hq3'⟩ := hout
  let c := act d.radical k (act d.radical x (p.walk.getVert 2))
  let K := Z d.radical c ⊓ Q d.radical (p.walk.getVert 2)
  let D := K ⊔ Z d.radical (alpha d.radical)
  have hdist : (cosetGraph d.radical).dist c (alpha d.radical) ≤ 2 := by
    have h1 : (cosetGraph d.radical).dist c t = 1 :=
      SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj d.radical _ _).mpr hc't)
    have h2 : (cosetGraph d.radical).dist t (alpha d.radical) = 1 :=
      SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj d.radical _ _).mpr (adjacent_symm d.radical hat))
    simpa only [h1,h2] using (cosetGraph_connected d.radical).dist_triangle
      (u := c) (v := t) (w := alpha d.radical)
  have hKV : K ≤ V d.radical (alpha d.radical) :=
    inf_le_left.trans ((Z_le_localZSpan d.radical _ _).trans (localZSpan_le_V d.radical hdist))
  have hmove : ⁅K,W⁆ ≤ ⁅Z d.radical (alpha d.radical),Z d.radical a'⁆ :=
    (commutator_mono (le_inf hKV inf_le_right) le_rfl).trans_eq hexact
  have hZaY : Z d.radical (alpha d.radical) ≤
      V d.radical (alpha d.radical) ⊓ Q d.radical (p.walk.getVert 2) := by
    apply le_inf (Z_le_VBall d.radical _ 2)
    apply Z_le_Q_of_dist_lt d.radical _ ((replacementGeometry h d).exists_critical _ rfl)
    rw [(replacementGeometry h d).distance_constant _ rfl,p.dist_start (by omega)]
    exact hb2
  have hDexact : ⁅D,W⁆ = ⁅Z d.radical (alpha d.radical),Z d.radical a'⁆ :=
    le_antisymm ((commutator_mono (sup_le (le_inf hKV inf_le_right) hZaY) le_rfl).trans_eq hexact)
      (hcritical.ge.trans (commutator_mono le_sup_right le_rfl))
  have hDmove : ⁅D,W⁆ ≤ Z d.radical (alpha d.radical) := hDexact.le.trans hRZ
  have hWD : W ≤ normalizer (D : Set (FreeAmalgam d.radical)) :=
    le_normalizer_iff_commutator_le_left.mpr (hDmove.trans le_sup_right)
  have hcent : ⁅Z d.radical c,Z d.radical (p.walk.getVert 2)⁆ ≤
      centralizer (W : Set (FreeAmalgam d.radical)) := by
    have hpre : ⁅Z d.radical c,Z d.radical (p.walk.getVert 2)⁆ ≤ Z d.radical (p.walk.getVert 2) :=
      ((critical_Z_commutator_le_moving (h := h) q').trans inf_le_right).trans
        (DistanceEight.U_le_Z d.radical _)
    have hQ : Z d.radical (p.walk.getVert 2) ≤ Q d.radical a' := by
      apply Z_le_Q_of_dist_lt d.radical _ ((replacementGeometry h d).exists_critical _ q'.end_color)
      rw [(replacementGeometry h d).distance_constant _ q'.end_color,p.dist_end]
      change p.walk.length-2 < replacementDistance h d
      omega
    have hCZ : Q d.radical a' ≤ centralizer (Z d.radical a' : Set (FreeAmalgam d.radical)) :=
      le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
        (Z_centralizes_Q d.radical a' p.end_color))
    exact (hpre.trans (hQ.trans hCZ)).trans
      (centralizer_le hWZ)
  have hsmall_bad (hsmall : (Q d.radical (p.walk.getVert 2)).relIndex (Z d.radical c) < 4)
      (hDN : stabilizer d.radical (alpha d.radical) ≤ normalizer (D : Set (FreeAmalgam d.radical))) :
      False := by
    have hDB : D ≤ B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _) :=
      normalized_radius_le_slice_of_actor_at s hb2 rfl D W
        (sup_le hKV (Z_le_VBall d.radical _ 2)) hDN hWG hWne hDmove
    have hKB : K ≤ B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _) :=
      le_sup_left.trans hDB
    let := finite_Z d.radical c
    have hidxK := relIndex_le_of_le_left hKB
      (index_ne_zero_of_finite (H := K.subgroupOf (Z d.radical c)))
    change (B d.radical (alpha d.radical) _).relIndex (Z d.radical c) ≤
      (Z d.radical c ⊓ Q d.radical (p.walk.getVert 2)).relIndex (Z d.radical c) at hidxK
    rw [inf_relIndex_left] at hidxK
    have hsmallidx := (small_critical_indices s hc q' hsmall).1
    have hle : (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
        (U d.radical c) ≤ 2 :=
      ((relIndex_le_of_le_right (DistanceEight.U_le_Z d.radical c)
        index_ne_zero_of_finite).trans hidxK).trans_eq hsmallidx
    exact (not_le_of_gt hstrict') hle

  refine ⟨W,hFE,hWZ,hindex,hcritical,hWne,hexact,t,c,hat,hc't,hgen,hgenNS,
    q',hq1',hq2',hq3',hidx',hstrict',⟨x,hx,hxt,k,hk,rfl,g,hg,hagree⟩,
    hmove,hDexact,hWD,hcent,?_,?_⟩
  · intro hsmall hND
    apply hsmall_bad hsmall
    rw [←hgen]
    exact sup_le hND hWD
  · intro hns
    by_contra! hsmall
    have hab := nonsylow_radical_image_elementary_knownSimple
      (e := e) (hz := hz) (hn := hn) hb2 hns
    rw [←SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s] at hab
    have hzero : ⁅d.radical.map s.projection,d.radical.map s.projection⁆ = ⊥ :=
      commutator_eq_bot_iff_le_centralizer.mpr
        (le_centralizer_iff_isMulCommutative.mpr hab.toIsMulCommutative)
    have hKN := (small_critical_end_kernels_normalized_of_abelian_image s hc hzero q' hsmall).1
    rw [hq1'] at hKN
    have hQG : Q d.radical t ≤ stabilizer d.radical (alpha d.radical) :=
      fun _ hx => hx.2 _ (adjacent_symm d.radical hat)
    have hQN : Q d.radical t ≤ normalizer (D : Set (FreeAmalgam d.radical)) :=
      (le_inf hKN (hQG.trans (Z_normalized d.radical _))).trans
        (normalizer_inf_normalizer_le_normalizer_sup _ _)
    apply hsmall_bad hsmall
    rw [←hgenNS hns]
    exact sup_le hQN hWD

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
