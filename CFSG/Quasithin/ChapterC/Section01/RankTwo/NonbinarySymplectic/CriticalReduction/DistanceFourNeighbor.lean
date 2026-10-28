module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.StrictIndexPathSelection
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.OriginalLargePaths

/-!
# The literal neighboring seed at distance at least four

The actual path neighbor has full B-relative moving index at least q.
If its join with the starting seed were vertex-normal, the critical endpoint
would force this join into B, making that same index one. Thus the original
join is nonnormal already at distance four; strict movement beyond q is not
needed for this implication.

When the reverse critical image has order at least q squared, the original
smaller-mover and large-mover selectors now give a backward critical path
in the prescribed residual orbit of the literal first two path vertices.
The maximizing plane is constructed in the branch where its hypothesis is
proved. The original and neighboring smaller movers are never identified.

Source: MS93 (5.8), printed p.920, and the selected path preparation for
(5.12)(1), printed pp.924--925. This settles the prescribed large-image
step at distance four. The root-image case with field-sized moving index,
the source commutator comparison (5.12)(1), and its subsequent normality
arguments remain separate obligations.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Theory.SpecificGroups.SymplecticFour
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction
open CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction.LargeDistance
open CFSG.Quasithin.ChapterC.Sp4Four.SourceComparison
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open ChapterB.QuasisimpleSource
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- The seed join at the literal first two-step vertex is nonnormal already
at distance four, using the actual moving index at least q. -/
theorem Input.replacement_path_neighbor_join_not_normal_of_four_le
    {geometry : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 ≤ geometry.b d.radical) :
    ¬ stabilizer d.radical a ≤ normalizer
      ((Z d.radical (path.walk.getVert 2) ⊔ Z d.radical a :
        Subgroup (FreeAmalgam d.radical)) : Set _) := by
  intro hn
  let c := path.walk.getVert 2
  let Y := Z d.radical c ⊔ Z d.radical a
  have hlen : 4 ≤ path.walk.length := by rwa [path.length_eq_b]
  have hc : color d.radical c=false :=
    (path.vertex_color (by omega)).mpr (by decide)
  have hcz : Z d.radical c ≤ Q d.radical z := by
    apply Z_le_Q_of_dist_lt d.radical c (geometry.exists_critical c hc)
    rw [geometry.distance_constant c hc,path.dist_end,path.length_eq_b]
    change geometry.b d.radical-2 < geometry.b d.radical
    omega
  have hfix : ⁅Z d.radical c,Z d.radical z⁆=⊥ := by
    apply commutator_eq_bot_iff_le_centralizer.mpr
    exact hcz.trans (le_centralizer_iff.mp
      (commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes z path.end_color)))
  have hYV : Y ≤ V d.radical a := by
    apply sup_le
    · exact le_iSup_of_le c (le_iSup_of_le (by
        rw [SimpleGraph.dist_comm]
        exact (path.dist_start (by omega : 2 ≤ path.walk.length)).le) le_rfl)
    · exact Z_le_VBall d.radical a 2
  have hYS := (hYV.trans (geometry.V_le_Q (by omega) a path.start_color)).trans
    (show Q d.radical a ≤ stabilizer d.radical a from fun _ hx => hx.1)
  have hdisp : ⁅Y,Z d.radical z⁆ ≤ Z d.radical a := by
    apply commutator_sup_le_of_relative_normal (stabilizer d.radical a)
      (Z d.radical c) (Z d.radical a) (Z d.radical z) (Z d.radical a)
      (Z_normalized d.radical a)
      (le_sup_left.trans hYS) (Z_le_stabilizer d.radical a)
    · rw [hfix]; exact bot_le
    · exact le_normalizer_iff_commutator_le_left.mp
        ((path.endpoint_Z_le_start_stabilizer (by omega)).trans (Z_normalized d.radical a))
  obtain ⟨E,hE,f,hf,hfQ,_⟩ := h.replacement_inner_natural_action d geometry hb path.start_color
  have hlarge : 3 < Nat.card E.Carrier := by
    rw [E.card_eq,hE]
    exact (by decide : 3 < 2^2).trans_le (Nat.pow_le_pow_right (by decide) h.nonbinary)
  let := Theory.SpecificGroups.SymplecticFour.SimpleQuotients.isSimpleGroup hlarge
  let : IsSimpleGroup (Sp E.Carrier) :=
    Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv.isSimpleGroup
  have hk : f.ker=(Q d.radical a).subgroupOf (stabilizer d.radical a) := by
    apply map_injective (stabilizer d.radical a).subtype_injective
    rw [hfQ,map_subgroupOf_eq_of_le (show Q d.radical a ≤ stabilizer d.radical a from fun _ hx => hx.1)]
  have hedge := MSCentralOrbit.edgeCentralizerCondition d.radical (h.replacement_two_group d)
    (h.replacement_core_le d) (h.replacement_omegaOrbit_centralizer d)
  have hescape := (critical_reverse d.radical geometry hedge a path.start_color
    (by rw [geometry.distance_constant a path.start_color]; exact lt_of_lt_of_le (by decide) hb)
    z path.end_color path.critical).2
  have hYB := normal_radius_le_B_of_kernel_escape geometry (by omega) path.start_color
    f hf hk (Q_isPGroup d.radical (h.replacement_two_group d)
      (h.replacement_core_le d) a path.start_color)
    Y (Z d.radical z) hYV hn (path.endpoint_Z_le_start_stabilizer (by omega)) hescape hdisp
  have hone := relIndex_eq_one.mpr (((U_le_Z c).trans le_sup_left).trans hYB)
  have hstrict := h.replacement_path_moving_index_ge_field d path hb
  rw [hone] at hstrict
  have hq : 1 < Nat.card F := Finite.one_lt_card
  omega

/-- A large reverse critical image supplies a backward shift in the
prescribed residual orbit of both original first vertices. The full B-index
and every literal path overlap are retained. -/
theorem Input.replacement_large_image_prescribed_backward_step
    {geometry : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 ≤ geometry.b d.radical)
    (hlarge : Nat.card F^2 ≤ (Q d.radical a).relIndex (Z d.radical z)) :
    ∃ y ∈ Ltilde d.radical a,
      let v := act d.radical y (path.walk.getVert 2)
      let w := act d.radical y (path.walk.getVert 1)
      Adjacent d.radical a w ∧ Adjacent d.radical v w ∧
      (B d.radical a (geometry.Z_normal a)).relIndex (U d.radical v) =
        (B d.radical a (geometry.Z_normal a)).relIndex
          (U d.radical (path.walk.getVert 2)) ∧
      ∃ back : CriticalPath d.radical geometry v (path.walk.getVert (path.walk.length-2)),
        back.walk.getVert 1 = w ∧
        ∀ i ≤ path.walk.length-2, back.walk.getVert (i+2) = path.walk.getVert i := by
  let t := path.walk.getVert 1
  let c := path.walk.getVert 2
  have hat : Adjacent d.radical a t := by
    have hh := (cosetGraph_adj d.radical _ _).mp
      (path.walk.adj_getVert_succ (by rw [path.length_eq_b]; omega : 0 < path.walk.length))
    simpa only [SimpleGraph.Walk.getVert_zero] using hh
  have hct : Adjacent d.radical c t := adjacent_symm d.radical
    ((cosetGraph_adj d.radical _ _).mp
      (path.walk.adj_getVert_succ (by rw [path.length_eq_b]; omega : 1 < path.walk.length)))
  have hnormal := h.replacement_path_neighbor_join_not_normal_of_four_le d path hb
  by_cases hJm : (centralizer (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
      (Q d.radical t) (Nat.card F^2) : Set (FreeAmalgam d.radical))).relIndex
        (U d.radical a) ≤ Nat.card F^2
  · obtain ⟨E,hE,f,hf,hfQ,hTf,hindex,hcore,hTP,hquad,hmax⟩ :=
      h.replacement_maximizing_parabolic d geometry hb path.start_color hat
    have hJplane := h.replacement_small_mover_le_maximizing_plane_of_index_le d
      geometry hb path.start_color hat E hE f hfQ hTf hindex hmax hJm
    obtain ⟨g,hg,x,hx,ha₁,hc₁,ha₂,hc₂,hgen₁,hgen₂,hfixed,hxn,hxp,
      v,hv,w,hvw,haw,hvw',hn,hidx,hback⟩ :=
      h.replacement_original_smaller_large_backward_path d path hb hat rfl hct hnormal
        E hE f hf hfQ hTf hindex hlarge hJplane
    rcases hvw with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact ⟨g⁻¹,(Ltilde d.radical a).inv_mem hg,haw,hvw',hidx,hback⟩
    · refine ⟨g⁻¹*x,(Ltilde d.radical a).mul_mem ((Ltilde d.radical a).inv_mem hg) hx,?_⟩
      dsimp only
      rw [act_mul,act_mul]
      exact ⟨haw,hvw',hidx,hback⟩
  · have hq : 1 < Nat.card F := Finite.one_lt_card
    have hl : Nat.card F < (Q d.radical a).relIndex (Z d.radical z) := by nlinarith
    obtain ⟨g,hg,haw,hvw,hidx,htransport,hgen,hfixed,hn,hback⟩ :=
      h.replacement_large_movement_selected_large_at_neighbor d path hb hat rfl hct
        hnormal hl (lt_of_not_ge hJm)
    exact ⟨g⁻¹,(Ltilde d.radical a).inv_mem hg,haw,hvw,hidx,hback⟩

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
