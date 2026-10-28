module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.PairedRadiusIntersectionGrowth
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.TerminalLargeActorFixed
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.DistanceReduction.LargeDistance.SourceCalculation

/-!
# Intermediate seeds for the actual paired terminal commutators

The maximizing parabolic acts quadratically on the whole U-layer. The
whole-Z decomposition retains its full vertex-central attachment and
therefore gives quadraticity on Z as well. Across equal smaller movers,
the full neighboring-kernel displacement is fixed by their common mover;
its large actor index puts that displacement in the neighboring seed.
Every actual critical commutator consequently lies in its second seed,
without an assumption on its critical image order or an identity X = Z.

Apply this inclusion to the literal paired critical paths and combine the
proved two-kernel radius growth with their common radius centrality. One
of the paired commutators lies two same-color steps farther along its path.
These commutators retain their own critical endpoints: they are not the
fixed-endpoint R-definition printed in MS93 (5.11), p.924. Excluding the
resulting seed containments remains a separate source duty.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped Pointwise IsMulCommutative
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction
open CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction.LargeDistance
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- Above distance four the literal smaller mover is quadratic on the
whole original seed, including its complete vertex-central attachment. -/
theorem Input.replacement_small_mover_Z_quadratic_of_four_lt
    (geometry : Geometry d.radical) (hb : 4 < geometry.b d.radical)
    {a t : Vertex d.radical} (ha : color d.radical a=false)
    (hat : Adjacent d.radical a t) :
    let J := Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
      (Q d.radical t) (Nat.card F^2)
    ⁅⁅Z d.radical a,J⁆,J⁆=⊥ := by
  let S := stabilizer d.radical a
  let J := Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
    (Q d.radical t) (Nat.card F^2)
  let C := Z d.radical a ⊓ centralizer (S : Set (FreeAmalgam d.radical))
  change ⁅⁅Z d.radical a,J⁆,J⁆=⊥
  have hJS : J ≤ S := (Subgroup.SmallMover.join_le _ _ _ _).trans
    (fun _ hx => hx.2 a (adjacent_symm _ hat))
  have hUS : U d.radical a ≤ S := (U_le_Z a).trans (Z_le_stabilizer _ a)
  obtain ⟨E,hE,f,hf,hfQ,hTf,hindex,hJP,hcore,hTP,hquad,hmax⟩ :=
    h.replacement_maximizing_parabolic_contains_mover_of_four_lt d geometry hb ha hat
  have hquadJ : ⁅⁅(U d.radical a).subgroupOf S,J.subgroupOf S⁆,J.subgroupOf S⁆=⊥ :=
    le_bot_iff.mp ((commutator_mono (commutator_mono le_rfl hJP) hJP).trans hquad.le)
  have hquadU : ⁅⁅U d.radical a,J⁆,J⁆=⊥ := by
    have hh := congrArg (Subgroup.map S.subtype) hquadJ
    rwa [map_commutator,map_commutator,map_subgroupOf_eq_of_le hUS,
      map_subgroupOf_eq_of_le hJS,Subgroup.map_bot] at hh
  have hsplit : Z d.radical a=U d.radical a ⊔ C :=
    h.replacement_Z_eq_U_sup_fixed d geometry hb.le ha
  have hUJ : ⁅U d.radical a,J⁆ ≤ U d.radical a :=
    le_normalizer_iff_commutator_le_left.mp (hJS.trans (U_normalized a))
  let := geometry.Z_elementary (by omega) a ha
  have hnorm : Z d.radical a ≤ normalizer ((⁅U d.radical a,J⁆ :
      Subgroup (FreeAmalgam d.radical)) : Set _) :=
    ((Z d.radical a).le_centralizer.trans
      (centralizer_le (hUJ.trans (U_le_Z a)))).trans (Subgroup.centralizer_le_normalizer _)
  have hcomm : ⁅Z d.radical a,J⁆ ≤ ⁅U d.radical a,J⁆ := by
    rw [hsplit]
    apply commutator_sup_le_of_relative_normal (Z d.radical a) (U d.radical a) C J
      ⁅U d.radical a,J⁆ hnorm (U_le_Z a) inf_le_left le_rfl
    rw [commutator_eq_bot_iff_le_centralizer.mpr
      (show C ≤ centralizer (J : Set (FreeAmalgam d.radical)) from
        inf_le_right.trans (centralizer_le hJS))]
    exact bot_le
  exact le_bot_iff.mp ((commutator_mono hcomm le_rfl).trans hquadU.le)

omit [CharP F 2] in
private theorem core_le_mover
    {a t : Vertex d.radical} (ha : color d.radical a=false)
    (hat : Adjacent d.radical a t) :
    Q d.radical a ≤ Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
      (Q d.radical t) (Nat.card F^2) := by
  obtain ⟨j,hj,hjr,hjR,hjQ,hjU⟩ := Sp4Four.LocalPackage.edge_coordinates d.radical
    (h.replacement_two_group d) (h.replacement_core_le d) ha hat
  have hh := map_mono (f := j) (Subgroup.SmallMover.kernel_le_join
    (Sp4Four.LocalPackage.initialLayer d.radical) (pCore 2 d.overgroup) d.radical
    (Nat.card F^2) (Nat.one_le_pow _ _ Nat.card_pos) (h.replacement_core_le d)
    (Sp4Four.LocalPackage.initialLayer_centralizes_core d.radical
      (h.replacement_two_group d) (h.replacement_core_le d)))
  rwa [Subgroup.SmallMover.join_map j hj,hjU,hjQ,hjR] at hh

private theorem equal_mover_kernel_displacement_le_seed
    (geometry : Geometry d.radical) (hb : 4 < geometry.b d.radical)
    {a t c : Vertex d.radical} (ha : color d.radical a=false)
    (hc : color d.radical c=false)
    (hat : Adjacent d.radical a t) (hct : Adjacent d.radical c t)
    (hequal : Subgroup.SmallMover.join (U d.radical c) (Q d.radical c)
        (Q d.radical t) (Nat.card F^2) =
      Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
        (Q d.radical t) (Nat.card F^2)) :
    ⁅Z d.radical c,Q d.radical a⁆ ≤ Z d.radical a := by
  let J := Subgroup.SmallMover.join (U d.radical c) (Q d.radical c)
    (Q d.radical t) (Nat.card F^2)
  have hQaJ : Q d.radical a ≤ J := by
    dsimp only [J]
    rw [hequal]
    exact core_le_mover h d ha hat
  have hJSc : J ≤ stabilizer d.radical c := (Subgroup.SmallMover.join_le _ _ _ _).trans
    (fun _ hx => hx.2 c (adjacent_symm _ hct))
  have hDZ : ⁅Z d.radical c,Q d.radical a⁆ ≤ Z d.radical c :=
    le_normalizer_iff_commutator_le_left.mp
      (hQaJ.trans (hJSc.trans (Z_normalized _ c)))
  have hDJ : ⁅⁅Z d.radical c,Q d.radical a⁆,J⁆=⊥ :=
    le_bot_iff.mp ((commutator_mono (commutator_mono le_rfl hQaJ) le_rfl).trans
      (h.replacement_small_mover_Z_quadratic_of_four_lt d geometry hb hc hct).le)
  have hlarge : Nat.card F < (Q d.radical c).relIndex J := by
    have hh := h.replacement_small_mover_join_index d geometry hb.le hc hct
    have hq : 1 < Nat.card F := Finite.one_lt_card
    dsimp only [J]
    exact lt_of_lt_of_le (by nlinarith) hh
  exact (h.replacement_equal_mover_large_actor_fixed_le_seed d geometry hb hc hct hat
    hequal.symm J le_rfl hlarge _ hDZ hDJ).trans inf_le_left

/-- Every literal critical commutator lies in the second seed when the
critical distance exceeds four, for all critical image orders. -/
theorem Input.replacement_critical_commutator_le_second_seed_of_four_lt
    {geometry : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 < geometry.b d.radical) :
    ⁅Z d.radical a,Z d.radical z⁆ ≤ Z d.radical (path.walk.getVert 2) := by
  have hlen : 4 < path.walk.length := by rwa [path.length_eq_b]
  have hc : color d.radical (path.walk.getVert 2)=false :=
    (path.vertex_color (by omega : 2 ≤ path.walk.length)).mpr (by decide)
  have hat : Adjacent d.radical a (path.walk.getVert 1) := by
    have hh := (cosetGraph_adj d.radical _ _).mp
      (path.walk.adj_getVert_succ (by omega : 0 < path.walk.length))
    simpa only [SimpleGraph.Walk.getVert_zero] using hh
  have hct : Adjacent d.radical (path.walk.getVert 2) (path.walk.getVert 1) :=
    adjacent_symm _ ((cosetGraph_adj d.radical _ _).mp
      (path.walk.adj_getVert_succ (by omega : 1 < path.walk.length)))
  have hequal : Subgroup.SmallMover.join (U d.radical (path.walk.getVert 2))
      (Q d.radical (path.walk.getVert 2)) (Q d.radical (path.walk.getVert 1))
      (Nat.card F^2) = Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
        (Q d.radical (path.walk.getVert 1)) (Nat.card F^2) := by
    simpa only [pathMoverAgreement,Nat.mul_zero,Nat.zero_add,SimpleGraph.Walk.getVert_zero]
      using h.replacement_mover_agreement_of_four_lt d ⟨a,z,path⟩ hb
  have hzQ : Z d.radical z ≤ Q d.radical (path.walk.getVert 2) := by
    apply Z_le_Q_of_dist_lt _ z (geometry.exists_critical z path.end_color)
    rw [geometry.distance_constant z path.end_color,SimpleGraph.dist_comm,
      path.dist_end,path.length_eq_b]
    change geometry.b d.radical-2 < geometry.b d.radical
    omega
  exact (commutator_mono le_rfl hzQ).trans
    (equal_mover_kernel_displacement_le_seed h d geometry hb hc path.start_color
      hct hat hequal.symm)

/-- The actual paired critical commutators satisfy the terminal seed
alternative, with the original radius and both full kernel factors. -/
theorem Input.replacement_paired_radius_terminal_seed_alternative
    {geometry : Geometry d.radical} (hb : 4 < geometry.b d.radical)
    (s : ℕ → CriticalSegment geometry)
    (hs : ∀ i, BackwardLink geometry (pairedRadiusChoice geometry (Nat.card F))
      (s i) (s (i+1))) :
    ⁅Z d.radical (s 2).first,Z d.radical (s 2).last⁆ ≤ Z d.radical (s 0).first ∨
      ⁅Z d.radical (s 3).first,Z d.radical (s 3).last⁆ ≤ Z d.radical (s 1).first := by
  have htwo (i : ℕ) : (s (i+1)).path.walk.getVert 2=(s i).first := by
    simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using (hs i).overlap 0 (by omega)
  have hD₂ : ⁅Z d.radical (s 2).first,Z d.radical (s 2).last⁆ ≤ Z d.radical (s 1).first := by
    have hh := h.replacement_critical_commutator_le_second_seed_of_four_lt d (s 2).path hb
    rwa [htwo 1] at hh
  have hD₃ : ⁅Z d.radical (s 3).first,Z d.radical (s 3).last⁆ ≤ Z d.radical (s 2).first := by
    have hh := h.replacement_critical_commutator_le_second_seed_of_four_lt d (s 3).path hb
    rwa [htwo 2] at hh
  have hfix := commutator_eq_bot_iff_le_centralizer.mp
    (paired_critical_commutators_centralize_radius hb
      (pairedRadiusChoice geometry (Nat.card F)) s hs)
  have hfix₂ := le_sup_left.trans hfix
  have hfix₃ := le_sup_right.trans hfix
  rcases h.replacement_critical_radius_index_split d (s 2).path hb with hlarge | hlarge
  · rw [htwo 1] at hlarge
    have hh := h.replacement_path_penultimate_radius_large_actor_fixed_le_next_seed d
      (s 1).path hb (by rwa [←(hs 1).last_eq]) _ hD₂
        (by rw [←(hs 1).last_eq]; exact commutator_eq_bot_iff_le_centralizer.mpr hfix₂)
    rw [htwo 0] at hh
    exact Or.inl (hh.trans inf_le_left)
  · have hh := h.replacement_path_kernel_large_actor_fixed_le_next_seed d (s 2).path hb
      (V d.radical (s 2).last) hlarge _ hD₃
      (commutator_eq_bot_iff_le_centralizer.mpr (hfix₃.trans (centralizer_le inf_le_left)))
    rw [htwo 1] at hh
    exact Or.inr (hh.trans inf_le_left)

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
