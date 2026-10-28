module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CubeRadiusPlane

/-!
# The central-intersection bound on the original paired chain

The literal source subgroup H lies in the selected edge seed and fixes the
original endpoint seed. The selected kernel together with that endpoint
seed and its cubic conjugate generates the starting stabilizer. Since the
conjugate critical seed has fixed index two on the full starting seed, H
has central index at most two there, including all central attachments.

A preceding paired shift supplies generation at the first interior vertex
by its two incident kernels. The part of H central at the starting vertex
transports into that interior seed. The large endpoint-radius actor forces
it into the next edge seed, so it is central at the interior vertex. The
same original transporter then makes it central at the backward starting
vertex. This proves the upper bound for the exact H used in (5.11)(2).
It contradicts the already proved lower bound four and hence gives the
required intermediate noncentrality above six, assuming the two strict
radius bounds. The preceding shift is retained explicitly; no two-kernel
generation at an arbitrary interior vertex is assumed.

Four coherent shifts and the established same-radius action implications
now force an actual critical path with radius index four whenever the
original nonsylow replacement has distance greater than four. Transport
places this path at the literal replacement base. This consumer has no
strict-radius or intermediate-centrality premise. Excluding that equality
case is the remaining strict-growth argument of (5.11)(1). The Sylow and
distance-four branches and the unconditional distance-two theorem remain
unproved. Both moved covers and the full central attachments are retained;
all paths, kernels and conjugators belong to the original natural graph.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (5.6) and (5.11), printed pp.917--918 and 923--924, in particular
the central-intersection comparison and the final radius argument on p.924.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open Representation.NormalElementaryQuotient
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open scoped commutatorElement IsMulCommutative Pointwise
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R} (s : FullSymmetricAction h e hz hn d)


include e hz hn in
private theorem paired_fixed_seed_central_index
    (hb : 4 < replacementDistance h d)
    (hns : ¬ ∃ T : Sylow 2 (L ⊔ R : Subgroup G),
      (T : Subgroup (L ⊔ R : Subgroup G)) = R.subgroupOf (L ⊔ R))
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (q : PairedBackwardShift (h := h) p)
    (H : Subgroup (FreeAmalgam d.radical))
    (hHZ : H ≤ Z d.radical a) (hHe : H ≤ Z d.radical q.edge)
    (hHend : H ≤ centralizer (Z d.radical a' : Set (FreeAmalgam d.radical))) :
    (centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))).relIndex H ≤ 2 := by
  let C := centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))
  let K := Q d.radical (act d.radical q.cubic a')
  have ht : color d.radical q.edge=true := by
    have hh := adjacent_color_ne d.radical q.adjacent_start
    rw [p.start_color] at hh
    cases he : color d.radical q.edge <;> simp_all
  have hHC : H ⊓ K ≤ C := by
    apply le_centralizer_iff.mpr
    rw [←q.endpoint_generation]
    refine sup_le (sup_le ?_ ?_) ?_
    · apply le_centralizer_iff.mp
      intro x hx
      have he := hHe hx.1
      rw [Z,if_neg (by simp [ht])] at he
      exact (mem_omegaCenter_iff.mp he).2.2
    · exact le_centralizer_iff.mp (inf_le_left.trans hHend)
    · exact le_centralizer_iff.mp (inf_le_right.trans
        (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
          (Z_centralizes_Q d.radical _ ((action_preserves_color d.radical _ _).trans p.end_color)))))
  have hfix : act d.radical q.cubic a = a := Ltilde_le_stabilizer _ q.cubic_mem
  have hidx : K.relIndex (Z d.radical a)=2 := by
    change (Q d.radical (act d.radical q.cubic a')).relIndex (Z d.radical a)=2
    conv_lhs => rhs; rw [←hfix]
    rw [Q_act,Z_act,relIndex_map_map_of_injective _ _ (MulAut.conj q.cubic⁻¹).injective]
    exact (nonsylow_critical_indices_two_knownSimple (e := e) (hz := hz) (hn := hn) hb hns p).1
  let := finite_Z d.radical a
  let : Finite H := Finite.of_injective (inclusion hHZ) (inclusion_injective _)
  have hi := relIndex_le_of_le_left hHC (index_ne_zero_of_finite (H := (H ⊓ K).subgroupOf H))
  rw [inf_relIndex_left] at hi
  exact hi.trans ((relIndex_le_of_le_right hHZ index_ne_zero_of_finite).trans_eq hidx)

include e hz hn in
private theorem paired_central_intersection_transfer
    (hb : 6 < replacementDistance h d)
    (hns : ¬ ∃ T : Sylow 2 (L ⊔ R : Subgroup G),
      (T : Subgroup (L ⊔ R : Subgroup G)) = R.subgroupOf (L ⊔ R))
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (q : PairedBackwardShift (h := h) p)
    (hgen : Q d.radical (p.walk.getVert 1) ⊔ Q d.radical (p.walk.getVert 3) =
      stabilizer d.radical (p.walk.getVert 2))
    (H : Subgroup (FreeAmalgam d.radical)) (hHc : H ≤ Z d.radical q.start)
    (hHend : H ≤ centralizer (V d.radical a' : Set (FreeAmalgam d.radical)))
    (hlarge : 2 < (Q d.radical (p.walk.getVert 2)).relIndex (V d.radical a')) :
    H ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)) ≤
      centralizer (stabilizer d.radical q.start : Set (FreeAmalgam d.radical)) := by
  let H₀ := H ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  obtain ⟨u,hfull⟩ := nonsylow_four_lt_radical_image_cube_knownSimple
    (e := e) (hz := hz) (hn := hn) (d := d) (by omega) hns
  have hR : d.radical.map s.projection ≤
      (CFSG.Quasithin.ChapterB.Offenders.D 6).map (MulAut.conj u).toMonoidHom := by
    rw [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s,hfull]
  have hfixed : H₀.map (MulAut.conj q.transporter⁻¹).toMonoidHom = H₀ :=
    mem_normalizer_iff_map_conj_eq.mp (Subgroup.centralizer_le_normalizer _
      (le_centralizer_iff.mp (show H₀ ≤ centralizer
        (stabilizer d.radical a : Set (FreeAmalgam d.radical)) from inf_le_right)
          ((stabilizer d.radical a).inv_mem q.transporter_mem)))
  have hH₂ : H₀ ≤ Z d.radical (p.walk.getVert 2) := by
    have hh : H₀ ≤ Z d.radical q.start := inf_le_left.trans hHc
    rw [←q.start_eq,Z_act,←hfixed] at hh
    exact (map_le_map_iff_of_injective (MulAut.conj q.transporter⁻¹).injective).mp hh
  have hl : p.walk.length=replacementDistance h d := p.length_eq_b
  have ha₂ : color d.radical (p.walk.getVert 2)=false :=
    (p.vertex_color (by omega)).mpr (by decide)
  have h₂₃ : Adjacent d.radical (p.walk.getVert 2) (p.walk.getVert 3) :=
    (cosetGraph_adj d.radical _ _).mp (p.walk.adj_getVert_succ (i := 2) (by omega))
  have ha₃ : color d.radical (p.walk.getVert 3)=true := by
    have hh := adjacent_color_ne d.radical h₂₃
    rw [ha₂] at hh
    cases he : color d.radical (p.walk.getVert 3) <;> simp_all
  have hV₃ : V d.radical a' ≤ Q d.radical (p.walk.getVert 3) := by
    apply V_le_Q_of_dist_add_two_lt d.radical (geometry := replacementGeometry h d) p.end_color
    rw [SimpleGraph.dist_comm,p.dist_end]
    change p.walk.length-3+2 < replacementDistance h d
    omega
  have hH₃ : H₀ ≤ Z d.radical (p.walk.getVert 3) :=
    (le_inf hH₂ (inf_le_left.trans hHend)).trans
      (cube_edge_large_fixed_le_seed s hc u hR ha₂ h₂₃ (V d.radical a') hV₃ hlarge)
  have hHC₂ : H₀ ≤ centralizer (stabilizer d.radical (p.walk.getVert 2) :
      Set (FreeAmalgam d.radical)) := by
    apply le_centralizer_iff.mpr
    rw [←hgen]
    refine sup_le ?_ ?_
    · apply le_centralizer_iff.mp
      apply (inf_le_right : H₀ ≤ centralizer (stabilizer d.radical a : Set _)).trans
      apply centralizer_le
      intro x hx
      apply hx.2 a
      apply adjacent_symm d.radical
      apply (cosetGraph_adj d.radical _ _).mp
      simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) (by omega)
    · apply le_centralizer_iff.mp
      intro x hx
      have hh := hH₃ hx
      rw [Z,if_neg (by simp [ha₃])] at hh
      exact (mem_omegaCenter_iff.mp hh).2.2
  have hh := (map_mono (f := (MulAut.conj q.transporter⁻¹).toMonoidHom) hHC₂).trans
    (map_centralizer_le_centralizer_image _ _)
  change H₀.map (MulAut.conj q.transporter⁻¹).toMonoidHom ≤
    centralizer ((stabilizer d.radical (p.walk.getVert 2)).map
      (MulAut.conj q.transporter⁻¹).toMonoidHom : Set (FreeAmalgam d.radical)) at hh
  rwa [hfixed,←stabilizer_act,q.start_eq] at hh

/-- On a shifted path, the preceding selector supplies generation at its
first interior component vertex by the two literal neighboring kernels. -/
theorem EdgePairedBackwardShift.first_interior_generation
    {a a' : Vertex d.radical}
    {p : CriticalPath d.radical (replacementGeometry h d) a a'}
    (q : EdgePairedBackwardShift (h := h) p) (hb : 2 < replacementDistance h d) :
    Q d.radical (q.path.walk.getVert 1) ⊔ Q d.radical (q.path.walk.getVert 3) =
      stabilizer d.radical (q.path.walk.getVert 2) := by
  have hl : p.walk.length = replacementDistance h d := p.length_eq_b
  have he₀ : q.path.walk.getVert 2=a := by
    simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using q.overlap 0 (Nat.zero_le _)
  have he₁ : q.path.walk.getVert 3=p.walk.getVert 1 := q.overlap 1 (by omega)
  rw [q.first,he₀,he₁]
  exact (sup_comm _ _).trans q.first_kernel_generation

include e hz hn in
/-- The central-intersection upper bound for the literal source H on the
paired chain. Both strict-radius premises are still required here. -/
theorem nonsylow_shifted_intermediate_central_radius_upper_knownSimple
    (hb : 6 < replacementDistance h d)
    (hns : ¬ ∃ T : Sylow 2 (L ⊔ R : Subgroup G),
      (T : Subgroup (L ⊔ R : Subgroup G)) = R.subgroupOf (L ⊔ R))
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (v : EdgePairedBackwardShift (h := h) p)
    (q : EdgePairedBackwardShift (h := h) v.path)
    (r : EdgePairedBackwardShift (h := h) q.path)
    (hcentral : ⁅Z d.radical r.start,Z d.radical (q.path.walk.getVert (q.path.walk.length-2))⁆ ≤
      centralizer (stabilizer d.radical q.start : Set (FreeAmalgam d.radical)))
    (hstrict₀ : 4 < (Q d.radical v.start).relIndex
      (V d.radical (p.walk.getVert (p.walk.length-2))))
    (hstrict : 4 < (Q d.radical q.start).relIndex
      (V d.radical (v.path.walk.getVert (v.path.walk.length-2)))) :
    let H := ⁅Z d.radical q.start,
      V d.radical (v.path.walk.getVert (v.path.walk.length-2)) ⊓ Q d.radical v.start⁆
    (centralizer (stabilizer d.radical q.start : Set (FreeAmalgam d.radical))).relIndex H ≤ 2 := by
  let H := ⁅Z d.radical q.start,
    V d.radical (v.path.walk.getVert (v.path.walk.length-2)) ⊓ Q d.radical v.start⁆
  obtain ⟨hlarge,_,_,hHZ,_,hHV⟩ :=
    nonsylow_intermediate_central_radius_displacement_knownSimple
      (e := e) (hz := hz) (hn := hn) hb hns v.path q r hcentral hstrict₀ hstrict
  obtain ⟨_,_,_,hHe,_,_,_⟩ := nonsylow_intermediate_central_radius_plane_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hns v.path q r hcentral hstrict₀ hstrict
  have hHc : H ≤ Z d.radical q.start :=
    hHe.trans (adjacent_Z_le d.radical q.path.start_color q.adjacent_shift)
  have hi := paired_fixed_seed_central_index (e := e) (hz := hz) (hn := hn)
    (by omega) hns v.path q.toPairedBackwardShift H hHZ hHe
      (hHV.trans (centralizer_le (Z_le_VBall d.radical _ 2)))
  have htransfer := paired_central_intersection_transfer (e := e) (hz := hz) (hn := hn)
    hb hns v.path q.toPairedBackwardShift (v.first_interior_generation (by omega)) H hHc hHV hlarge
  let := finite_Z d.radical v.start
  let : Finite H := Finite.of_injective (inclusion hHZ) (inclusion_injective _)
  have hup := relIndex_le_of_le_left htransfer (index_ne_zero_of_finite
    (H := (H ⊓ centralizer (stabilizer d.radical v.start : Set (FreeAmalgam d.radical))).subgroupOf H))
  rw [inf_relIndex_left] at hup
  exact hup.trans hi

include e hz hn in
/-- Strict growth at the two successive radii excludes intermediate
centrality above six. The preceding paired shift discharges the required
interior generation, on the same original graph. -/
theorem nonsylow_shifted_intermediate_noncentral_of_strict_knownSimple
    (hb : 6 < replacementDistance h d)
    (hns : ¬ ∃ T : Sylow 2 (L ⊔ R : Subgroup G),
      (T : Subgroup (L ⊔ R : Subgroup G)) = R.subgroupOf (L ⊔ R))
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (v : EdgePairedBackwardShift (h := h) p)
    (q : EdgePairedBackwardShift (h := h) v.path)
    (r : EdgePairedBackwardShift (h := h) q.path)
    (hstrict₀ : 4 < (Q d.radical v.start).relIndex
      (V d.radical (p.walk.getVert (p.walk.length-2))))
    (hstrict : 4 < (Q d.radical q.start).relIndex
      (V d.radical (v.path.walk.getVert (v.path.walk.length-2)))) :
    ¬ ⁅Z d.radical r.start,Z d.radical (q.path.walk.getVert (q.path.walk.length-2))⁆ ≤
      centralizer (stabilizer d.radical q.start : Set (FreeAmalgam d.radical)) := by
  intro hcentral
  have hu := nonsylow_shifted_intermediate_central_radius_upper_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hns p v q r hcentral hstrict₀ hstrict
  have hl := (nonsylow_intermediate_central_radius_displacement_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hns v.path q r hcentral hstrict₀ hstrict).2.2.1
  omega

include e hz hn in
/-- Every nonsylow replacement of critical distance greater than four has
an actual critical path whose opposite radius index is exactly four.
The strict-radius theorem is now the only remaining source-(5.11) input
for this branch; no intermediate-centrality premise remains. -/
theorem nonsylow_four_lt_exists_radius_four_knownSimple
    (hb : 4 < replacementDistance h d)
    (hns : ¬ ∃ T : Sylow 2 (L ⊔ R : Subgroup G),
      (T : Subgroup (L ⊔ R : Subgroup G)) = R.subgroupOf (L ⊔ R)) :
    ∃ a a' : Vertex d.radical,
      ∃ _p : CriticalPath d.radical (replacementGeometry h d) a a',
        (Q d.radical a).relIndex (V d.radical a')=4 := by
  obtain ⟨a',⟨p⟩⟩ := CriticalPath.exists_from (R := d.radical)
    (geometry := replacementGeometry h d) (a := alpha d.radical) rfl
  by_cases hb6 : 6 < replacementDistance h d
  · obtain ⟨v⟩ := nonsylow_edge_paired_backward_shift_knownSimple
      (e := e) (hz := hz) (hn := hn) hb hns p
    obtain ⟨q,r,t,_,_,_,hact₄,hact₆⟩ := nonsylow_edge_paired_terminal_radius_actions_knownSimple
      (e := e) (hz := hz) (hn := hn) hb hns v.path
    have small {c z : Vertex d.radical}
        (w : CriticalPath d.radical (replacementGeometry h d) c z)
        (hh : (Q d.radical c).relIndex (V d.radical z) ≤ 4) :
        (Q d.radical c).relIndex (V d.radical z)=4 :=
      (small_opposite_radius_eq_four_knownSimple (e := e) (hz := hz) (hn := hn)
        (by omega) w hh).2.2
    by_cases hv : 4 < (Q d.radical v.start).relIndex (V d.radical (p.walk.getVert (p.walk.length-2)))
    · by_cases hq : 4 < (Q d.radical q.start).relIndex
          (V d.radical (v.path.walk.getVert (v.path.walk.length-2)))
      · by_cases hr : 4 < (Q d.radical r.start).relIndex
            (V d.radical (q.path.walk.getVert (q.path.walk.length-2)))
        · have hn₄ := nonsylow_shifted_intermediate_noncentral_of_strict_knownSimple
            (e := e) (hz := hz) (hn := hn) hb6 hns p v q r hv hq
          have hn₆ := nonsylow_shifted_intermediate_noncentral_of_strict_knownSimple
            (e := e) (hz := hz) (hn := hn) hb6 hns v.path q r t hq hr
          let z₄ := q.path.walk.getVert (q.path.walk.length-2)
          have hi₄ : (Q d.radical q.start).relIndex (V d.radical z₄) ≤ 2 := by
            by_contra! hh
            exact hn₄ (hact₄ hh)
          have hi₆ : (Q d.radical r.start).relIndex (V d.radical z₄ ⊓ Q d.radical q.start) ≤ 2 := by
            by_contra! hh
            exact hn₆ (hact₆ hh)
          have hVQ : V d.radical z₄ ≤ Q d.radical z₄ :=
            V_le_Q d.radical (geometry := replacementGeometry h d) r.path.end_color
              (by change 2 < replacementDistance h d; omega)
          let := finite_stabilizer d.radical z₄
          let : Finite (V d.radical z₄) := Finite.of_injective
            (inclusion (hVQ.trans (fun _ hx => hx.1))) (inclusion_injective _)
          have htower := relIndex_inf_mul_relIndex (Q d.radical r.start)
            (Q d.radical q.start) (V d.radical z₄)
          rw [inf_comm (Q d.radical q.start)] at htower
          have hmono : (Q d.radical r.start).relIndex (V d.radical z₄) ≤
              (Q d.radical r.start ⊓ Q d.radical q.start).relIndex (V d.radical z₄) :=
            relIndex_le_of_le_left inf_le_left index_ne_zero_of_finite
          have hupper : (Q d.radical r.start).relIndex (V d.radical z₄) ≤ 4 := by
            rw [←htower] at hmono
            exact hmono.trans ((Nat.mul_le_mul hi₆ hi₄).trans (by decide))
          exact ⟨_,_,r.path,small r.path hupper⟩
        · exact ⟨_,_,r.path,small r.path (Nat.le_of_not_gt hr)⟩
      · exact ⟨_,_,q.path,small q.path (Nat.le_of_not_gt hq)⟩
    · exact ⟨_,_,v.path,small v.path (Nat.le_of_not_gt hv)⟩
  · have heven := replacementDistance_even h d
    rw [Nat.even_iff] at heven
    have heq : replacementDistance h d=6 := by omega
    obtain ⟨q,r,t,_,_,_,_,_,hi⟩ := nonsylow_edge_paired_terminal_six_knownSimple
      (e := e) (hz := hz) (hn := hn) heq hns p
    exact ⟨_,_,r.path,hi⟩

include e hz hn in
/-- Transport the forced radius-four path to the actual replacement base.
This is the remaining equality case for the strict-radius source argument. -/
theorem nonsylow_four_lt_exists_base_radius_four_knownSimple
    (hb : 4 < replacementDistance h d)
    (hns : ¬ ∃ T : Sylow 2 (L ⊔ R : Subgroup G),
      (T : Subgroup (L ⊔ R : Subgroup G)) = R.subgroupOf (L ⊔ R)) :
    ∃ a' : Vertex d.radical,
      ∃ _p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a',
        (Q d.radical (alpha d.radical)).relIndex (V d.radical a')=4 := by
  obtain ⟨a,a',p,hi⟩ := nonsylow_four_lt_exists_radius_four_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hns
  obtain ⟨g,hg⟩ := exists_mVertex_of_color d.radical p.start_color
  have hbase : act d.radical g⁻¹ a = alpha d.radical := by
    rw [hg,act_mVertex,mul_inv_cancel]
    rfl
  have hex : ∃ q : CriticalPath d.radical (replacementGeometry h d)
      (act d.radical g⁻¹ a) (act d.radical g⁻¹ a'),
      (Q d.radical (act d.radical g⁻¹ a)).relIndex (V d.radical (act d.radical g⁻¹ a'))=4 := by
    refine ⟨p.act g⁻¹,?_⟩
    rw [Q_act,V_act,relIndex_map_map_of_injective _ _ (MulAut.conj (g⁻¹)⁻¹).injective]
    exact hi
  rw [hbase] at hex
  exact ⟨_,hex⟩

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
