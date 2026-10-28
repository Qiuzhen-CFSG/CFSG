module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.Geometry.Paths
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneLongTerminalActions
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneLongCentralTransfer
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneLocalAction

/-!
# An actual generated radius-four path on the original cubic plane

The source-selected edge pairs preserve the original paths and their
interior generation. At distance six, the terminal action estimates give
index four. At larger distance, hypothetical strict growth makes each
intermediate line noncentral by opposite central-index bounds; the same
radius action estimates then bound one of the radii by four. All local
actors are original two-subgroups, retaining the cubic quotient E/Q.
Source: MS93 (5.11), printed pp.923--924.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open scoped commutatorElement
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "Rg" => edge L R
local notation "π" => CubicAction.projection h e hz hk

theorem EdgePlanePairedBackwardShift.first_interior_generation
    {a a' : Vertex Rg}
    {p : CriticalPath Rg (sourceGeometry h) a a'}
    (q : EdgePlanePairedBackwardShift (h := h) p) (hb : 2 < sourceDistance h) :
    Q Rg (q.path.walk.getVert 1) ⊔ Q Rg (q.path.walk.getVert 3) =
      stabilizer Rg (q.path.walk.getVert 2) := by
  have hl : p.walk.length = sourceDistance h := p.length_eq_b
  have he₀ : q.path.walk.getVert 2=a := by
    simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using q.overlap 0 (Nat.zero_le _)
  have he₁ : q.path.walk.getVert 3=p.walk.getVert 1 := q.overlap 1 (by omega)
  rw [q.first,he₀,he₁]
  exact (sup_comm _ _).trans q.first_kernel_generation


theorem plane_long_intermediate_central_radius_displacement
    (hb : 6 < sourceDistance h)
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    {a a' : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) a a')
    (q : EdgePlanePairedBackwardShift (h := h) p)
    (r : EdgePlanePairedBackwardShift (h := h) q.path)
    (hcentral : ⁅Z Rg r.start,Z Rg (q.path.walk.getVert (q.path.walk.length-2))⁆ ≤
      centralizer (stabilizer Rg q.start : Set (FreeAmalgam Rg)))
    (hstrict₀ : 4 < (Q Rg a).relIndex (V Rg a'))
    (hstrict : 4 < (Q Rg q.start).relIndex
      (V Rg (p.walk.getVert (p.walk.length-2)))) :
    let A := V Rg (p.walk.getVert (p.walk.length-2)) ⊓ Q Rg a
    let H := ⁅Z Rg q.start,A⁆
    2 < (Q Rg (p.walk.getVert 2)).relIndex (V Rg a') ∧
      2 < (Q Rg q.start).relIndex A ∧
      4 ≤ (centralizer (stabilizer Rg q.start : Set (FreeAmalgam Rg))).relIndex H ∧
      H ≤ Z Rg a ∧ H ≤ V Rg (p.walk.getVert (p.walk.length-2)) ∧
      H ≤ centralizer (V Rg a' : Set (FreeAmalgam Rg)) := by
  let z := p.walk.getVert (p.walk.length-2)
  let A := V Rg z ⊓ Q Rg a
  let H := ⁅Z Rg q.start,A⁆
  have hjoin := plane_long_paired_intermediate_central_radius_index h e hz hk hb u hR p
    q.toPlanePairedBackwardShift r.toPlanePairedBackwardShift q.first_kernel_generation hcentral
  have hi : (Q Rg a).relIndex (V Rg z) ≤ 2 := by
    have hh := relIndex_le_of_le_right (H := Q Rg a)
      (show V Rg z ≤ V Rg z ⊔
        (V Rg a' ⊓ Q Rg (p.walk.getVert 2)) from le_sup_left)
      (by rw [hjoin]; decide)
    exact hh.trans_eq hjoin
  have hi₀ : (Q Rg a).relIndex
      (V Rg a' ⊓ Q Rg (p.walk.getVert 2)) ≤ 2 := by
    have hh := relIndex_le_of_le_right (H := Q Rg a)
      (show V Rg a' ⊓ Q Rg (p.walk.getVert 2) ≤ V Rg z ⊔
        (V Rg a' ⊓ Q Rg (p.walk.getVert 2)) from le_sup_right)
      (by rw [hjoin]; decide)
    exact hh.trans_eq hjoin
  have hlarge₀ : 2 < (Q Rg (p.walk.getVert 2)).relIndex (V Rg a') := by
    have hVQ₀ : V Rg a' ≤ Q Rg a' :=
      V_le_Q Rg (geometry := sourceGeometry h) p.end_color
        (by change 2 < sourceDistance h; omega)
    let := finite_stabilizer Rg a'
    let : Finite (V Rg a') := Finite.of_injective
      (inclusion (hVQ₀.trans (fun _ hx => hx.1))) (inclusion_injective _)
    by_contra! hsmall
    have htower := relIndex_inf_mul_relIndex (Q Rg a)
      (Q Rg (p.walk.getVert 2)) (V Rg a')
    rw [inf_comm (Q Rg (p.walk.getVert 2))] at htower
    have hmono : (Q Rg a).relIndex (V Rg a') ≤
        (Q Rg a ⊓ Q Rg (p.walk.getVert 2)).relIndex (V Rg a') :=
      relIndex_le_of_le_left inf_le_left index_ne_zero_of_finite
    rw [←htower] at hmono
    have hupper := hmono.trans (Nat.mul_le_mul hi₀ hsmall)
    omega
  have hVQ : V Rg z ≤ Q Rg z :=
    V_le_Q Rg (geometry := sourceGeometry h) q.path.end_color
      (by change 2 < sourceDistance h; omega)
  let := finite_stabilizer Rg z
  let : Finite (V Rg z) := Finite.of_injective
    (inclusion (hVQ.trans (fun _ hx => hx.1))) (inclusion_injective _)
  have hlarge : 2 < (Q Rg q.start).relIndex A := by
    by_contra! hsmall
    have htower := relIndex_inf_mul_relIndex (Q Rg q.start) (Q Rg a) (V Rg z)
    rw [inf_comm (Q Rg a)] at htower
    have hmono : (Q Rg q.start).relIndex (V Rg z) ≤
        (Q Rg q.start ⊓ Q Rg a).relIndex (V Rg z) :=
      relIndex_le_of_le_left inf_le_left index_ne_zero_of_finite
    rw [←htower] at hmono
    have hupper := hmono.trans (Nat.mul_le_mul hsmall hi)
    change 4 < (Q Rg q.start).relIndex (V Rg z) at hstrict
    omega
  have ht : color Rg q.edge=true := by
    have hh := adjacent_color_ne Rg q.adjacent_start
    rw [p.start_color] at hh
    cases he : color Rg q.edge <;> simp_all
  have hAedge : A ≤ Q Rg q.edge :=
    inf_le_right.trans (Q_le_adjacent_h Rg ht q.adjacent_start)
  have hAG : A ≤ stabilizer Rg q.start :=
    hAedge.trans (fun _ hx => hx.2 _ (adjacent_symm Rg q.adjacent_shift))
  have hAtwo : IsPGroup 2 A :=
    (Q_isPGroup Rg h.relative_radical.isPGroup h.relative_radical.twoCore_le
      z q.path.end_color).to_le (inf_le_left.trans hVQ)
  have hlower := graph_large_actor_seed_commutator_index h e hz hk q.path.start_color A hAG hAtwo hlarge
  have hHZ : H ≤ Z Rg a :=
    ((commutator_mono le_rfl hAedge).trans
      (plane_edge_seed_commutator h e hz hk u hR q.path.start_color q.adjacent_shift)).trans
        (adjacent_Z_le Rg p.start_color q.adjacent_start)
  have hZG : Z Rg q.start ≤ stabilizer Rg z :=
    Z_le_stabilizer_of_dist_le q.start _ q.path.critical.1.le
  have hHV : H ≤ V Rg z :=
    (commutator_mono le_rfl (show A ≤ V Rg z from inf_le_left)).trans
      (le_normalizer_iff_commutator_le_right.mp (hZG.trans (DistanceEight.V_normalized Rg z)))
  have hdist : (cosetGraph Rg).dist z a'=2 := by
    change (cosetGraph Rg).dist (p.walk.getVert (p.walk.length-2)) a'=2
    rw [p.dist_end]
    have hl : p.walk.length=sourceDistance h := p.length_eq_b
    omega
  have hVV : V Rg z ≤ centralizer (V Rg a' : Set (FreeAmalgam Rg)) := by
    apply Escape.PairingControl.Geometry.V_centralizes_V_of_distance
      (geometry := sourceGeometry h) q.path.end_color p.end_color
    change (cosetGraph Rg).dist z a'+4 < sourceDistance h
    omega
  exact ⟨hlarge₀,hlarge,hlower,hHZ,hHV,hHV.trans hVV⟩


/-- On the same selected chain, centrality would force the source commutator
central index to be at most two, contradicting its actual two-actor bound. -/
theorem plane_long_shifted_intermediate_noncentral_of_strict
    (hb : 6 < sourceDistance h)
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    {a z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (v : EdgePlanePairedBackwardShift (h := h) p)
    (q : EdgePlanePairedBackwardShift (h := h) v.path)
    (r : EdgePlanePairedBackwardShift (h := h) q.path)
    (hstrict₀ : 4 < (Q Rg v.start).relIndex
      (V Rg (p.walk.getVert (p.walk.length-2))))
    (hstrict : 4 < (Q Rg q.start).relIndex
      (V Rg (v.path.walk.getVert (v.path.walk.length-2)))) :
    ¬ ⁅Z Rg r.start,Z Rg (q.path.walk.getVert (q.path.walk.length-2))⁆ ≤
      centralizer (stabilizer Rg q.start : Set (FreeAmalgam Rg)) := by
  intro hcentral
  let A := V Rg (v.path.walk.getVert (v.path.walk.length-2)) ⊓ Q Rg v.start
  let H := ⁅Z Rg q.start,A⁆
  obtain ⟨hlarge,_,hlower,hHZ,_,hHV⟩ := plane_long_intermediate_central_radius_displacement
    h e hz hk hb u hR v.path q r hcentral hstrict₀ hstrict
  have ht : color Rg q.edge = true := by
    have hh := adjacent_color_ne Rg q.adjacent_start
    rw [v.path.start_color] at hh
    cases he : color Rg q.edge <;> simp_all
  have hAedge : A ≤ Q Rg q.edge :=
    inf_le_right.trans (Q_le_adjacent_h Rg ht q.adjacent_start)
  have hHe : H ≤ Z Rg q.edge :=
    (commutator_mono le_rfl hAedge).trans
      (plane_edge_seed_commutator h e hz hk u hR q.path.start_color q.adjacent_shift)
  have hHc : H ≤ Z Rg q.start :=
    hHe.trans (adjacent_Z_le Rg q.path.start_color q.adjacent_shift)
  have hi := plane_long_paired_fixed_seed_central_index h e hz hk
    (by omega) u hR v.path q.edge q.adjacent_start q.cubic
    (Ltilde_le_stabilizer _ q.cubic_mem) q.endpoint_generation H hHZ hHe
    (hHV.trans (centralizer_le (Z_le_VBall Rg _ 2)))
  have htransfer := plane_long_central_intersection_transfer h e hz hk hb u hR
    v.path q.transporter q.transporter_mem (EdgePlanePairedBackwardShift.first_interior_generation h v (by omega)) H
    (q.start_eq ▸ hHc) hHV hlarge
  rw [q.start_eq] at htransfer
  let := finite_Z Rg v.start
  let : Finite H := Finite.of_injective (inclusion hHZ) (inclusion_injective _)
  have hup := relIndex_le_of_le_left htransfer (index_ne_zero_of_finite
    (H := (H ⊓ centralizer (stabilizer Rg v.start : Set (FreeAmalgam Rg))).subgroupOf H))
  rw [inf_relIndex_left] at hup
  have hupper := hup.trans hi
  change 4 ≤ (centralizer (stabilizer Rg q.start : Set (FreeAmalgam Rg))).relIndex H at hlower
  omega

theorem plane_long_exists_generated_radius_four
    (hb : 4 < sourceDistance h)
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom) :
    ∃ a a' : Vertex Rg,
      ∃ p : CriticalPath Rg (sourceGeometry h) a a',
        (Q Rg (p.walk.getVert 1) ⊔ Q Rg (p.walk.getVert 3) =
          stabilizer Rg (p.walk.getVert 2)) ∧
        (Q Rg a).relIndex (V Rg a')=4 := by
  obtain ⟨a',⟨p⟩⟩ := CriticalPath.exists_from (R := Rg)
    (geometry := sourceGeometry h) (a := alpha Rg) rfl
  by_cases hb6 : 6 < sourceDistance h
  · obtain ⟨v⟩ := plane_long_edge_paired_backward_shift
      h e hz hk hb u hR p
    obtain ⟨q,r,t,_,_,_,hact₄,hact₆⟩ := plane_long_edge_paired_terminal_radius_actions
      h e hz hk hb u hR v.path
    have small {c z : Vertex Rg}
        (w : CriticalPath Rg (sourceGeometry h) c z)
        (hh : (Q Rg c).relIndex (V Rg z) ≤ 4) :
        (Q Rg c).relIndex (V Rg z)=4 :=
      (small_opposite_radius_eq_four h e hz hk
        (by omega) w hh).2.2
    by_cases hv : 4 < (Q Rg v.start).relIndex (V Rg (p.walk.getVert (p.walk.length-2)))
    · by_cases hq : 4 < (Q Rg q.start).relIndex
          (V Rg (v.path.walk.getVert (v.path.walk.length-2)))
      · by_cases hr : 4 < (Q Rg r.start).relIndex
            (V Rg (q.path.walk.getVert (q.path.walk.length-2)))
        · have hn₄ := plane_long_shifted_intermediate_noncentral_of_strict
            h e hz hk hb6 u hR p v q r hv hq
          have hn₆ := plane_long_shifted_intermediate_noncentral_of_strict
            h e hz hk hb6 u hR v.path q r t hq hr
          let z₄ := q.path.walk.getVert (q.path.walk.length-2)
          have hi₄ : (Q Rg q.start).relIndex (V Rg z₄) ≤ 2 := by
            by_contra! hh
            exact hn₄ (hact₄ hh)
          have hi₆ : (Q Rg r.start).relIndex (V Rg z₄ ⊓ Q Rg q.start) ≤ 2 := by
            by_contra! hh
            exact hn₆ (hact₆ hh)
          have hVQ : V Rg z₄ ≤ Q Rg z₄ :=
            V_le_Q Rg (geometry := sourceGeometry h) r.path.end_color
              (by change 2 < sourceDistance h; omega)
          let := finite_stabilizer Rg z₄
          let : Finite (V Rg z₄) := Finite.of_injective
            (inclusion (hVQ.trans (fun _ hx => hx.1))) (inclusion_injective _)
          have htower := relIndex_inf_mul_relIndex (Q Rg r.start)
            (Q Rg q.start) (V Rg z₄)
          rw [inf_comm (Q Rg q.start)] at htower
          have hmono : (Q Rg r.start).relIndex (V Rg z₄) ≤
              (Q Rg r.start ⊓ Q Rg q.start).relIndex (V Rg z₄) :=
            relIndex_le_of_le_left inf_le_left index_ne_zero_of_finite
          have hupper : (Q Rg r.start).relIndex (V Rg z₄) ≤ 4 := by
            rw [←htower] at hmono
            exact hmono.trans ((Nat.mul_le_mul hi₆ hi₄).trans (by decide))
          exact ⟨_,_,r.path,EdgePlanePairedBackwardShift.first_interior_generation h r (by omega),small r.path hupper⟩
        · exact ⟨_,_,r.path,EdgePlanePairedBackwardShift.first_interior_generation h r (by omega),small r.path (Nat.le_of_not_gt hr)⟩
      · exact ⟨_,_,q.path,EdgePlanePairedBackwardShift.first_interior_generation h q (by omega),small q.path (Nat.le_of_not_gt hq)⟩
    · exact ⟨_,_,v.path,EdgePlanePairedBackwardShift.first_interior_generation h v (by omega),small v.path (Nat.le_of_not_gt hv)⟩
  · have heven := sourceDistance_even h
    rw [Nat.even_iff] at heven
    have heq : sourceDistance h=6 := by omega
    obtain ⟨q,r,t,_,_,_,_,_,hi⟩ := plane_long_edge_paired_terminal_six
      h e hz hk heq u hR p
    exact ⟨_,_,r.path,EdgePlanePairedBackwardShift.first_interior_generation h r (by omega),hi⟩
end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
