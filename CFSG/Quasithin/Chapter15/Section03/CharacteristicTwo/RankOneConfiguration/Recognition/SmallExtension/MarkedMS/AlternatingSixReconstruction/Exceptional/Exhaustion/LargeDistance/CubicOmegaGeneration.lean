module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicOmegaControl
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicSmallBackward
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicOmegaControl

/-!
# Central generation of the full omega layer in the cubic point branch

On consecutive critical four-edge paths a--z and d--c, with midpoints c
and a, let Y = U_d intersect Q_c and R1 = [Y,X_z intersect Q_a]. When the
first backward edge and Z_z generate G_a, that edge normalizes the backward
seed kernel and its order-two predecessor commutator. R1 is either trivial
or that commutator, while Z_z centralizes R1. Thus R1 is central in G_a and
belongs to the actual seed Z_a.

The noncentral-extension control alternative then places Y in the Baumann
slice at a: it normalizes Y join Z_a, and its commutator with the critical
seed is contained in Z_a. The critical index two bounds the entire moving
slice by two. A strict forward slice therefore forces central generation
at z. The already proved strict reciprocal slice on the selected nonabelian
span supplies such a path, possibly after the literal midpoint conjugation.
Transport through the original graph proves X_a = U_a C_{X_a}(G_a) at every
component vertex. Its fixed subgroup lies in the original seed orbit, so
X_a = Z_a follows here without being assumed in the preceding arguments.

The selected-path application also places R1 in both midpoint seeds and
makes it central in the original stabilizer. Whole-core and literal C.1.32
consumers retain the actual cubic projection with kernel E, the odd E/Q,
both moving covers and the original nonsylow radical. Central generation
does not itself yield the remaining MS93 (5.12) inequality or its terminal
contradiction. Plane/Sylow exclusions, natural exhaustion and both final
reconstruction outcomes remain required.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (3.3)(ii), pp.866--867, and the generating-kernel and central-generation
arguments in (5.9)--(5.12), pp.920--927; Aschbacher--Smith C.1.31--32,
pp.135--136. All transports use the original cubic graph.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement Pointwise
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
open Theory.SpecificGroups.SymmetricSix Theory.SpecificGroups.SymmetricSix.BinaryFlags
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "Rg" => edge L R
local notation "π" => CubicAction.projection h e hz hk

include h e hz hk in
/-- The selected generating edge makes the shifted full-omega kernel
commutator central in the midpoint stabilizer and contained in its seed. -/
theorem point_generating_shifted_kernel_central
    (u : S) (hR : (Rg).map π ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    {a z c d : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) a z)
    (q : CriticalPath Rg (sourceGeometry h) d c)
    (hpc : p.walk.getVert 2 = c) (hqa : q.walk.getVert 2 = a)
    (hgen : Q Rg (q.walk.getVert 1) ⊔ Z Rg z = stabilizer Rg a) :
    let Y := U Rg d ⊓ Q Rg c
    let R₁ := ⁅Y,X Rg z ⊓ Q Rg a⁆
    Q Rg (q.walk.getVert 1) ≤ normalizer (Y : Set (FreeAmalgam Rg)) ∧
      R₁ ≤ centralizer (stabilizer Rg a : Set (FreeAmalgam Rg)) ∧
      R₁ ≤ Z Rg a := by
  let t := q.walk.getVert 1
  let K := Z Rg d ⊓ Q Rg c
  let Y := U Rg d ⊓ Q Rg c
  let H := ⁅K,Q Rg a⁆
  let R₁ := ⁅Y,X Rg z ⊓ Q Rg a⁆
  have hb := point_image_distance_eq_four h e hz hk u hR
  have hl : q.walk.length = 4 := q.length_eq_b.trans hb
  have hdt : Adjacent Rg d t := by
    simpa only [SimpleGraph.Walk.getVert_zero] using
      (cosetGraph_adj Rg _ _).mp (q.walk.adj_getVert_succ (i := 0) (by omega))
  have hat : Adjacent Rg a t := by
    rw [←hqa]
    exact adjacent_symm Rg
      ((cosetGraph_adj Rg _ _).mp (q.walk.adj_getVert_succ (i := 1) (by omega)))
  have htGa : Q Rg t ≤ stabilizer Rg a := fun _ hx => hx.2 a (adjacent_symm Rg hat)
  have htGd : Q Rg t ≤ stabilizer Rg d := fun _ hx => hx.2 d (adjacent_symm Rg hdt)
  have hZct : Z Rg c ≤ Q Rg t := by
    apply Z_le_Q_of_dist_lt Rg c ((sourceGeometry h).exists_critical c q.end_color)
    rw [SimpleGraph.dist_comm,q.dist_end,hl,(sourceGeometry h).distance_constant _ q.end_color]
    change 4-1 < sourceDistance h
    omega
  have htK : Q Rg t ≤ normalizer (K : Set (FreeAmalgam Rg)) := by
    rw [show K = Z Rg d ⊓ centralizer (Z Rg c : Set (FreeAmalgam Rg)) from
      (critical_seed_centralizer_intersection h e q).symm]
    exact edge_preserves_seed_fixer h e hz hk u hR q.start_color hdt _ hZct
  have htY : Q Rg t ≤ normalizer (Y : Set (FreeAmalgam Rg)) := by
    have he : Y = U Rg d ⊓ K := by
      change U Rg d ⊓ Q Rg c = U Rg d ⊓ (Z Rg d ⊓ Q Rg c)
      rw [←inf_assoc,inf_eq_left.mpr (DistanceEight.U_le_Z Rg d)]
    rw [he]
    exact (le_inf (htGd.trans (U_normalized d)) htK).trans inf_normalizer_le_normalizer_inf
  have htH : Q Rg t ≤ normalizer (H : Set (FreeAmalgam Rg)) := by
    intro x hx
    apply mem_normalizer_iff_map_conj_eq.mpr
    rw [map_commutator,mem_normalizer_iff_map_conj_eq.mp (htK hx),
      mem_normalizer_iff_map_conj_eq.mp ((htGa.trans (Q_normalized Rg a)) hx)]
  have hd := point_shifted_omega_kernel_line h e hz hk u hR p q hpc hqa
  have htR : Q Rg t ≤ centralizer (R₁ : Set (FreeAmalgam Rg)) := by
    rcases hd.2.2.1 with hzero | heq
    · rw [show R₁ = ⊥ from hzero]
      exact le_centralizer_iff.mpr bot_le
    · rw [show R₁ = H from heq]
      exact htH.trans (normalizer_le_centralizer_of_card_two H hd.1)
  have hRz : R₁ ≤ X Rg z := hd.2.2.2.1.trans inf_le_right |>.trans
    ((DistanceEight.U_le_Z Rg z).trans ((sourceGeometry h).omega_bound z p.end_color (by
      rw [(sourceGeometry h).distance_constant _ p.end_color]; exact sourceDistance_pos h)))
  have hzR : Z Rg z ≤ centralizer (R₁ : Set (FreeAmalgam Rg)) := by
    exact (((Z_le_VBall Rg z 2).trans
      ((sourceGeometry h).V_le_Q (distance_gt_two h e hz hk) z p.end_color)).trans (Q_le_centralizer_X Rg z)).trans
      (centralizer_le hRz)
  have hcentral : R₁ ≤ centralizer (stabilizer Rg a : Set (FreeAmalgam Rg)) := by
    apply le_centralizer_iff.mp
    rw [←hgen]
    exact sup_le htR hzR
  have hRa : R₁ ≤ X Rg a := hd.2.2.2.2.2.2.2.1.trans inf_le_left
  exact ⟨htY,hcentral,(le_inf hRa hcentral).trans (omega_fixed_le_seed h a p.start_color)⟩


include h e hz hk in
/-- The literal full-omega control bound places the backward moving
kernel in the midpoint Baumann slice and bounds the full moving index. -/
theorem point_generating_shifted_slice_of_control
    (u : S) (hR : (Rg).map π ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    {z c d : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z)
    (q : CriticalPath Rg (sourceGeometry h) d c)
    (hpc : p.walk.getVert 2 = c) (hqa : q.walk.getVert 2 = alpha Rg)
    (hgen : Q Rg (q.walk.getVert 1) ⊔ Z Rg z = stabilizer Rg (alpha Rg))
    (hcontrol :
      ⁅U Rg d ⊓ Q Rg c,X Rg z⁆ ≤ ⁅Z Rg (alpha Rg),Z Rg z⁆ ⊔
        ⁅U Rg d ⊓ Q Rg c,X Rg z ⊓ Q Rg (alpha Rg)⁆ ∧
      X Rg z ≤ normalizer (((U Rg d ⊓ Q Rg c) ⊔ Z Rg (alpha Rg) :
        Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg))) :
    U Rg d ⊓ Q Rg c ≤ B Rg (alpha Rg) ((sourceGeometry h).Z_normal _) ∧
      (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex (U Rg d) ≤ 2 := by
  let Y := U Rg d ⊓ Q Rg c
  let T := Y ⊔ Z Rg (alpha Rg)
  have hb := distance_gt_two h e hz hk
  have hb4 := point_image_distance_eq_four h e hz hk u hR
  have hl : q.walk.length = 4 := q.length_eq_b.trans hb4
  have hda : (cosetGraph Rg).dist d (alpha Rg) ≤ 2 := by
    rw [←hqa,q.dist_start (by omega)]
  have hYV : Y ≤ V Rg (alpha Rg) := inf_le_left.trans
    ((DistanceEight.U_le_Z Rg d).trans (le_iSup_of_le d (le_iSup_of_le hda le_rfl)))
  have hZzX : Z Rg z ≤ X Rg z := (sourceGeometry h).omega_bound z p.end_color (by
    rw [(sourceGeometry h).distance_constant _ p.end_color]; exact sourceDistance_pos h)
  obtain ⟨htY,_,hRseed⟩ := point_generating_shifted_kernel_central h e hz hk u hR p q hpc hqa hgen
  have hYcomm : ⁅Y,Z Rg z⁆ ≤ Z Rg (alpha Rg) :=
    (commutator_mono le_rfl hZzX).trans
      (hcontrol.1.trans (sup_le (critical_seed_commutator_le h p) hRseed))
  have htG : Q Rg (q.walk.getVert 1) ≤ stabilizer Rg (alpha Rg) :=
    le_sup_left.trans hgen.le
  have hTnormal : stabilizer Rg (alpha Rg) ≤ normalizer (T : Set (FreeAmalgam Rg)) := by
    rw [←hgen]
    exact sup_le ((le_inf htY (htG.trans (Z_normalized Rg _))).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)) (hZzX.trans hcontrol.2)
  have hTcomm : ⁅T,Z Rg z⁆ ≤ Z Rg (alpha Rg) :=
    commutator_sup_le_of_relative_normal (stabilizer Rg (alpha Rg))
      Y (Z Rg (alpha Rg)) (Z Rg z) (Z Rg (alpha Rg))
      (Z_normalized Rg _) (hYV.trans ((sourceGeometry h).V_local _ rfl hb))
      (Z_le_stabilizer Rg _) hYcomm (critical_seed_commutator_le h p)
  have hYB : Y ≤ B Rg (alpha Rg) ((sourceGeometry h).Z_normal _) :=
    le_sup_left.trans (normalized_radius_le_slice_of_critical_commutator h e hz hb p T
      (sup_le hYV (Z_le_VBall Rg _ 2)) hTnormal hTcomm)
  let := finite_Z Rg d
  let : Finite (U Rg d) := Finite.of_injective
    (inclusion (DistanceEight.U_le_Z Rg d)) (inclusion_injective _)
  refine ⟨hYB,?_⟩
  have hYindex : Y.relIndex (U Rg d) ≤ 2 := by
    rw [show Y = U Rg d ⊓ Q Rg c from rfl,inf_relIndex_left]
    exact (relIndex_le_of_le_right (DistanceEight.U_le_Z Rg d) index_ne_zero_of_finite).trans_eq
      (point_image_critical_indices_two h e hz hk u hR q).1
  exact (relIndex_le_of_le_left hYB index_ne_zero_of_finite).trans hYindex

include h e hz hk in
/-- A strict forward slice excludes the noncentral-extension alternative
on its actual generating backward configuration. -/
theorem point_strict_forward_omega_generation
    (u : S) (hR : (Rg).map π ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    {z : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z)
    (hindex : 2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (p.walk.getVert 2))) :
    X Rg z = U Rg z ⊔
      (X Rg z ⊓ centralizer (stabilizer Rg z : Set (FreeAmalgam Rg))) := by
  have hb := distance_gt_two h e hz hk
  have hb4 := point_image_distance_eq_four h e hz hk u hR
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb4
  obtain ⟨d,t,x,hx,hxd,hat,hdt,hgen,q,hq1,hover⟩ :=
    full_point_backward_step_of_strict_forward h e hz hk u
      (full_point_image_of_contained h e hz hk u hR) p hindex
  have hpc : p.walk.getVert 2 = p.walk.getVert (p.walk.length-2) := by rw [hl]
  have hqa : q.walk.getVert 2 = alpha Rg := by
    simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using hover 0 (Nat.zero_le _)
  have hgen' : Q Rg (q.walk.getVert 1) ⊔ Z Rg z = stabilizer Rg (alpha Rg) := by
    rwa [hq1]
  rcases point_shifted_omega_generation_or_control h e hz hk u hR p q hpc hqa with hcentral | hcontrol
  · exact hcentral
  have hsmall := (point_generating_shifted_slice_of_control h e hz hk u hR p q hpc hqa hgen' hcontrol).2
  have hBmap : (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).map
      (MulAut.conj x⁻¹).toMonoidHom = B Rg (alpha Rg) ((sourceGeometry h).Z_normal _) :=
    mem_normalizer_iff_map_conj_eq.mp (Escape.Propagation.Rigidity.B_normalized
      (geometry := sourceGeometry h) hb (alpha Rg) rfl ((stabilizer Rg (alpha Rg)).inv_mem hx))
  rw [←hxd,U_act,←hBmap,relIndex_map_map_of_injective _ _ (MulAut.conj x⁻¹).injective] at hsmall
  omega

omit [Finite G] in
private theorem omega_generation_transport
    {a b : Vertex Rg} (ha : color Rg a = false) (hb : color Rg b = false)
    (hgen : X Rg a = U Rg a ⊔
      (X Rg a ⊓ centralizer (stabilizer Rg a : Set (FreeAmalgam Rg)))) :
    X Rg b = U Rg b ⊔
      (X Rg b ⊓ centralizer (stabilizer Rg b : Set (FreeAmalgam Rg))) := by
  obtain ⟨x,rfl⟩ := exists_mVertex_of_color Rg ha
  obtain ⟨y,rfl⟩ := exists_mVertex_of_color Rg hb
  let g := x⁻¹*y
  have he : act Rg g (mVertex Rg x) = mVertex Rg y := by
    simp only [g,act_mVertex,mul_inv_cancel_left]
  have hm := congrArg (Subgroup.map (MulAut.conj g⁻¹).toMonoidHom) hgen
  rw [Subgroup.map_sup,←map_inf_centralizer_of_injective _ (MulAut.conj g⁻¹).injective,
    ←X_act,←U_act,←stabilizer_act,he] at hm
  exact hm

include h e hz hk in
/-- The point-core branch forces central generation at every original
component vertex, using the proved strict reciprocal slice. -/
theorem point_omega_central_generation
    (u : S) (hR : (Rg).map π ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    (a : Vertex Rg) (ha : color Rg a = false) :
    X Rg a = U Rg a ⊔
      (X Rg a ⊓ centralizer (stabilizer Rg a : Set (FreeAmalgam Rg))) := by
  obtain ⟨z,p,hcard,hcentral,hradius⟩ := point_image_selected_span_radius_line h e hz hk u hR
  have hnon : ⁅localZSpan Rg (p.walk.getVert 2) (alpha Rg),
      localZSpan Rg (p.walk.getVert 2) (alpha Rg)⁆ ≠ ⊥ := by
    intro he
    rw [he,card_bot] at hcard
    omega
  rcases point_selected_reciprocal_slice_alternative h e hz hk u hR p hnon with hforward | hreverse
  · exact omega_generation_transport p.end_color ha
      (point_strict_forward_omega_generation h e hz hk u hR p hforward)
  obtain ⟨_,x,hx,q,_,hqa,_⟩ :=
    selected_span_conjugate_critical_path h (distance_gt_two h e hz hk) p hnon
  have hqindex : 2 < (B Rg (p.walk.getVert 2) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (q.walk.getVert 2)) := by rwa [hqa]
  obtain ⟨g,hg⟩ := exists_mVertex_of_color Rg q.start_color
  have hbase : act Rg g⁻¹ (p.walk.getVert 2) = alpha Rg := by
    rw [hg,act_mVertex,mul_inv_cancel]
    rfl
  have hs : 2 < (B Rg (act Rg g⁻¹ (p.walk.getVert 2))
      ((sourceGeometry h).Z_normal _)).relIndex (U Rg ((q.act g⁻¹).walk.getVert 2)) := by
    simp only [CriticalPath.act,actWalk_getVert]
    rw [Escape.PairingControl.FirstPairing.B_act (distance_gt_two h e hz hk) g⁻¹ _ q.start_color,
      U_act,relIndex_map_map_of_injective _ _ (MulAut.conj (g⁻¹)⁻¹).injective]
    exact hqindex
  have hq0 : ∃ q0 : CriticalPath Rg (sourceGeometry h)
      (act Rg g⁻¹ (p.walk.getVert 2)) (act Rg g⁻¹ (act Rg x (p.walk.getVert 2))),
      2 < (B Rg (act Rg g⁻¹ (p.walk.getVert 2)) ((sourceGeometry h).Z_normal _)).relIndex
        (U Rg (q0.walk.getVert 2)) := ⟨q.act g⁻¹,hs⟩
  rw [hbase] at hq0
  obtain ⟨q0,hq0⟩ := hq0
  exact omega_generation_transport q0.end_color ha
    (point_strict_forward_omega_generation h e hz hk u hR q0 hq0)

include h e hz hk in
/-- In the point-core branch the full omega layer equals its seed orbit.
This follows from the source geometry and is not a change of conventions. -/
theorem point_omega_eq_seed
    (u : S) (hR : (Rg).map π ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    (a : Vertex Rg) (ha : color Rg a = false) : X Rg a = Z Rg a :=
  omega_eq_seed_of_central_generation h a ha (point_omega_central_generation h e hz hk u hR a ha)


include h e hz hk in
/-- The selected span and the shifted kernel retain their original paths.
The shifted line is central at the original vertex and lies in both seeds. -/
theorem point_image_selected_central_omega
    (u : S) (hR : (Rg).map π ≤ pointCore.map (MulAut.conj u).toMonoidHom) :
    ∃ z, ∃ p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z,
      ∃ d, ∃ q : CriticalPath Rg (sourceGeometry h) d
        (p.walk.getVert (p.walk.length-2)),
      q.walk.getVert 2 = alpha Rg ∧
      let c := p.walk.getVert (p.walk.length-2)
      let P := localZSpan Rg c (alpha Rg)
      let H := ⁅Z Rg d ⊓ Q Rg c,Q Rg (alpha Rg)⁆
      let R₁ := ⁅U Rg d ⊓ Q Rg c,X Rg z ⊓ Q Rg (alpha Rg)⁆
      Nat.card (⁅P,P⁆ : Subgroup (FreeAmalgam Rg)) = 2 ∧
      ⁅P,P⁆ ≤ centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg)) ∧
      ⁅P,V Rg (alpha Rg)⁆ = ⁅P,P⁆ ∧
      Nat.card H = 2 ∧ (R₁ = ⊥ ∨ R₁ = H) ∧
      R₁ ≤ Z Rg (alpha Rg) ⊓ Z Rg c ∧
      R₁ ≤ centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg)) ∧
      R₁ = ⁅U Rg d ⊓ Q Rg c,Z Rg z ⊓ Q Rg (alpha Rg)⁆ ∧
      (R₁ ≠ ⊥ → H = ⁅Z Rg z ⊓ Q Rg (alpha Rg),Q Rg c⁆) := by
  obtain ⟨hb,z,p,_,d,t,x,hx,hxd,_,_,hgen,q,hq1,hover,_,_,hcard,hcentral⟩ :=
    point_image_small_central_generating_configuration h e hz hk u hR
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hq2 : q.walk.getVert 2 = alpha Rg := by
    simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using hover 0 (Nat.zero_le _)
  have hpc : p.walk.getVert 2 = p.walk.getVert (p.walk.length-2) := by rw [hl]
  let qr : CriticalPath Rg (sourceGeometry h) (p.walk.getVert (p.walk.length-2)) d :=
    ⟨q.end_color,q.walk.reverse,
      by rw [SimpleGraph.Walk.length_reverse,q.shortest,SimpleGraph.dist_comm],
      critical_reverse Rg (sourceGeometry h) (sourceEdgeCentralizer h e) d q.start_color
        (by rw [(sourceGeometry h).distance_constant _ q.start_color]; exact sourceDistance_pos h)
        _ q.end_color q.critical⟩
  have hqr2 : qr.walk.getVert 2 = alpha Rg := by
    change q.walk.reverse.getVert 2 = _
    rw [SimpleGraph.Walk.getVert_reverse,show q.walk.length = 4 from q.length_eq_b.trans hb]
    exact hq2
  have hd : d ∈ Set.range (fun g : stabilizer Rg (alpha Rg) =>
      act Rg g (p.walk.getVert (p.walk.length-2))) := by
    refine ⟨⟨x,hx⟩,?_⟩
    simpa only [hl,Nat.reduceSub] using hxd
  have hcent : ⁅Z Rg (p.walk.getVert (p.walk.length-2)),Z Rg d⁆ ≤
      centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg)) := by
    rwa [commutator_comm]
  have hs := point_selected_span_radius_commutator h e hz hk u hR qr hqr2 hd hcent
  rw [commutator_comm (Z Rg (p.walk.getVert (p.walk.length-2))) (Z Rg d)] at hs
  have hgen' : Q Rg (q.walk.getVert 1) ⊔ Z Rg z = stabilizer Rg (alpha Rg) := by
    rwa [hq1]
  obtain ⟨_,hRc,hRZ⟩ := point_generating_shifted_kernel_central h e hz hk u hR p q hpc hq2 hgen'
  obtain ⟨hH,_,hRalt,_,_,_,hRseed,hRX,hRident⟩ :=
    point_shifted_omega_kernel_line h e hz hk u hR p q hpc hq2
  have hRmid := hRX.trans inf_le_right
  rw [point_omega_eq_seed h e hz hk u hR _ q.end_color] at hRmid
  refine ⟨z,p,d,q,hq2,?_,hs.2.trans_le hcentral,hs.1.trans hs.2.symm,
    hH,hRalt,le_inf hRZ hRmid,hRc,hRseed,hRident⟩
  rw [hs.2]
  exact hcard

omit hk in
include h e hz in
/-- Whole-core application: the point branch now has centrally generated
full omega layers, equal to the actual seed orbits, on the original cubic graph. -/
theorem coreExhaustion_or_cubic_central_omega :
    CoreExhaustion L R ∨ ∃ hk : layerKernel L R = extensionKernel h,
      Function.Surjective (CubicAction.projection h e hz hk) ∧
      2 < sourceDistance h ∧
      (∀ a : Vertex Rg, color Rg a = false →
        Nat.card (U Rg a) = 16 ∨ Nat.card (U Rg a) = 32) ∧
      ∃ u : S,
        ((Rg).map (CubicAction.projection h e hz hk) =
            pointCore.map (MulAut.conj u).toMonoidHom ∧
          sourceDistance h = 4 ∧
          (∀ a : Vertex Rg, color Rg a = false →
            X Rg a = U Rg a ⊔
              (X Rg a ⊓ centralizer (stabilizer Rg a : Set (FreeAmalgam Rg))) ∧
            X Rg a = Z Rg a) ∧
          (∃ z, ∃ p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z,
            ∃ d, ∃ q : CriticalPath Rg (sourceGeometry h) d
              (p.walk.getVert (p.walk.length-2)),
            q.walk.getVert 2 = alpha Rg ∧
            let c := p.walk.getVert (p.walk.length-2)
            let P := localZSpan Rg c (alpha Rg)
            let H := ⁅Z Rg d ⊓ Q Rg c,Q Rg (alpha Rg)⁆
            let R₁ := ⁅U Rg d ⊓ Q Rg c,X Rg z ⊓ Q Rg (alpha Rg)⁆
            Nat.card (⁅P,P⁆ : Subgroup (FreeAmalgam Rg)) = 2 ∧
            ⁅P,P⁆ ≤ centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg)) ∧
            ⁅P,V Rg (alpha Rg)⁆ = ⁅P,P⁆ ∧
            Nat.card H = 2 ∧ (R₁ = ⊥ ∨ R₁ = H) ∧
            R₁ ≤ Z Rg (alpha Rg) ⊓ Z Rg c ∧
            R₁ ≤ centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg)) ∧
            R₁ = ⁅U Rg d ⊓ Q Rg c,Z Rg z ⊓ Q Rg (alpha Rg)⁆ ∧
            (R₁ ≠ ⊥ → H = ⁅Z Rg z ⊓ Q Rg (alpha Rg),Q Rg c⁆))) ∨
        (Rg).map (CubicAction.projection h e hz hk) =
          D.map (MulAut.conj u).toMonoidHom ∨
        (Rg).map (CubicAction.projection h e hz hk) =
          borel.map (MulAut.conj u).toMonoidHom := by
  rcases coreExhaustion_or_cubic_radical_cases h e hz with
    hx | ⟨hk,hs,hb,hcovers,u,hpoint | hplane | hsylow⟩
  · exact Or.inl hx
  · exact Or.inr ⟨hk,hs,hb,hcovers,u,Or.inl ⟨hpoint.2,hpoint.1,
      fun a ha => ⟨point_omega_central_generation h e hz hk u hpoint.2.le a ha,
        point_omega_eq_seed h e hz hk u hpoint.2.le a ha⟩,
      point_image_selected_central_omega h e hz hk u hpoint.2.le⟩⟩
  · exact Or.inr ⟨hk,hs,hb,hcovers,u,Or.inr (Or.inl hplane)⟩
  · exact Or.inr ⟨hk,hs,hb,hcovers,u,Or.inr (Or.inr hsylow)⟩

omit hk in
include h e hz in
/-- Literal C.1.32 application of central omega generation, preserving the
original projection, both moving covers and the plane/Sylow alternatives. -/
theorem rankTwo_or_cubic_central_omega :
    RankTwoAlternatives L R ∨ ∃ hk : layerKernel L R = extensionKernel h,
      Function.Surjective (CubicAction.projection h e hz hk) ∧
      2 < sourceDistance h ∧
      (∀ a : Vertex Rg, color Rg a = false →
        Nat.card (U Rg a) = 16 ∨ Nat.card (U Rg a) = 32) ∧
      ∃ u : S,
        ((Rg).map (CubicAction.projection h e hz hk) =
            pointCore.map (MulAut.conj u).toMonoidHom ∧
          sourceDistance h = 4 ∧
          (∀ a : Vertex Rg, color Rg a = false →
            X Rg a = U Rg a ⊔
              (X Rg a ⊓ centralizer (stabilizer Rg a : Set (FreeAmalgam Rg))) ∧
            X Rg a = Z Rg a) ∧
          (∃ z, ∃ p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z,
            ∃ d, ∃ q : CriticalPath Rg (sourceGeometry h) d
              (p.walk.getVert (p.walk.length-2)),
            q.walk.getVert 2 = alpha Rg ∧
            let c := p.walk.getVert (p.walk.length-2)
            let P := localZSpan Rg c (alpha Rg)
            let H := ⁅Z Rg d ⊓ Q Rg c,Q Rg (alpha Rg)⁆
            let R₁ := ⁅U Rg d ⊓ Q Rg c,X Rg z ⊓ Q Rg (alpha Rg)⁆
            Nat.card (⁅P,P⁆ : Subgroup (FreeAmalgam Rg)) = 2 ∧
            ⁅P,P⁆ ≤ centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg)) ∧
            ⁅P,V Rg (alpha Rg)⁆ = ⁅P,P⁆ ∧
            Nat.card H = 2 ∧ (R₁ = ⊥ ∨ R₁ = H) ∧
            R₁ ≤ Z Rg (alpha Rg) ⊓ Z Rg c ∧
            R₁ ≤ centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg)) ∧
            R₁ = ⁅U Rg d ⊓ Q Rg c,Z Rg z ⊓ Q Rg (alpha Rg)⁆ ∧
            (R₁ ≠ ⊥ → H = ⁅Z Rg z ⊓ Q Rg (alpha Rg),Q Rg c⁆))) ∨
        (Rg).map (CubicAction.projection h e hz hk) =
          D.map (MulAut.conj u).toMonoidHom ∨
        (Rg).map (CubicAction.projection h e hz hk) =
          borel.map (MulAut.conj u).toMonoidHom :=
  (coreExhaustion_or_cubic_central_omega h e hz).imp (rankTwo_of_exhaustion h e hz) id

end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
