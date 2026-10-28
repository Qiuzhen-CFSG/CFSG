module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneForwardKernel

import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneBackward

/-!
# Exact first-edge actions and their radius kernels

In the original cubic graph at critical distance four, let a--v--c--t--z
be an escaping small critical path. Put Y = V_a intersect Q_c and
F = Z_z intersect Q_a. The full first-edge orbit P = <Z_a^{G_v}> lies in Y
and fixes F. The full-seed critical-kernel centralizer theorem then gives
[P,Z_z] = [Z_a,Z_z], with literal endpoint image of order two. Its fixed
subgroup on the entire endpoint seed is exactly F.

The centralizer K = C_Y(F) also has endpoint image two. It contains
Y intersect Q_z, and comparison of the quotient images gives
K = P (Y intersect Q_z). Since Y has endpoint image four, K has index two
in Y. Its commutator with the entire endpoint seed is the same critical
line. The image calculation uses the actual two-subgroup theorem across
the odd extension kernel; the projection kernel remains E, not Q.

On the original paired displaced paths these conclusions hold for both
radii and both first-edge orbits. The original critical line supplements
the opposite full kernel, so [P,F_opposite] and [K,F_opposite] are also
that line. The full radius retains its larger opposite-kernel commutator.
The whole-core and literal C.1.32 applications preserve the selected
conjugator, exact path distances, both covers of orders sixteen and
thirty-two, all central attachments and the original radical.

This isolates the remaining radius action beyond its first-edge orbit.
It does not exclude all residual rotations or prove the terminal
contradiction, other image/distance cases or either core exhaustion.
The internal import reuses the existing central-attachment commutator
calculation without changing its public boundary.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (3.3)(ii), (5.2), and the comparisons in (5.12)(1),(3), printed
pp.866--867,912--914,924--927; Aschbacher--Smith C.1.31--32, pp.135--136.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.SpecificGroups.SymmetricSix Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open scoped Pointwise IsMulCommutative commutatorElement
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
/-- The whole first-edge orbit has the original critical action, exact full
fixed kernel and endpoint image of order two. -/
theorem plane_radius_first_edge_action
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    (hb4 : sourceDistance h = 4)
    (hsmall : ∀ a z (_p : CriticalPath Rg (sourceGeometry h) a z),
      (Q Rg z).relIndex (Z Rg a) < 4)
    {a z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (hescape : ¬ ⁅V Rg a ⊓ Q Rg (p.walk.getVert 2),Z Rg z⁆ ≤ Z Rg a) :
    let P := localZSpan Rg a (p.walk.getVert 1)
    let Y := V Rg a ⊓ Q Rg (p.walk.getVert 2)
    let F := Z Rg z ⊓ Q Rg a
    P ≤ Y ∧ ⁅P,F⁆ = ⊥ ∧
      Z Rg z ⊓ centralizer (P : Set (FreeAmalgam Rg)) = F ∧
      ⁅P,Z Rg z⁆ = ⁅Z Rg a,Z Rg z⁆ ∧
      (Q Rg z).relIndex P = 2 := by
  let c := p.walk.getVert 2
  let v := p.walk.getVert 1
  let t := p.walk.getVert 3
  let P := localZSpan Rg a v
  let Y := V Rg a ⊓ Q Rg c
  let F := Z Rg z ⊓ Q Rg a
  have hb := distance_gt_two h e hz hk
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb4
  have hav : Adjacent Rg a v := by
    apply (cosetGraph_adj Rg _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using
      p.walk.adj_getVert_succ (i := 0) (by omega)
  have hcv : Adjacent Rg c v := adjacent_symm Rg
    ((cosetGraph_adj Rg _ _).mp (p.walk.adj_getVert_succ (i := 1) (by omega)))
  have hct : Adjacent Rg c t :=
    (cosetGraph_adj Rg _ _).mp (p.walk.adj_getVert_succ (i := 2) (by omega))
  have hzt : Adjacent Rg z t := by
    have hh := p.walk.adj_getVert_succ (i := 3) (by omega)
    rw [show 3+1=p.walk.length by omega,p.walk.getVert_length] at hh
    exact adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp hh)
  have hv : color Rg v = true := by
    have hh := adjacent_color_ne Rg hav
    rw [p.start_color] at hh
    cases he : color Rg v <;> simp_all
  have ht : color Rg t = true := by
    have hh := adjacent_color_ne Rg hzt
    rw [p.end_color] at hh
    cases he : color Rg t <;> simp_all
  have hPY : P ≤ Y := by
    apply iSup_le
    intro g
    have hgw : Adjacent Rg (act Rg g a) v := by
      have hh := (adjacent_act_iff Rg (g : FreeAmalgam Rg) _ _).mpr hav
      rwa [show act Rg g v = v from g.property] at hh
    have common {x : Vertex Rg} (hx : Adjacent Rg x v) :
        (cosetGraph Rg).dist (act Rg g a) x ≤ 2 := by
      have h₁ := SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj Rg _ _).mpr hgw)
      have h₂ := SimpleGraph.dist_eq_one_iff_adj.mpr
        ((cosetGraph_adj Rg _ _).mpr (adjacent_symm Rg hx))
      have hh := (cosetGraph_connected Rg).dist_triangle
        (u := act Rg g a) (v := v) (w := x)
      omega
    refine le_inf (le_iSup_of_le (act Rg g a) (le_iSup_of_le (common hav) le_rfl)) ?_
    have hw : color Rg (act Rg g a) = false := by
      rw [action_preserves_color,p.start_color]
    apply Z_le_Q_of_dist_lt Rg _ ((sourceGeometry h).exists_critical _ hw)
    rw [(sourceGeometry h).distance_constant _ hw]
    exact lt_of_le_of_lt (common hcv) hb
  have hPG : P ≤ stabilizer Rg z :=
    (hPY.trans inf_le_right).trans ((Q_le_adjacent_h Rg ht hct).trans
      (fun _ hx => hx.2 _ (adjacent_symm Rg hzt)))
  have hAP : Z Rg a ≤ P := Z_le_localZSpan Rg _ _
  have hPF : ⁅P,F⁆ = ⊥ := (commutator_comm P F).trans
    (plane_radius_first_edge_orbit_fixed h e hz hk u hR hb4 hsmall p hescape)
  have hfix : P ≤ centralizer (F : Set (FreeAmalgam Rg)) :=
    commutator_eq_bot_iff_le_centralizer.mp hPF
  have hcomm : ⁅P,Z Rg z⁆ = ⁅Z Rg a,Z Rg z⁆ :=
    le_antisymm (small_critical_kernel_commutator h e hz hk p (hsmall _ _ p) P hPG hfix)
      (commutator_mono hAP le_rfl)
  let pr := CriticalPath.ofPair (geometry := sourceGeometry h) p.end_color
    (critical_reverse Rg (sourceGeometry h) (sourceEdgeCentralizer h e)
      a p.start_color (by
        rw [(sourceGeometry h).distance_constant _ p.start_color]
        exact sourceDistance_pos h) z p.end_color p.critical)
  have hfixed : Z Rg z ⊓ centralizer (P : Set (FreeAmalgam Rg)) = F := by
    apply le_antisymm
    · exact (inf_le_inf_left _ (centralizer_le hAP)).trans_eq
        (critical_seed_centralizer_intersection h e pr)
    · exact le_inf inf_le_left (le_centralizer_iff.mp hfix)
  let := finite_Z Rg z
  let : Finite (U Rg z) := Finite.of_injective
    (inclusion (DistanceEight.U_le_Z Rg z)) (inclusion_injective _)
  let := finite_stabilizer Rg z
  let : Finite P := Finite.of_injective (inclusion hPG) (inclusion_injective _)
  have hindex : (centralizer (P : Set (FreeAmalgam Rg))).relIndex (U Rg z) ≤ 2 :=
    ((relIndex_le_of_le_left (le_centralizer_iff.mp hfix) index_ne_zero_of_finite).trans
      (relIndex_le_of_le_right (DistanceEight.U_le_Z Rg z) index_ne_zero_of_finite)).trans_eq
        (by rw [show F = Z Rg z ⊓ Q Rg a from rfl,inf_relIndex_left]
            exact (small_critical_indices h e hz hk p (hsmall _ _ p)).2)

  have htwo : IsPGroup 2 P :=
    (Q_isPGroup Rg h.relative_radical.isPGroup h.relative_radical.twoCore_le a
      p.start_color).to_le ((hPY.trans inf_le_left).trans
        ((sourceGeometry h).V_le_Q hb a p.start_color))
  have hupper := moving_small_fixed_index_image h e hz hk p.end_color P hPG htwo hindex
  have hlower := relIndex_le_of_le_right (H := Q Rg z) hAP index_ne_zero_of_finite
  rw [(small_critical_indices h e hz hk p (hsmall _ _ p)).1] at hlower
  exact ⟨hPY,hPF,hfixed,hcomm,le_antisymm hupper hlower⟩


private theorem equal_two_images_supplement {J : Type*} [Group J]
    (P K N : Subgroup J) (hPK : P ≤ K) (hKN : K ≤ normalizer (N : Set J))
    (hP : N.relIndex P = 2) (hK : N.relIndex K = 2) :
    P ⊔ (K ⊓ N) = K := by
  let D := K ⊓ N
  have hND : K ≤ normalizer (D : Set J) :=
    (le_inf K.le_normalizer hKN).trans inf_normalizer_le_normalizer_inf
  let _ : (D.subgroupOf K).Normal := normal_subgroupOf_of_le_normalizer hND
  have hi : D.relIndex P = 2 := by
    change (K ⊓ N).relIndex P = 2
    rw [inf_comm,←relIndex_inf_mul_relIndex,inf_eq_right.mpr hPK,
      relIndex_eq_one.mpr hPK,mul_one]
    exact hP
  have hs := relIndex_sup_left (P.subgroupOf K) (D.subgroupOf K)
  rw [←subgroupOf_sup inf_le_left hPK,
    relIndex_subgroupOf (sup_le inf_le_left hPK),relIndex_subgroupOf hPK,hi] at hs
  have hm := relIndex_mul_relIndex D (D ⊔ P) K le_sup_left (sup_le inf_le_left hPK)
  rw [hs,show D.relIndex K = 2 by rw [inf_relIndex_left]; exact hK] at hm
  have he : (D ⊔ P).relIndex K = 1 := by omega
  exact (sup_comm P D).trans
    (le_antisymm (sup_le inf_le_left hPK) (relIndex_eq_one.mp he))

include h e hz hk in
/-- The full reverse-kernel centralizer in the escaping radius is precisely
the first-edge orbit joined with the endpoint two-core intersection. It has
index two in the radius, and its whole endpoint commutator is the critical line. -/
theorem plane_radius_forward_action_kernel
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    (hb4 : sourceDistance h = 4)
    (hsmall : ∀ a z (_p : CriticalPath Rg (sourceGeometry h) a z),
      (Q Rg z).relIndex (Z Rg a) < 4)
    {a z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (hescape : ¬ ⁅V Rg a ⊓ Q Rg (p.walk.getVert 2),Z Rg z⁆ ≤ Z Rg a) :
    let P := localZSpan Rg a (p.walk.getVert 1)
    let Y := V Rg a ⊓ Q Rg (p.walk.getVert 2)
    let F := Z Rg z ⊓ Q Rg a
    let K := Y ⊓ centralizer (F : Set (FreeAmalgam Rg))
    K = P ⊔ (Y ⊓ Q Rg z) ∧ K.relIndex Y = 2 ∧
      ⁅K,Z Rg z⁆ = ⁅Z Rg a,Z Rg z⁆ := by
  let c := p.walk.getVert 2
  let t := p.walk.getVert 3
  let P := localZSpan Rg a (p.walk.getVert 1)
  let Y := V Rg a ⊓ Q Rg c
  let F := Z Rg z ⊓ Q Rg a
  let K := Y ⊓ centralizer (F : Set (FreeAmalgam Rg))
  have hb := distance_gt_two h e hz hk
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb4
  have hct : Adjacent Rg c t :=
    (cosetGraph_adj Rg _ _).mp (p.walk.adj_getVert_succ (i := 2) (by omega))
  have hzt : Adjacent Rg z t := by
    have hh := p.walk.adj_getVert_succ (i := 3) (by omega)
    rw [show 3+1=p.walk.length by omega,p.walk.getVert_length] at hh
    exact adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp hh)
  have ht : color Rg t = true := by
    have hh := adjacent_color_ne Rg hzt
    rw [p.end_color] at hh
    cases he : color Rg t <;> simp_all
  obtain ⟨hPY,hPF,hfixed,hcomm,hPi⟩ :=
    plane_radius_first_edge_action h e hz hk u hR hb4 hsmall p hescape
  have hPK : P ≤ K := le_inf hPY (commutator_eq_bot_iff_le_centralizer.mp hPF)
  have hAP : Z Rg a ≤ P := Z_le_localZSpan Rg _ _
  have hYt : Y ≤ Q Rg (p.walk.getVert (p.walk.length-1)) := by
    rw [hl]
    exact inf_le_right.trans (Q_le_adjacent_h Rg ht hct)
  have hYG : Y ≤ stabilizer Rg z := by
    have hh : Y ≤ Q Rg t := by simpa only [hl,Nat.reduceSub] using hYt
    exact hh.trans (fun _ hx => hx.2 _ (adjacent_symm Rg hzt))
  have hKG : K ≤ stabilizer Rg z := inf_le_left.trans hYG
  have hYi : (Q Rg z).relIndex Y = 4 :=
    (plane_radius_kernel_indices_four h e hz hk u hR p (hsmall _ _ p)
      Y inf_le_left hYt (hAP.trans hPY) hescape).1
  have hfix : K ≤ centralizer (F : Set (FreeAmalgam Rg)) := inf_le_right
  let := finite_Z Rg z
  let : Finite (U Rg z) := Finite.of_injective
    (inclusion (DistanceEight.U_le_Z Rg z)) (inclusion_injective _)
  let := finite_stabilizer Rg z
  let : Finite K := Finite.of_injective (inclusion hKG) (inclusion_injective _)
  have hindex : (centralizer (K : Set (FreeAmalgam Rg))).relIndex (U Rg z) ≤ 2 :=
    ((relIndex_le_of_le_left (le_centralizer_iff.mp hfix) index_ne_zero_of_finite).trans
      (relIndex_le_of_le_right (DistanceEight.U_le_Z Rg z) index_ne_zero_of_finite)).trans_eq
        (by rw [show F = Z Rg z ⊓ Q Rg a from rfl,inf_relIndex_left]
            exact (small_critical_indices h e hz hk p (hsmall _ _ p)).2)
  have htwo : IsPGroup 2 K :=
    (Q_isPGroup Rg h.relative_radical.isPGroup h.relative_radical.twoCore_le a
      p.start_color).to_le ((inf_le_left.trans inf_le_left : K ≤ V Rg a).trans
        ((sourceGeometry h).V_le_Q hb a p.start_color))
  have hupper := moving_small_fixed_index_image h e hz hk p.end_color K hKG htwo hindex
  have hlower := relIndex_le_of_le_right (H := Q Rg z) hPK index_ne_zero_of_finite
  rw [hPi] at hlower
  have hKi : (Q Rg z).relIndex K = 2 := le_antisymm hupper hlower
  have hQF : Q Rg z ≤ centralizer (F : Set (FreeAmalgam Rg)) :=
    (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q Rg z p.end_color))).trans (centralizer_le inf_le_left)
  have hmeet : K ⊓ Q Rg z = Y ⊓ Q Rg z := by
    apply le_antisymm (inf_le_inf_right _ inf_le_left)
    exact le_inf (le_inf inf_le_left (inf_le_right.trans hQF)) inf_le_right
  have hs := equal_two_images_supplement P K (Q Rg z) hPK
    (hKG.trans (Q_normalized Rg z)) hPi hKi
  rw [hmeet] at hs
  have hNK : Y ⊓ Q Rg z ≤ K := hmeet ▸ inf_le_left
  have hm := relIndex_mul_relIndex (Y ⊓ Q Rg z) K Y hNK inf_le_left
  have hNi : (Y ⊓ Q Rg z).relIndex K = 2 := by
    rw [←hmeet,inf_relIndex_left,hKi]
  rw [hNi,inf_relIndex_left Y (Q Rg z),hYi] at hm
  have hKY : K.relIndex Y = 2 := by omega
  refine ⟨hs.symm,hKY,le_antisymm ?_ ?_⟩
  · exact small_critical_kernel_commutator h e hz hk p (hsmall _ _ p) K hKG hfix
  · exact commutator_mono (hAP.trans hPK) le_rfl

include h e hz hk in
/-- Both retained paths have exact forward action kernels. The original orbit
and kernel have only the critical line as opposite-kernel commutator, while the
whole radius retains its larger opposite-kernel commutator. -/
theorem plane_small_four_forward_action_control
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    (hb4 : sourceDistance h = 4)
    (hsmall : ∀ a z (_p : CriticalPath Rg (sourceGeometry h) a z),
      (Q Rg z).relIndex (Z Rg a) < 4) :
    ∃ a z, ∃ p : CriticalPath Rg (sourceGeometry h) a z,
      ∃ s, Adjacent Rg z s ∧
        Q Rg s ⊔ (V Rg a ⊓ Q Rg (p.walk.getVert 2)) = stabilizer Rg z ∧
        ∃ g ∈ Q Rg s, act Rg g⁻¹ z = z ∧
          ∃ q : CriticalPath Rg (sourceGeometry h) (act Rg g⁻¹ a) z,
            (∀ i, q.walk.getVert i = act Rg g⁻¹ (p.walk.getVert i)) ∧
            (∀ i j, (cosetGraph Rg).dist (p.walk.getVert i) (q.walk.getVert j) =
              (4-i) + (4-j)) ∧
            let Y := V Rg a ⊓ Q Rg (p.walk.getVert 2)
            let F := Z Rg z ⊓ Q Rg a
            let H := ⁅Y,F⁆
            let C := ⁅Y,Z Rg z⁆
            let forward := fun b (r : CriticalPath Rg (sourceGeometry h) b z) =>
              let P := localZSpan Rg b (r.walk.getVert 1)
              let Y₀ := V Rg b ⊓ Q Rg (r.walk.getVert 2)
              let F₀ := Z Rg z ⊓ Q Rg b
              let K := Y₀ ⊓ centralizer (F₀ : Set (FreeAmalgam Rg))
              P ≤ Y₀ ∧ ⁅P,F₀⁆ = ⊥ ∧
                Z Rg z ⊓ centralizer (P : Set (FreeAmalgam Rg)) = F₀ ∧
                ⁅P,Z Rg z⁆ = ⁅Z Rg b,Z Rg z⁆ ∧
                (Q Rg z).relIndex P = 2 ∧
                K = P ⊔ (Y₀ ⊓ Q Rg z) ∧ K.relIndex Y₀ = 2 ∧
                ⁅K,Z Rg z⁆ = ⁅Z Rg b,Z Rg z⁆
            Nat.card H = 2 ∧ H < C ∧ 4 ≤ Nat.card C ∧
              ⁅Y,Z Rg z ⊓ Q Rg (act Rg g⁻¹ a)⁆ = C ∧
              ⁅localZSpan Rg a (p.walk.getVert 1),Z Rg z ⊓ Q Rg (act Rg g⁻¹ a)⁆ =
                ⁅Z Rg a,Z Rg z⁆ ∧
              ⁅Y ⊓ centralizer (F : Set (FreeAmalgam Rg)),
                Z Rg z ⊓ Q Rg (act Rg g⁻¹ a)⁆ = ⁅Z Rg a,Z Rg z⁆ ∧
              forward a p ∧ forward (act Rg g⁻¹ a) q := by
  obtain ⟨a,z,p,s,hzs,hgen,g,hg,hfix,q,hverts,hgeom,
    hsupp,_,_,hopp,_,_,_,hcard,hstrict,hbig,hescape,_,_⟩ :=
    plane_small_four_full_kernel_comparison h e hz hk u hR hb4 hsmall
  let Y := V Rg a ⊓ Q Rg (p.walk.getVert 2)
  let F := Z Rg z ⊓ Q Rg a
  let F' := Z Rg z ⊓ Q Rg (act Rg g⁻¹ a)
  let T := ⁅Z Rg a,Z Rg z⁆
  have compare (A : Subgroup (FreeAmalgam Rg)) (hAV : A ≤ V Rg a) :
      ⁅A,F'⁆ = ⁅A,Z Rg z⁆ := by
    have hTZ : T ≤ Z Rg z := le_normalizer_iff_commutator_le_right.mp
      ((Z_le_stabilizer_of_dist_le a _ p.critical.1.le).trans (Z_normalized Rg z))
    have hTa : T ≤ Z Rg a := le_normalizer_iff_commutator_le_left.mp
      ((critical_Z_le_stabilizer Rg (sourceGeometry h) a p.start_color
        (by rw [(sourceGeometry h).distance_constant _ p.start_color]; exact sourceDistance_pos h)
        p.critical).trans (Z_normalized Rg a))
    let := (sourceGeometry h).Z_elementary (sourceDistance_pos h) z p.end_color
    have hTN : T ≤ normalizer (F' : Set (FreeAmalgam Rg)) :=
      ((hTZ.trans (le_centralizer (H := Z Rg z))).trans
        (centralizer_le (show F' ≤ Z Rg z from inf_le_left))).trans
          (Subgroup.centralizer_le_normalizer _)
    have hTC : T ≤ centralizer (A : Set (FreeAmalgam Rg)) :=
      (hTa.trans (commutator_eq_bot_iff_le_centralizer.mp
        (Z_centralizes_Q Rg a p.start_color))).trans
          (centralizer_le (hAV.trans
            ((sourceGeometry h).V_le_Q (distance_gt_two h e hz hk) a p.start_color)))
    rw [commutator_comm A F',commutator_comm A (Z Rg z),←hsupp]
    exact (commutator_sup_of_central_attachment F' T A hTN hTC).symm
  have hZz : (Z Rg z).map (MulAut.conj g).toMonoidHom = Z Rg z := by
    simpa only [inv_inv,hfix] using (Z_act Rg g⁻¹ z).symm
  have hescape' : ¬ ⁅V Rg (act Rg g⁻¹ a) ⊓ Q Rg (q.walk.getVert 2),Z Rg z⁆ ≤
      Z Rg (act Rg g⁻¹ a) := by
    intro hh
    apply hescape
    apply (map_le_map_iff_of_injective (f := (MulAut.conj g).toMonoidHom)
      (MulAut.conj g).injective).mp
    rw [map_commutator,hZz,
      Subgroup.map_inf _ _ (MulAut.conj g).toMonoidHom (MulAut.conj g).injective]
    simpa only [hverts 2,V_act,Q_act,Z_act,inv_inv] using hh
  have hA := plane_radius_first_edge_action h e hz hk u hR hb4 hsmall p hescape
  have hK := plane_radius_forward_action_kernel h e hz hk u hR hb4 hsmall p hescape
  have hA' := plane_radius_first_edge_action h e hz hk u hR hb4 hsmall q hescape'
  have hK' := plane_radius_forward_action_kernel h e hz hk u hR hb4 hsmall q hescape'
  refine ⟨a,z,p,s,hzs,hgen,g,hg,hfix,q,hverts,hgeom,hcard,hstrict,hbig,hopp,?_,?_,?_,?_⟩
  · exact (compare _ (hA.1.trans inf_le_left)).trans hA.2.2.2.1
  · exact (compare _ (inf_le_left.trans inf_le_left)).trans hK.2.2
  · exact ⟨hA.1,hA.2.1,hA.2.2.1,hA.2.2.2.1,hA.2.2.2.2,hK⟩
  · exact ⟨hA'.1,hA'.2.1,hA'.2.2.1,hA'.2.2.2.1,hA'.2.2.2.2,hK'⟩


omit hk in
include h e hz in
/-- Whole-core application of the exact forward action kernels on both original
paths, preserving the literal cubic projection and both full covers. -/
theorem coreExhaustion_or_cubic_forward_action_control :
    CoreExhaustion L R ∨
    ∃ hk : layerKernel L R = extensionKernel h,
      Function.Surjective (CubicAction.projection h e hz hk) ∧
      2 < sourceDistance h ∧
      (∀ a : Vertex Rg, color Rg a = false →
        Nat.card (U Rg a) = 16 ∨ Nat.card (U Rg a) = 32) ∧
      ∃ u : S,
        (Rg).map (CubicAction.projection h e hz hk) =
          borel.map (MulAut.conj u).toMonoidHom ∨
        ((Rg).map (CubicAction.projection h e hz hk) =
          D.map (MulAut.conj u).toMonoidHom ∧
        (sourceDistance h = 4 →
          (∀ a z (_p : CriticalPath Rg (sourceGeometry h) a z),
            (Q Rg z).relIndex (Z Rg a) < 4) →
    ∃ a z, ∃ p : CriticalPath Rg (sourceGeometry h) a z,
      ∃ s, Adjacent Rg z s ∧
        Q Rg s ⊔ (V Rg a ⊓ Q Rg (p.walk.getVert 2)) = stabilizer Rg z ∧
        ∃ g ∈ Q Rg s, act Rg g⁻¹ z = z ∧
          ∃ q : CriticalPath Rg (sourceGeometry h) (act Rg g⁻¹ a) z,
            (∀ i, q.walk.getVert i = act Rg g⁻¹ (p.walk.getVert i)) ∧
            (∀ i j, (cosetGraph Rg).dist (p.walk.getVert i) (q.walk.getVert j) =
              (4-i) + (4-j)) ∧
            let Y := V Rg a ⊓ Q Rg (p.walk.getVert 2)
            let F := Z Rg z ⊓ Q Rg a
            let H := ⁅Y,F⁆
            let C := ⁅Y,Z Rg z⁆
            let forward := fun b (r : CriticalPath Rg (sourceGeometry h) b z) =>
              let P := localZSpan Rg b (r.walk.getVert 1)
              let Y₀ := V Rg b ⊓ Q Rg (r.walk.getVert 2)
              let F₀ := Z Rg z ⊓ Q Rg b
              let K := Y₀ ⊓ centralizer (F₀ : Set (FreeAmalgam Rg))
              P ≤ Y₀ ∧ ⁅P,F₀⁆ = ⊥ ∧
                Z Rg z ⊓ centralizer (P : Set (FreeAmalgam Rg)) = F₀ ∧
                ⁅P,Z Rg z⁆ = ⁅Z Rg b,Z Rg z⁆ ∧
                (Q Rg z).relIndex P = 2 ∧
                K = P ⊔ (Y₀ ⊓ Q Rg z) ∧ K.relIndex Y₀ = 2 ∧
                ⁅K,Z Rg z⁆ = ⁅Z Rg b,Z Rg z⁆
            Nat.card H = 2 ∧ H < C ∧ 4 ≤ Nat.card C ∧
              ⁅Y,Z Rg z ⊓ Q Rg (act Rg g⁻¹ a)⁆ = C ∧
              ⁅localZSpan Rg a (p.walk.getVert 1),Z Rg z ⊓ Q Rg (act Rg g⁻¹ a)⁆ =
                ⁅Z Rg a,Z Rg z⁆ ∧
              ⁅Y ⊓ centralizer (F : Set (FreeAmalgam Rg)),
                Z Rg z ⊓ Q Rg (act Rg g⁻¹ a)⁆ = ⁅Z Rg a,Z Rg z⁆ ∧
              forward a p ∧ forward (act Rg g⁻¹ a) q)) := by
  rcases coreExhaustion_or_cubic_plane_paths h e hz with
    hex | ⟨hk,hs,hb,hcovers,u,hborel | ⟨hplane,_⟩⟩
  · exact Or.inl hex
  · exact Or.inr ⟨hk,hs,hb,hcovers,u,Or.inl hborel⟩
  · exact Or.inr ⟨hk,hs,hb,hcovers,u,Or.inr ⟨hplane,
      fun hb4 hsmall => plane_small_four_forward_action_control h e hz hk u hplane hb4 hsmall⟩⟩

omit hk in
include h e hz in
/-- Literal C.1.32 application. The original radical, odd extension-kernel
quotient and full central attachments are retained. -/
theorem rankTwo_or_cubic_forward_action_control :
    RankTwoAlternatives L R ∨
    ∃ hk : layerKernel L R = extensionKernel h,
      Function.Surjective (CubicAction.projection h e hz hk) ∧
      2 < sourceDistance h ∧
      (∀ a : Vertex Rg, color Rg a = false →
        Nat.card (U Rg a) = 16 ∨ Nat.card (U Rg a) = 32) ∧
      ∃ u : S,
        (Rg).map (CubicAction.projection h e hz hk) =
          borel.map (MulAut.conj u).toMonoidHom ∨
        ((Rg).map (CubicAction.projection h e hz hk) =
          D.map (MulAut.conj u).toMonoidHom ∧
        (sourceDistance h = 4 →
          (∀ a z (_p : CriticalPath Rg (sourceGeometry h) a z),
            (Q Rg z).relIndex (Z Rg a) < 4) →
    ∃ a z, ∃ p : CriticalPath Rg (sourceGeometry h) a z,
      ∃ s, Adjacent Rg z s ∧
        Q Rg s ⊔ (V Rg a ⊓ Q Rg (p.walk.getVert 2)) = stabilizer Rg z ∧
        ∃ g ∈ Q Rg s, act Rg g⁻¹ z = z ∧
          ∃ q : CriticalPath Rg (sourceGeometry h) (act Rg g⁻¹ a) z,
            (∀ i, q.walk.getVert i = act Rg g⁻¹ (p.walk.getVert i)) ∧
            (∀ i j, (cosetGraph Rg).dist (p.walk.getVert i) (q.walk.getVert j) =
              (4-i) + (4-j)) ∧
            let Y := V Rg a ⊓ Q Rg (p.walk.getVert 2)
            let F := Z Rg z ⊓ Q Rg a
            let H := ⁅Y,F⁆
            let C := ⁅Y,Z Rg z⁆
            let forward := fun b (r : CriticalPath Rg (sourceGeometry h) b z) =>
              let P := localZSpan Rg b (r.walk.getVert 1)
              let Y₀ := V Rg b ⊓ Q Rg (r.walk.getVert 2)
              let F₀ := Z Rg z ⊓ Q Rg b
              let K := Y₀ ⊓ centralizer (F₀ : Set (FreeAmalgam Rg))
              P ≤ Y₀ ∧ ⁅P,F₀⁆ = ⊥ ∧
                Z Rg z ⊓ centralizer (P : Set (FreeAmalgam Rg)) = F₀ ∧
                ⁅P,Z Rg z⁆ = ⁅Z Rg b,Z Rg z⁆ ∧
                (Q Rg z).relIndex P = 2 ∧
                K = P ⊔ (Y₀ ⊓ Q Rg z) ∧ K.relIndex Y₀ = 2 ∧
                ⁅K,Z Rg z⁆ = ⁅Z Rg b,Z Rg z⁆
            Nat.card H = 2 ∧ H < C ∧ 4 ≤ Nat.card C ∧
              ⁅Y,Z Rg z ⊓ Q Rg (act Rg g⁻¹ a)⁆ = C ∧
              ⁅localZSpan Rg a (p.walk.getVert 1),Z Rg z ⊓ Q Rg (act Rg g⁻¹ a)⁆ =
                ⁅Z Rg a,Z Rg z⁆ ∧
              ⁅Y ⊓ centralizer (F : Set (FreeAmalgam Rg)),
                Z Rg z ⊓ Q Rg (act Rg g⁻¹ a)⁆ = ⁅Z Rg a,Z Rg z⁆ ∧
              forward a p ∧ forward (act Rg g⁻¹ a) q)) :=
  (coreExhaustion_or_cubic_forward_action_control h e hz).imp
    (rankTwo_of_exhaustion h e hz) id

end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
