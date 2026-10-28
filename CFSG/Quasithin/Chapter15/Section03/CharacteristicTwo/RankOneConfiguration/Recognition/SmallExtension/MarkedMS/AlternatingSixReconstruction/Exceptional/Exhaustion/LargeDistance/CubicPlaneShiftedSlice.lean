module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneReciprocalKernel
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneEscape
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneRadiusAlignment
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlanePredecessor

/-!
# Shifted cubic kernel comparison for small predecessor slices

Keep the original critical path a--c--z and an overlapping critical path
from d to c through a. If the predecessor Baumann slice at c has index at
most two on U_z, every subgroup K of Z_d intersect Q_c satisfies
[K,Z_z] <= [K,Z_z intersect Q_a] join [Z_a,Z_z].

Suppose the comparison fails. The retained radius calculation identifies
[K,Z_z intersect Q_a] with the nonzero order-two radius line H. The small
slice makes the full reverse kernel fixed modulo Z_c by the residual at c,
and its core commutator is central there. Thus the actual residual rotation
preserves H while moving the final edge to the preceding edge. The rotated
endpoint gives a four-edge critical path from d. Its small critical image
makes the entire moving-seed commutator equal H.

The line H is aligned with the original critical line modulo the endpoint
center. On either allowed cover, an actor whose full displacement has that
alignment fixes the original critical hyperplane. This forces H to vanish.
The rotated full seed need only lie in the endpoint stabilizer; it is not
assumed to lie in the original edge kernel. The private graph adapter uses
the literal embedding and the existing cover map to establish that assertion.

The selected-path application retains the same opposite-edge conjugator,
both displaced radii, all cross-distances, and the larger full commutator
carried by the opposite kernel. The conjugator transports the small-slice
bound and escape to the second path, so both paths satisfy every shifted
kernel comparison. The remaining alternative is a strict slice at the
original midpoint. Whole-core and literal C.1.32 applications preserve the
original radical, kernel E with nontrivial odd E/Q, and both covers of orders
sixteen and thirty-two. The strict-slice case, terminal contradiction, other
image/distance cases and both core exhaustions remain unfinished.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (3.3)(ii), (5.8) and the shifted comparison (5.12)(1), printed
pp.866--867,920,924--925; Aschbacher--Smith C.1.31--32, printed pp.135--136.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.SpecificGroups.SymmetricSix Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open Representation Representation.BinaryOffender BinaryPermutation
open Representation.NormalElementaryQuotient
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


local notation "M" => (L ⊔ R : Subgroup G)
local notation "W₀" => (⁅centralOmega L R,L.subgroupOf M⁆ : Subgroup M)
local instance : IsElementaryAbelian 2 W₀ := IsElementaryAbelian.of_le (commutator_le_left _ _)

include h e hz hk in
private theorem critical_aligned_actor_fixes_moving_kernel
    {a z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (hp : (Q Rg z).relIndex (Z Rg a) < 4)
    (J : Subgroup (FreeAmalgam Rg)) (hJG : J ≤ stabilizer Rg z)
    (hmove : ⁅U Rg z,J⁆ ≤ ⁅Z Rg a,Z Rg z⁆ ⊔
      (stabilizer Rg z ⊓ centralizer (stabilizer Rg z : Set (FreeAmalgam Rg)))) :
    ⁅U Rg z ⊓ Q Rg a,J⁆ = ⊥ := by
  let := h.relative_normal
  have hb := distance_gt_two h e hz hk
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb
  have hzt : Adjacent Rg z (p.walk.getVert (p.walk.length-1)) := by
    have hh := p.walk.adj_getVert_succ (i := p.walk.length-1) (by omega)
    rw [show p.walk.length-1+1=p.walk.length by omega,p.walk.getVert_length] at hh
    exact adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp hh)
  have hAt : Z Rg a ≤ Q Rg (p.walk.getVert (p.walk.length-1)) := by
    apply Z_le_Q_of_dist_lt Rg _ ((sourceGeometry h).exists_critical _ p.start_color)
    rw [(sourceGeometry h).distance_constant _ p.start_color,p.dist_start (Nat.sub_le _ _)]
    have he : p.walk.length = sourceDistance h := p.length_eq_b
    change p.walk.length-1 < sourceDistance h
    omega
  obtain ⟨i,hi,hir,hiR,hiQ,hiU⟩ := remaining_edge_coordinates h e hz p.end_color hzt
  let A := (Z Rg a).comap i
  let J₀ := J.comap i
  have hA : A.map i = Z Rg a := map_comap_eq_self (hAt.trans (hiR ▸ map_le_range i _))
  have hJ : J₀.map i = J := map_comap_eq_self (hJG.trans_eq hir.symm)
  have hAr : A ≤ Rg := by
    apply (map_le_map_iff_of_injective hi).mp
    rwa [hA,hiR]
  obtain ⟨⟨τ,hτ,hτswap,hτeq⟩,hcrit⟩ :=
    plane_small_critical_chart_actor h e hz hk p hp i hi hiQ hiU hA hAr
  have hc : (center M).map i = stabilizer Rg z ⊓
      centralizer (stabilizer Rg z : Set (FreeAmalgam Rg)) := by
    rw [map_center_eq_range_inf_centralizer i hi,hir]
  have hm : ⁅W₀,J₀⁆ ≤ ⁅W₀,A⁆ ⊔ center M := by
    apply (map_le_map_iff_of_injective hi).mp
    rw [Subgroup.map_sup,map_commutator W₀ J₀ i,hiU,hJ,hcrit,hc]
    exact hmove
  have hm' : ⁅W₀,J₀⁆ ≤ ⁅W₀,A⁆ ⊔ (W₀ ⊓ center M) := by
    intro x hx
    obtain ⟨v,hv,c,hc,rfl⟩ := mem_sup_of_normal_right.mp (hm hx)
    have hcW : c ∈ W₀ := by
      have hh := (W₀).mul_mem ((W₀).inv_mem ((commutator_le_left W₀ A) hv))
        ((commutator_le_left W₀ J₀) hx)
      simpa only [inv_mul_cancel_left] using hh
    exact (⁅W₀,A⁆ ⊔ (W₀ ⊓ center M)).mul_mem (mem_sup_left hv)
      (mem_sup_right ⟨hcW,hc⟩)
  let σ := coverAction h e hz hk
  have htop : subgroupSpace W₀ W₀ = ⊤ := by
    ext v
    exact iff_of_true v.toMul.property (Submodule.mem_top)
  have hC : subgroupSpace W₀ (W₀ ⊓ center M) = fixedSpace σ ⊤ := by
    ext v
    have hh := mem_fixedSpace_image W₀ π (CubicEven.projection_surjective h e hz hk)
      (CubicAction.moved_projection_kernel h e hz hk) (⊤ : Subgroup M) v
    rw [map_top_of_surjective π (CubicEven.projection_surjective h e hz hk),coe_top,
      centralizer_univ] at hh
    change ((v.toMul : M) ∈ W₀ ∧ (v.toMul : M) ∈ center M) ↔ _
    simp only [v.toMul.property,true_and]
    exact hh.symm
  have hwhole (B : Subgroup M) : subgroupSpace W₀ ⁅W₀,B⁆ =
      subspaceCommutator σ ⊤ (B.map π) := by
    rw [subgroupSpace_commutator W₀ π (CubicEven.projection_surjective h e hz hk)
      (CubicAction.moved_projection_kernel h e hz hk) W₀ B le_rfl,htop]
  have hlin : subspaceCommutator σ ⊤ (J₀.map π) ≤
      subspaceCommutator σ ⊤ (zpowers τ) ⊔ fixedSpace σ ⊤ := by
    rw [←hτeq,←hwhole J₀,←hwhole A,←hC,
      ←subgroupSpace_sup W₀ (commutator_le_left W₀ A) inf_le_left]
    exact fun _ hv => hm' hv
  have hzero := cubic_cover_aligned_fixed_eq_bot h e hz hk τ hτswap (J₀.map π) hlin
  let F := W₀ ⊓ centralizer (A : Set M)
  have hF : subgroupSpace W₀ F = fixedSpace σ (A.map π) := by
    ext v
    change ((v.toMul : M) ∈ W₀ ∧ (v.toMul : M) ∈ centralizer (A : Set M)) ↔ _
    simp only [v.toMul.property,true_and]
    exact (mem_fixedSpace_image W₀ π (CubicEven.projection_surjective h e hz hk)
      (CubicAction.moved_projection_kernel h e hz hk) A v).symm
  have hzspace : subgroupSpace W₀ ⁅F,J₀⁆ = ⊥ := by
    rw [subgroupSpace_commutator W₀ π (CubicEven.projection_surjective h e hz hk)
      (CubicAction.moved_projection_kernel h e hz hk) F J₀ inf_le_left,hF,hτeq]
    exact hzero
  have hzgroup : ⁅F,J₀⁆ = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    have hv : Additive.ofMul (⟨x,((commutator_mono inf_le_left le_rfl).trans
      (commutator_le_left W₀ J₀)) hx⟩ : W₀) ∈ subgroupSpace W₀ ⁅F,J₀⁆ := hx
    rw [hzspace] at hv
    exact mem_bot.mpr (congrArg (fun v : Additive W₀ => (v.toMul : M))
      ((Submodule.mem_bot (ZMod 2)).mp hv))
  have hFm : F.map i = U Rg z ⊓ Q Rg a := by
    rw [show F = W₀ ⊓ centralizer (A : Set M) from rfl,
      ←map_inf_centralizer_of_injective i hi,hiU,hA,←critical_moving_kernel_eq_fixed h e p]
  have hh := congrArg (Subgroup.map i) hzgroup
  rwa [map_commutator,hFm,hJ,Subgroup.map_bot] at hh

include h e hz hk in
/-- A small opposite predecessor slice excludes failure of the shifted
kernel comparison. The residual rotation takes place on the same cubic path. -/
theorem plane_shifted_kernel_comparison_of_small_slice
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    (hb4 : sourceDistance h = 4)
    (hsmall : ∀ a z (_p : CriticalPath Rg (sourceGeometry h) a z),
      (Q Rg z).relIndex (Z Rg a) < 4)
    {a z d : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (q : CriticalPath Rg (sourceGeometry h) d (p.walk.getVert 2))
    (hqa : q.walk.getVert 2 = a)
    (hescape : ¬ ⁅V Rg a ⊓ Q Rg (p.walk.getVert 2),Z Rg z⁆ ≤ Z Rg a)
    (K : Subgroup (FreeAmalgam Rg)) (hK : K ≤ Z Rg d ⊓ Q Rg (p.walk.getVert 2))
    (hslice : (B Rg (p.walk.getVert 2) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg z) ≤ 2) :
    ⁅K,Z Rg z⁆ ≤ ⁅K,Z Rg z ⊓ Q Rg a⁆ ⊔ ⁅Z Rg a,Z Rg z⁆ := by
  by_contra hfail
  let c := p.walk.getVert 2
  let F := Z Rg z ⊓ Q Rg a
  let H := ⁅V Rg a ⊓ Q Rg c,F⁆
  have hb := distance_gt_two h e hz hk
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb4
  have hql : q.walk.length = 4 := q.length_eq_b.trans hb4
  have hc : color Rg c = false := q.end_color
  have hct : Adjacent Rg c (p.walk.getVert 3) :=
    (cosetGraph_adj Rg _ _).mp (p.walk.adj_getVert_succ (i := 2) (by omega))
  have hcv : Adjacent Rg c (p.walk.getVert 1) :=
    adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp
      (p.walk.adj_getVert_succ (i := 1) (by omega)))
  have hzt : Adjacent Rg z (p.walk.getVert 3) := by
    have hh := p.walk.adj_getVert_succ (i := 3) (by omega)
    rw [show 3+1=p.walk.length by omega,p.walk.getVert_length] at hh
    exact adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp hh)
  have ht : color Rg (p.walk.getVert 3) = true := by
    have hh := adjacent_color_ne Rg hzt
    rw [p.end_color] at hh
    cases he : color Rg (p.walk.getVert 3) <;> simp_all
  have hYt : V Rg a ⊓ Q Rg c ≤ Q Rg (p.walk.getVert (p.walk.length-1)) := by
    rw [hl]
    exact inf_le_right.trans (Q_le_adjacent_h Rg ht hct)
  have hAY : Z Rg a ≤ V Rg a ⊓ Q Rg c := by
    refine le_inf (Z_le_VBall Rg _ 2) ?_
    apply Z_le_Q_of_dist_lt Rg _ ((sourceGeometry h).exists_critical _ p.start_color)
    rw [(sourceGeometry h).distance_constant _ p.start_color,p.dist_start (by omega)]
    exact hb
  obtain ⟨hcard,_,_,_,_,halign⟩ := plane_radius_kernel_alignment h e hz hk u hR
    p (hsmall _ _ p) _ inf_le_left hYt hAY hescape
  change Nat.card H = 2 at hcard
  have hne : H ≠ ⊥ := by
    intro he
    rw [he,card_bot] at hcard
    omega
  have hKF : ⁅K,F⁆ = H :=
    (plane_shifted_kernel_failure_transfer h e hz hk u hR hb4 hsmall p q hqa
      hescape K hK hfail).1
  obtain ⟨k,hkm,hkt⟩ := residual_neighbor_transporter (h := h) hc hct hcv
  have hks : k ∈ Ltilde Rg (p.walk.getVert (p.walk.length-2)) := by
    simpa only [hl,Nat.reduceSub] using hkm
  have hs : (B Rg (p.walk.getVert (p.walk.length-2))
      ((sourceGeometry h).Z_normal _)).relIndex (U Rg z) ≤ 2 := by
    simpa only [hl,Nat.reduceSub] using hslice
  let K' := K.map (MulAut.conj k).toMonoidHom
  have hKc : K ≤ Q Rg (p.walk.getVert (p.walk.length-2)) := by
    simpa only [hl,Nat.reduceSub] using hK.trans inf_le_right
  have htrans : ⁅F,K'⁆ = H := by
    rw [show K' = K.map (MulAut.conj k).toMonoidHom from rfl,
      plane_predecessor_slice_residual_transport h e hz hk u hR p hs K hKc k hks,
      commutator_comm]
    exact hKF
  have hK'c : K' ≤ Q Rg (p.walk.getVert (p.walk.length-2)) := by
    exact (map_mono hKc).trans_eq
      (mem_normalizer_iff_map_conj_eq.mp
        ((Q_normalized Rg _) (Ltilde_le_stabilizer _ hks)))
  have htransU : ⁅U Rg z ⊓ Q Rg a,K'⁆ = H :=
    ((critical_kernel_predecessor_moving h e hz hb p).2.2 _ hK'c).symm.trans htrans
  have hK'd : K' ≤ Z Rg (act Rg k⁻¹ d) := by
    rw [Z_act,inv_inv]
    exact map_mono (hK.trans inf_le_left)
  have hesc : ¬ Z Rg d ≤ Q Rg (act Rg k z) := by
    intro hh
    have hh' : Z Rg (act Rg k⁻¹ d) ≤ Q Rg z := by
      calc
        _ = (Z Rg d).map (MulAut.conj k).toMonoidHom := by rw [Z_act,inv_inv]
        _ ≤ (Q Rg (act Rg k z)).map (MulAut.conj k).toMonoidHom := map_mono hh
        _ = Q Rg (act Rg k⁻¹ (act Rg k z)) := by
          simpa only [inv_inv] using (Q_act Rg k⁻¹ (act Rg k z)).symm
        _ = Q Rg z := by rw [←act_mul,mul_inv_cancel,act_one]
    apply hne
    rw [←htrans]
    exact le_bot_iff.mp ((commutator_mono inf_le_left (hK'd.trans hh')).trans_eq
      (Z_centralizes_Q Rg z p.end_color))
  have hdt : Adjacent Rg d (q.walk.getVert 1) := by
    apply (cosetGraph_adj Rg _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using
      q.walk.adj_getVert_succ (i := 0) (by omega)
  have hta : (cosetGraph Rg).Adj (q.walk.getVert 1) a := by
    have hh := q.walk.adj_getVert_succ (i := 1) (by omega)
    simpa only [hqa] using hh
  have hap : (cosetGraph Rg).Adj a (p.walk.getVert 1) := by
    simpa only [SimpleGraph.Walk.getVert_zero] using
      p.walk.adj_getVert_succ (i := 0) (by omega)
  have hend : (cosetGraph Rg).Adj (p.walk.getVert 1) (act Rg k z) := by
    rw [←hkt]
    exact (cosetGraph_adj Rg _ _).mpr ((adjacent_act_iff Rg k _ _).mpr
      (adjacent_symm Rg hzt))
  let w : (cosetGraph Rg).Walk d (act Rg k z) :=
    .cons ((cosetGraph_adj Rg _ _).mpr hdt) (.cons hta (.cons hap (.cons hend .nil)))
  have hw : w.length = 4 := rfl
  have hmin := criticalDistance_le Rg d ((sourceGeometry h).exists_critical d q.start_color) hesc
  rw [(sourceGeometry h).distance_constant d q.start_color] at hmin
  have hdist : (cosetGraph Rg).dist d (act Rg k z) = sourceDistance h := by
    have hh := SimpleGraph.dist_le w
    rw [hw,←hb4] at hh
    exact le_antisymm hh hmin
  let r : CriticalPath Rg (sourceGeometry h) d (act Rg k z) :=
    ⟨q.start_color,w,hw.trans (hb4.symm.trans hdist.symm),by
      refine ⟨?_,hesc⟩
      rw [(sourceGeometry h).distance_constant d q.start_color]
      exact hdist⟩
  let rr := CriticalPath.ofPair (geometry := sourceGeometry h) r.end_color
    (critical_reverse Rg (sourceGeometry h) (sourceEdgeCentralizer h e)
      d r.start_color (by
        rw [(sourceGeometry h).distance_constant d r.start_color]
        exact sourceDistance_pos h) (act Rg k z) r.end_color r.critical)
  have hex : Nonempty (CriticalPath Rg (sourceGeometry h) z (act Rg k⁻¹ d)) := by
    have hback : act Rg k⁻¹ (act Rg k z) = z := by
      rw [←act_mul,mul_inv_cancel,act_one]
    rw [←hback]
    exact ⟨rr.act k⁻¹⟩
  obtain ⟨r'⟩ := hex
  let J := Z Rg (act Rg k⁻¹ d)
  have hJ : J ≤ stabilizer Rg z :=
    critical_Z_le_stabilizer Rg (sourceGeometry h) z r'.start_color
      (by rw [(sourceGeometry h).distance_constant z r'.start_color]; exact sourceDistance_pos h)
      r'.critical
  have hCJ : Nat.card (⁅U Rg z,J⁆ : Subgroup (FreeAmalgam Rg)) = 2 := by
    rw [small_critical_moving_commutator_eq h e hz hk r' (hsmall _ _ r')]
    exact small_critical_commutator_card h e hz hk r' (hsmall _ _ r')
  have hHJ : H ≤ ⁅U Rg z,J⁆ := by
    rw [←htransU]
    exact commutator_mono inf_le_left hK'd
  let : Finite (⁅U Rg z,J⁆ : Subgroup (FreeAmalgam Rg)) :=
    Nat.finite_of_card_ne_zero (by rw [hCJ]; decide)
  have hJH : ⁅U Rg z,J⁆ = H :=
    (eq_of_le_of_card_ge hHJ (by rw [hCJ,hcard])).symm
  have hmove : ⁅U Rg z,J⁆ ≤ ⁅Z Rg a,Z Rg z⁆ ⊔
      (stabilizer Rg z ⊓ centralizer (stabilizer Rg z : Set (FreeAmalgam Rg))) := by
    rw [hJH]
    exact le_sup_left.trans_eq halign
  have hzero := critical_aligned_actor_fixes_moving_kernel h e hz hk p
    (hsmall _ _ p) J hJ hmove
  apply hne
  rw [←htransU]
  exact le_bot_iff.mp ((commutator_mono le_rfl hK'd).trans_eq hzero)


include h e hz hk in
/-- On the original selected and displaced paths, either the endpoint has a
strict predecessor slice, or every overlapping shifted kernel on either path satisfies the
source commutator comparison. The larger opposite-kernel commutator is retained. -/
theorem plane_small_four_shifted_slice_comparison
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
            let T := ⁅Z Rg a,Z Rg z⁆
            let H := ⁅Y,F⁆
            let C := ⁅Y,Z Rg z⁆
            Nat.card H = 2 ∧ H < C ∧ 4 ≤ Nat.card C ∧
              ⁅Y,Z Rg z ⊓ Q Rg (act Rg g⁻¹ a)⁆ = C ∧
              (2 < (B Rg (p.walk.getVert 2) ((sourceGeometry h).Z_normal _)).relIndex (U Rg z) ∨
                ((∀ d (r : CriticalPath Rg (sourceGeometry h) d (p.walk.getVert 2)),
                    r.walk.getVert 2 = a →
                    ∀ K : Subgroup (FreeAmalgam Rg),
                      K ≤ Z Rg d ⊓ Q Rg (p.walk.getVert 2) →
                      ⁅K,Z Rg z⁆ ≤ ⁅K,F⁆ ⊔ T) ∧
                  (∀ d (r : CriticalPath Rg (sourceGeometry h) d (q.walk.getVert 2)),
                    r.walk.getVert 2 = act Rg g⁻¹ a →
                    ∀ K : Subgroup (FreeAmalgam Rg),
                      K ≤ Z Rg d ⊓ Q Rg (q.walk.getVert 2) →
                      ⁅K,Z Rg z⁆ ≤ ⁅K,Z Rg z ⊓ Q Rg (act Rg g⁻¹ a)⁆ ⊔
                        ⁅Z Rg (act Rg g⁻¹ a),Z Rg z⁆))) := by
  obtain ⟨a,z,p,s,hzs,hgen,g,hg,hfix,q,hverts,hgeom,
    _,_,_,hopp,_,_,_,hcard,hstrict,hbig,hescape,_,_⟩ :=
    plane_small_four_full_kernel_comparison h e hz hk u hR hb4 hsmall
  refine ⟨a,z,p,s,hzs,hgen,g,hg,hfix,q,hverts,hgeom,hcard,hstrict,hbig,hopp,?_⟩
  by_cases hs : (B Rg (p.walk.getVert 2) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg z) ≤ 2
  · refine Or.inr ⟨fun d r hra K hK =>
      plane_shifted_kernel_comparison_of_small_slice h e hz hk u hR hb4 hsmall
        p r hra hescape K hK hs,?_⟩
    have hb := distance_gt_two h e hz hk
    have hl : p.walk.length = 4 := p.length_eq_b.trans hb4
    have hc : color Rg (p.walk.getVert 2) = false :=
      (p.vertex_color (by omega)).mpr (by decide)
    have hUz : (U Rg z).map (MulAut.conj g).toMonoidHom = U Rg z := by
      simpa only [inv_inv,hfix] using (U_act Rg g⁻¹ z).symm
    have hZz : (Z Rg z).map (MulAut.conj g).toMonoidHom = Z Rg z := by
      simpa only [inv_inv,hfix] using (Z_act Rg g⁻¹ z).symm
    have hs' : (B Rg (q.walk.getVert 2) ((sourceGeometry h).Z_normal _)).relIndex
        (U Rg z) ≤ 2 := by
      rw [hverts 2,Escape.PairingControl.FirstPairing.B_act
        (geometry := sourceGeometry h) hb _ _ hc,inv_inv,←hUz,
        relIndex_map_map_of_injective _ _ (MulAut.conj g).injective]
      exact hs
    have hescape' : ¬ ⁅V Rg (act Rg g⁻¹ a) ⊓ Q Rg (q.walk.getVert 2),Z Rg z⁆ ≤
        Z Rg (act Rg g⁻¹ a) := by
      intro hh
      apply hescape
      apply (map_le_map_iff_of_injective (f := (MulAut.conj g).toMonoidHom)
        (MulAut.conj g).injective).mp
      rw [map_commutator,hZz,
        Subgroup.map_inf _ _ (MulAut.conj g).toMonoidHom (MulAut.conj g).injective]
      simpa only [hverts 2,V_act,Q_act,Z_act,inv_inv] using hh
    exact fun d r hra K hK =>
      plane_shifted_kernel_comparison_of_small_slice h e hz hk u hR hb4 hsmall
        q r hra hescape' K hK hs'
  · exact Or.inl (lt_of_not_ge hs)


omit hk in
include h e hz in
/-- Whole-core application of the shifted comparison with the small predecessor
slice discharged by residual rotation. Both cubic covers remain explicit. -/
theorem coreExhaustion_or_cubic_shifted_slice_comparison :
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
            let T := ⁅Z Rg a,Z Rg z⁆
            let H := ⁅Y,F⁆
            let C := ⁅Y,Z Rg z⁆
            Nat.card H = 2 ∧ H < C ∧ 4 ≤ Nat.card C ∧
              ⁅Y,Z Rg z ⊓ Q Rg (act Rg g⁻¹ a)⁆ = C ∧
              (2 < (B Rg (p.walk.getVert 2) ((sourceGeometry h).Z_normal _)).relIndex (U Rg z) ∨
                ((∀ d (r : CriticalPath Rg (sourceGeometry h) d (p.walk.getVert 2)),
                    r.walk.getVert 2 = a →
                    ∀ K : Subgroup (FreeAmalgam Rg),
                      K ≤ Z Rg d ⊓ Q Rg (p.walk.getVert 2) →
                      ⁅K,Z Rg z⁆ ≤ ⁅K,F⁆ ⊔ T) ∧
                  (∀ d (r : CriticalPath Rg (sourceGeometry h) d (q.walk.getVert 2)),
                    r.walk.getVert 2 = act Rg g⁻¹ a →
                    ∀ K : Subgroup (FreeAmalgam Rg),
                      K ≤ Z Rg d ⊓ Q Rg (q.walk.getVert 2) →
                      ⁅K,Z Rg z⁆ ≤ ⁅K,Z Rg z ⊓ Q Rg (act Rg g⁻¹ a)⁆ ⊔
                        ⁅Z Rg (act Rg g⁻¹ a),Z Rg z⁆))))) := by
  rcases coreExhaustion_or_cubic_plane_paths h e hz with
    hex | ⟨hk,hs,hb,hcovers,u,hborel | ⟨hplane,_⟩⟩
  · exact Or.inl hex
  · exact Or.inr ⟨hk,hs,hb,hcovers,u,Or.inl hborel⟩
  · exact Or.inr ⟨hk,hs,hb,hcovers,u,Or.inr ⟨hplane,
      fun hb4 hsmall => plane_small_four_shifted_slice_comparison h e hz hk u hplane hb4 hsmall⟩⟩

omit hk in
include h e hz in
/-- Literal C.1.32 application retaining the original radical, projection with
kernel E, full attachments, and the same selected opposite-kernel commutator. -/
theorem rankTwo_or_cubic_shifted_slice_comparison :
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
            let T := ⁅Z Rg a,Z Rg z⁆
            let H := ⁅Y,F⁆
            let C := ⁅Y,Z Rg z⁆
            Nat.card H = 2 ∧ H < C ∧ 4 ≤ Nat.card C ∧
              ⁅Y,Z Rg z ⊓ Q Rg (act Rg g⁻¹ a)⁆ = C ∧
              (2 < (B Rg (p.walk.getVert 2) ((sourceGeometry h).Z_normal _)).relIndex (U Rg z) ∨
                ((∀ d (r : CriticalPath Rg (sourceGeometry h) d (p.walk.getVert 2)),
                    r.walk.getVert 2 = a →
                    ∀ K : Subgroup (FreeAmalgam Rg),
                      K ≤ Z Rg d ⊓ Q Rg (p.walk.getVert 2) →
                      ⁅K,Z Rg z⁆ ≤ ⁅K,F⁆ ⊔ T) ∧
                  (∀ d (r : CriticalPath Rg (sourceGeometry h) d (q.walk.getVert 2)),
                    r.walk.getVert 2 = act Rg g⁻¹ a →
                    ∀ K : Subgroup (FreeAmalgam Rg),
                      K ≤ Z Rg d ⊓ Q Rg (q.walk.getVert 2) →
                      ⁅K,Z Rg z⁆ ≤ ⁅K,Z Rg z ⊓ Q Rg (act Rg g⁻¹ a)⁆ ⊔
                        ⁅Z Rg (act Rg g⁻¹ a),Z Rg z⁆))))) :=
  (coreExhaustion_or_cubic_shifted_slice_comparison h e hz).imp
    (rankTwo_of_exhaustion h e hz) id

end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
