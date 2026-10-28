module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneStrictComparison
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneShiftedSlice

/-!
# Full reverse kernels fix the first-edge orbit

In the original cubic graph at critical distance four, fix a small critical
path a--v--c--t--z whose midpoint radius Y = V_a intersect Q_c escapes Z_a.
Its full reverse kernel F = Z_z intersect Q_a has [Y,F] of order two,
aligned with [Z_a,Z_z] modulo the actual center of G_z.

A seed subactor K of Y supported at distance at most four from z centralizes
F. Otherwise [F,K] is that order-two radius line. The supporting seed gives
a new critical pair, whose full moving commutator has order two as well.
It therefore has the original alignment. On both allowed full covers the
aligned-actor theorem fixes the original moving kernel, and the checked
full/moving kernel identity forces [F,K] to vanish.

Every seed incident to v lies in Y and within distance four of z. Thus F
centralizes their entire G_v orbit span. In particular, a midpoint-residual
rotation carrying t to v makes F commute with the entire rotated endpoint
seed, not only its reverse kernel. Adjoining Z_c gives an elementary abelian
join, as does the smaller join of the original and rotated full kernels.
Residual neighbor transitivity supplies an actual such rotation and its
transported critical path, without a small-slice or displacement premise.

The applications retain both original displaced paths, their cross-distances,
opposite-edge generator, and full opposite-kernel commutator. Whole-core and
literal C.1.32 consumers preserve the original radical, cubic projection
kernel E, nontrivial odd E/Q and both covers of orders sixteen and thirty-two.
This excludes nonabelian rotations through the original first edge. Other
rotation directions, the terminal comparison, remaining image/distance
branches and both core exhaustions still require their source arguments.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (3.3)(ii), (5.2), and the comparisons toward (5.12)(1),(3), printed
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
/-- A radius subactor supported within four edges of the endpoint fixes the
full reverse kernel. The proof retains the central attachment. -/
theorem plane_radius_near_seed_kernel_fixed
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    (hb4 : sourceDistance h = 4)
    (hsmall : ∀ a z (_p : CriticalPath Rg (sourceGeometry h) a z),
      (Q Rg z).relIndex (Z Rg a) < 4)
    {a z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (hescape : ¬ ⁅V Rg a ⊓ Q Rg (p.walk.getVert 2),Z Rg z⁆ ≤ Z Rg a)
    {w : Vertex Rg} (hw : color Rg w = false)
    (hd : (cosetGraph Rg).dist z w ≤ 4)
    (K : Subgroup (FreeAmalgam Rg)) (hKw : K ≤ Z Rg w)
    (hKY : K ≤ V Rg a ⊓ Q Rg (p.walk.getVert 2)) :
    ⁅Z Rg z ⊓ Q Rg a,K⁆ = ⊥ := by
  let c := p.walk.getVert 2
  let Y := V Rg a ⊓ Q Rg c
  let F := Z Rg z ⊓ Q Rg a
  let H := ⁅Y,F⁆
  let J := ⁅F,K⁆
  have hb := distance_gt_two h e hz hk
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb4
  have hct : Adjacent Rg c (p.walk.getVert 3) :=
    (cosetGraph_adj Rg _ _).mp (p.walk.adj_getVert_succ (i := 2) (by omega))
  have hzt : Adjacent Rg z (p.walk.getVert 3) := by
    have hh := p.walk.adj_getVert_succ (i := 3) (by omega)
    rw [show 3+1=p.walk.length by omega,p.walk.getVert_length] at hh
    exact adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp hh)
  have ht : color Rg (p.walk.getVert 3) = true := by
    have hh := adjacent_color_ne Rg hzt
    rw [p.end_color] at hh
    cases he : color Rg (p.walk.getVert 3) <;> simp_all
  have hYt : Y ≤ Q Rg (p.walk.getVert (p.walk.length-1)) := by
    rw [hl]
    exact inf_le_right.trans (Q_le_adjacent_h Rg ht hct)
  have hAY : Z Rg a ≤ Y := by
    refine le_inf (Z_le_VBall Rg _ 2) ?_
    apply Z_le_Q_of_dist_lt Rg _ ((sourceGeometry h).exists_critical _ p.start_color)
    rw [(sourceGeometry h).distance_constant _ p.start_color,p.dist_start (by omega)]
    exact hb
  obtain ⟨hcard,_,_,_,_,halign⟩ := plane_radius_kernel_alignment h e hz hk u hR
    p (hsmall _ _ p) Y inf_le_left hYt hAY hescape
  change Nat.card H = 2 at hcard
  by_contra hne
  change J ≠ ⊥ at hne
  have hJH : J ≤ H := by
    rw [show H = ⁅Y,F⁆ from rfl,commutator_comm]
    exact commutator_mono le_rfl hKY
  let : Finite H := Nat.finite_of_card_ne_zero (by rw [hcard]; decide)
  let : Finite J := Finite.of_injective (inclusion hJH) (inclusion_injective _)
  have hJcard : Nat.card J = 2 := by
    have hlo := (one_lt_card_iff_ne_bot J).mpr hne
    have hhi := card_le_of_le hJH
    omega
  have hJeq : J = H := eq_of_le_of_card_ge hJH (by rw [hJcard,hcard])
  have hesc : ¬ Z Rg z ≤ Q Rg w := by
    intro hh
    apply hne
    exact le_bot_iff.mp ((commutator_mono (inf_le_left.trans hh) hKw).trans_eq
      ((commutator_comm (Q Rg w) (Z Rg w)).trans (Z_centralizes_Q Rg w hw)))
  have hmin := criticalDistance_le Rg z
    ((sourceGeometry h).exists_critical _ p.end_color) hesc
  rw [(sourceGeometry h).distance_constant _ p.end_color] at hmin
  change sourceDistance h ≤ (cosetGraph Rg).dist z w at hmin
  have hdist : (cosetGraph Rg).dist z w = sourceDistance h := by omega
  let r : CriticalPath Rg (sourceGeometry h) z w :=
    CriticalPath.ofPair p.end_color ⟨by
      rw [(sourceGeometry h).distance_constant _ p.end_color]
      exact hdist,hesc⟩
  have hKc : K ≤ Q Rg (p.walk.getVert (p.walk.length-2)) := by
    simpa only [hl,Nat.reduceSub] using hKY.trans inf_le_right
  have hstrip : ⁅U Rg z ⊓ Q Rg a,K⁆ = J :=
    ((critical_kernel_predecessor_moving h e hz hb p).2.2 K hKc).symm
  let C := ⁅U Rg z,Z Rg w⁆
  have hCcard : Nat.card C = 2 := by
    rw [show C = ⁅U Rg z,Z Rg w⁆ from rfl,
      small_critical_moving_commutator_eq h e hz hk r (hsmall _ _ r)]
    exact small_critical_commutator_card h e hz hk r (hsmall _ _ r)
  have hJC : J ≤ C := by
    rw [←hstrip]
    exact commutator_mono inf_le_left hKw
  let : Finite C := Nat.finite_of_card_ne_zero (by rw [hCcard]; decide)
  have hCH : C = H := (eq_of_le_of_card_ge hJC (by rw [hJcard,hCcard])).symm.trans hJeq
  have hmove : ⁅U Rg z,Z Rg w⁆ ≤ ⁅Z Rg a,Z Rg z⁆ ⊔
      (stabilizer Rg z ⊓ centralizer (stabilizer Rg z : Set (FreeAmalgam Rg))) := by
    change C ≤ _
    rw [hCH]
    exact le_sup_left.trans_eq halign
  have hzero := critical_aligned_actor_fixes_moving_kernel h e hz hk p
    (hsmall _ _ p) (Z Rg w)
    (critical_Z_le_stabilizer Rg (sourceGeometry h) z r.start_color
      (by rw [(sourceGeometry h).distance_constant _ r.start_color]; exact sourceDistance_pos h)
      r.critical) hmove
  apply hne
  rw [←hstrip]
  exact le_bot_iff.mp ((commutator_mono le_rfl hKw).trans_eq hzero)


include h e hz hk in
/-- The full reverse kernel centralizes every seed incident to the original
first edge of the escaping critical path. -/
theorem plane_radius_first_edge_seed_fixed
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    (hb4 : sourceDistance h = 4)
    (hsmall : ∀ a z (_p : CriticalPath Rg (sourceGeometry h) a z),
      (Q Rg z).relIndex (Z Rg a) < 4)
    {a z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (hescape : ¬ ⁅V Rg a ⊓ Q Rg (p.walk.getVert 2),Z Rg z⁆ ≤ Z Rg a)
    {w : Vertex Rg} (hw : Adjacent Rg w (p.walk.getVert 1)) :
    ⁅Z Rg z ⊓ Q Rg a,Z Rg w⁆ = ⊥ := by
  let c := p.walk.getVert 2
  let v := p.walk.getVert 1
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb4
  have hav : Adjacent Rg a v := by
    apply (cosetGraph_adj Rg _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using
      p.walk.adj_getVert_succ (i := 0) (by omega)
  have hcv : Adjacent Rg c v := adjacent_symm Rg
    ((cosetGraph_adj Rg _ _).mp (p.walk.adj_getVert_succ (i := 1) (by omega)))
  have hv : color Rg v = true := by
    have hh := adjacent_color_ne Rg hav
    rw [p.start_color] at hh
    cases he : color Rg v <;> simp_all
  have hwcol : color Rg w = false := by
    have hh := adjacent_color_ne Rg hw
    rw [hv] at hh
    cases he : color Rg w <;> simp_all
  have common {x : Vertex Rg} (hx : Adjacent Rg x v) :
      (cosetGraph Rg).dist x w ≤ 2 := by
    have h₁ := SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj Rg _ _).mpr hx)
    have h₂ := SimpleGraph.dist_eq_one_iff_adj.mpr
      ((cosetGraph_adj Rg _ _).mpr (adjacent_symm Rg hw))
    change (cosetGraph Rg).dist v w = 1 at h₂
    have hh := (cosetGraph_connected Rg).dist_triangle (u := x) (v := v) (w := w)
    omega
  have haw := common hav
  have hcw := common hcv
  have hzc : (cosetGraph Rg).dist z c = 2 := by
    rw [SimpleGraph.dist_comm,p.dist_end,hl]
  have hzw : (cosetGraph Rg).dist z w ≤ 4 := by
    have hh := (cosetGraph_connected Rg).dist_triangle (u := z) (v := c) (w := w)
    omega
  apply plane_radius_near_seed_kernel_fixed h e hz hk u hR hb4 hsmall p hescape
    hwcol hzw (Z Rg w) le_rfl
  have hwa : (cosetGraph Rg).dist w a ≤ 2 := by rwa [SimpleGraph.dist_comm]
  refine le_inf (le_iSup_of_le w (le_iSup_of_le hwa le_rfl)) ?_
  apply Z_le_Q_of_dist_lt Rg _ ((sourceGeometry h).exists_critical _ hwcol)
  rw [(sourceGeometry h).distance_constant _ hwcol,SimpleGraph.dist_comm]
  change (cosetGraph Rg).dist c w < sourceDistance h
  omega

include h e hz hk in
/-- The entire first-edge orbit span centralizes the full reverse kernel. -/
theorem plane_radius_first_edge_orbit_fixed
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    (hb4 : sourceDistance h = 4)
    (hsmall : ∀ a z (_p : CriticalPath Rg (sourceGeometry h) a z),
      (Q Rg z).relIndex (Z Rg a) < 4)
    {a z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (hescape : ¬ ⁅V Rg a ⊓ Q Rg (p.walk.getVert 2),Z Rg z⁆ ≤ Z Rg a) :
    ⁅Z Rg z ⊓ Q Rg a,localZSpan Rg a (p.walk.getVert 1)⁆ = ⊥ := by
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb4
  have hav : Adjacent Rg a (p.walk.getVert 1) := by
    apply (cosetGraph_adj Rg _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using
      p.walk.adj_getVert_succ (i := 0) (by omega)
  apply commutator_eq_bot_iff_le_centralizer.mpr
  apply le_centralizer_iff.mpr
  apply iSup_le
  intro g
  have hgw : Adjacent Rg (act Rg g a) (p.walk.getVert 1) := by
    have hh := (adjacent_act_iff Rg (g : FreeAmalgam Rg) _ _).mpr hav
    rwa [show act Rg g (p.walk.getVert 1) = p.walk.getVert 1 from g.property] at hh
  exact le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
    (plane_radius_first_edge_seed_fixed h e hz hk u hR hb4 hsmall p hescape hgw))

include h e hz hk in
/-- A rotation through the original first edge has elementary full-seed and
full-kernel joins. No strict-slice or displacement premise is needed. -/
theorem plane_forward_kernel_rotation_elementary
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    (hb4 : sourceDistance h = 4)
    (hsmall : ∀ a z (_p : CriticalPath Rg (sourceGeometry h) a z),
      (Q Rg z).relIndex (Z Rg a) < 4)
    {a z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (hescape : ¬ ⁅V Rg a ⊓ Q Rg (p.walk.getVert 2),Z Rg z⁆ ≤ Z Rg a)
    (k : FreeAmalgam Rg) (hkm : k ∈ Ltilde Rg (p.walk.getVert 2))
    (hturn : act Rg k⁻¹ (p.walk.getVert 3) = p.walk.getVert 1) :
    let c := p.walk.getVert 2
    let F := Z Rg z ⊓ Q Rg a
    let z' := act Rg k⁻¹ z
    let F' := Z Rg z' ⊓ Q Rg (act Rg k⁻¹ a)
    ⁅F,Z Rg z'⁆ = ⊥ ∧
      IsElementaryAbelian 2 ((F ⊔ Z Rg z') ⊔ Z Rg c : Subgroup (FreeAmalgam Rg)) ∧
      IsElementaryAbelian 2 ((F ⊔ Z Rg c) ⊔ (F' ⊔ Z Rg c) : Subgroup (FreeAmalgam Rg)) := by
  let c := p.walk.getVert 2
  let F := Z Rg z ⊓ Q Rg a
  let z' := act Rg k⁻¹ z
  have hb := distance_gt_two h e hz hk
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb4
  have hc : color Rg c = false := (p.vertex_color (by omega)).mpr (by decide)
  have hzt : Adjacent Rg z (p.walk.getVert 3) := by
    have hh := p.walk.adj_getVert_succ (i := 3) (by omega)
    rw [show 3+1=p.walk.length by omega,p.walk.getVert_length] at hh
    exact adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp hh)
  have hz'v : Adjacent Rg z' (p.walk.getVert 1) := by
    rw [←hturn]
    exact (adjacent_act_iff Rg k⁻¹ _ _).mpr hzt
  have hzero := plane_radius_first_edge_seed_fixed h e hz hk u hR hb4 hsmall p hescape hz'v
  have hz'col : color Rg z' = false := by rw [action_preserves_color,p.end_color]
  let := (sourceGeometry h).Z_elementary (sourceDistance_pos h) z p.end_color
  let := (sourceGeometry h).Z_elementary (sourceDistance_pos h) z' hz'col
  let := (sourceGeometry h).Z_elementary (sourceDistance_pos h) c hc
  let : IsElementaryAbelian 2 F := IsElementaryAbelian.of_le (show F ≤ Z Rg z from inf_le_left)
  let : IsElementaryAbelian 2 (F ⊔ Z Rg z' : Subgroup (FreeAmalgam Rg)) :=
    IsElementaryAbelian.sup_of_le_centralizer
      (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hzero))
  have hZQ : Z Rg z ≤ Q Rg c := by
    apply Z_le_Q_of_dist_lt Rg _ ((sourceGeometry h).exists_critical _ p.end_color)
    rw [(sourceGeometry h).distance_constant _ p.end_color,SimpleGraph.dist_comm,p.dist_end,hl]
    exact hb
  have hfix : act Rg k⁻¹ c = c := Ltilde_le_stabilizer c ((Ltilde Rg c).inv_mem hkm)
  have hZ'Q : Z Rg z' ≤ Q Rg c := by
    have hh := map_mono (f := (MulAut.conj k).toMonoidHom) hZQ
    rw [show z' = act Rg k⁻¹ z from rfl,Z_act,inv_inv]
    exact hh.trans_eq (mem_normalizer_iff_map_conj_eq.mp
      ((Q_normalized Rg c) (Ltilde_le_stabilizer c hkm)))
  have hQC : Q Rg c ≤ centralizer (Z Rg c : Set (FreeAmalgam Rg)) :=
    le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q Rg c hc))
  have hAC : F ⊔ Z Rg z' ≤ centralizer (Z Rg c : Set (FreeAmalgam Rg)) :=
    (sup_le (inf_le_left.trans hZQ) hZ'Q).trans hQC
  let he : IsElementaryAbelian 2 ((F ⊔ Z Rg z') ⊔ Z Rg c : Subgroup (FreeAmalgam Rg)) :=
    IsElementaryAbelian.sup_of_le_centralizer (le_centralizer_iff.mp hAC)
  refine ⟨hzero,he,?_⟩
  exact IsElementaryAbelian.of_le (show
    (F ⊔ Z Rg c) ⊔ ((Z Rg z' ⊓ Q Rg (act Rg k⁻¹ a)) ⊔ Z Rg c) ≤
      (F ⊔ Z Rg z') ⊔ Z Rg c from
    sup_le (sup_le (le_sup_left.trans le_sup_left) le_sup_right)
      (sup_le (inf_le_left.trans (le_sup_right.trans le_sup_left)) le_sup_right))


include h e hz hk in
/-- Construct an actual forward residual rotation and its transported path,
with the full elementary joins proved on that same rotation. -/
theorem plane_forward_kernel_rotation
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    (hb4 : sourceDistance h = 4)
    (hsmall : ∀ a z (_p : CriticalPath Rg (sourceGeometry h) a z),
      (Q Rg z).relIndex (Z Rg a) < 4)
    {a z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (hescape : ¬ ⁅V Rg a ⊓ Q Rg (p.walk.getVert 2),Z Rg z⁆ ≤ Z Rg a) :
    ∃ k ∈ Ltilde Rg (p.walk.getVert 2),
      act Rg k⁻¹ (p.walk.getVert 2) = p.walk.getVert 2 ∧
      act Rg k⁻¹ (p.walk.getVert 3) = p.walk.getVert 1 ∧
      ∃ q : CriticalPath Rg (sourceGeometry h) (act Rg k⁻¹ a) (act Rg k⁻¹ z),
        (∀ i, q.walk.getVert i = act Rg k⁻¹ (p.walk.getVert i)) ∧
        let F := Z Rg z ⊓ Q Rg a
        let F' := Z Rg (act Rg k⁻¹ z) ⊓ Q Rg (act Rg k⁻¹ a)
        ⁅F,Z Rg (act Rg k⁻¹ z)⁆ = ⊥ ∧
          IsElementaryAbelian 2 ((F ⊔ Z Rg (act Rg k⁻¹ z)) ⊔ Z Rg (p.walk.getVert 2) : Subgroup (FreeAmalgam Rg)) ∧
          IsElementaryAbelian 2 ((F ⊔ Z Rg (p.walk.getVert 2)) ⊔
            (F' ⊔ Z Rg (p.walk.getVert 2)) : Subgroup (FreeAmalgam Rg)) := by
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb4
  have hc : color Rg (p.walk.getVert 2) = false :=
    (p.vertex_color (by omega)).mpr (by decide)
  have hct : Adjacent Rg (p.walk.getVert 2) (p.walk.getVert 3) :=
    (cosetGraph_adj Rg _ _).mp (p.walk.adj_getVert_succ (i := 2) (by omega))
  have hcv : Adjacent Rg (p.walk.getVert 2) (p.walk.getVert 1) :=
    adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp
      (p.walk.adj_getVert_succ (i := 1) (by omega)))
  obtain ⟨j,hjm,hjt⟩ := residual_neighbor_transporter (h := h) hc hct hcv
  let k := j⁻¹
  have hkm : k ∈ Ltilde Rg (p.walk.getVert 2) := (Ltilde Rg _).inv_mem hjm
  have hturn : act Rg k⁻¹ (p.walk.getVert 3) = p.walk.getVert 1 := by
    simpa only [k,inv_inv] using hjt
  exact ⟨k,hkm,Ltilde_le_stabilizer _ ((Ltilde Rg _).inv_mem hkm),hturn,
    p.act k⁻¹,fun i => by simp only [CriticalPath.act,actWalk_getVert],
    plane_forward_kernel_rotation_elementary h e hz hk u hR hb4 hsmall p hescape k hkm hturn⟩


include h e hz hk in
/-- Both original displaced paths have full first-edge orbit control and
actual elementary forward rotations, retaining their opposite-kernel comparison. -/
theorem plane_small_four_forward_kernel_control
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
              ⁅Z Rg z ⊓ Q Rg b,localZSpan Rg b (r.walk.getVert 1)⁆ = ⊥ ∧
                ∃ k ∈ Ltilde Rg (r.walk.getVert 2),
                  act Rg k⁻¹ (r.walk.getVert 2) = r.walk.getVert 2 ∧
                  act Rg k⁻¹ (r.walk.getVert 3) = r.walk.getVert 1 ∧
                  let F₀ := Z Rg z ⊓ Q Rg b
                  let F₁ := Z Rg (act Rg k⁻¹ z) ⊓ Q Rg (act Rg k⁻¹ b)
                  ⁅F₀,Z Rg (act Rg k⁻¹ z)⁆ = ⊥ ∧
                    IsElementaryAbelian 2 ((F₀ ⊔ Z Rg (act Rg k⁻¹ z)) ⊔
                      Z Rg (r.walk.getVert 2) : Subgroup (FreeAmalgam Rg)) ∧
                    IsElementaryAbelian 2 ((F₀ ⊔ Z Rg (r.walk.getVert 2)) ⊔
                      (F₁ ⊔ Z Rg (r.walk.getVert 2)) : Subgroup (FreeAmalgam Rg))
            Nat.card H = 2 ∧ H < C ∧ 4 ≤ Nat.card C ∧
              ⁅Y,Z Rg z ⊓ Q Rg (act Rg g⁻¹ a)⁆ = C ∧
              forward a p ∧ forward (act Rg g⁻¹ a) q := by
  obtain ⟨a,z,p,s,hzs,hgen,g,hg,hfix,q,hverts,hgeom,
    _,_,_,hopp,_,_,_,hcard,hstrict,hbig,hescape,_,_⟩ :=
    plane_small_four_full_kernel_comparison h e hz hk u hR hb4 hsmall
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
  refine ⟨a,z,p,s,hzs,hgen,g,hg,hfix,q,hverts,hgeom,hcard,hstrict,hbig,hopp,?_,?_⟩
  · refine ⟨plane_radius_first_edge_orbit_fixed h e hz hk u hR hb4 hsmall p hescape,?_⟩
    obtain ⟨k,hkm,hkc,hkt,r,hr,hzero,he,he'⟩ :=
      plane_forward_kernel_rotation h e hz hk u hR hb4 hsmall p hescape
    exact ⟨k,hkm,hkc,hkt,hzero,he,he'⟩
  · refine ⟨plane_radius_first_edge_orbit_fixed h e hz hk u hR hb4 hsmall q hescape',?_⟩
    obtain ⟨k,hkm,hkc,hkt,r,hr,hzero,he,he'⟩ :=
      plane_forward_kernel_rotation h e hz hk u hR hb4 hsmall q hescape'
    exact ⟨k,hkm,hkc,hkt,hzero,he,he'⟩

omit hk in
include h e hz in
/-- Whole-core application of the forward rotation exclusion on both original
paths, with the same cubic projection and both full covers. -/
theorem coreExhaustion_or_cubic_forward_kernel_control :
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
              ⁅Z Rg z ⊓ Q Rg b,localZSpan Rg b (r.walk.getVert 1)⁆ = ⊥ ∧
                ∃ k ∈ Ltilde Rg (r.walk.getVert 2),
                  act Rg k⁻¹ (r.walk.getVert 2) = r.walk.getVert 2 ∧
                  act Rg k⁻¹ (r.walk.getVert 3) = r.walk.getVert 1 ∧
                  let F₀ := Z Rg z ⊓ Q Rg b
                  let F₁ := Z Rg (act Rg k⁻¹ z) ⊓ Q Rg (act Rg k⁻¹ b)
                  ⁅F₀,Z Rg (act Rg k⁻¹ z)⁆ = ⊥ ∧
                    IsElementaryAbelian 2 ((F₀ ⊔ Z Rg (act Rg k⁻¹ z)) ⊔
                      Z Rg (r.walk.getVert 2) : Subgroup (FreeAmalgam Rg)) ∧
                    IsElementaryAbelian 2 ((F₀ ⊔ Z Rg (r.walk.getVert 2)) ⊔
                      (F₁ ⊔ Z Rg (r.walk.getVert 2)) : Subgroup (FreeAmalgam Rg))
            Nat.card H = 2 ∧ H < C ∧ 4 ≤ Nat.card C ∧
              ⁅Y,Z Rg z ⊓ Q Rg (act Rg g⁻¹ a)⁆ = C ∧
              forward a p ∧ forward (act Rg g⁻¹ a) q)) := by
  rcases coreExhaustion_or_cubic_plane_paths h e hz with
    hex | ⟨hk,hs,hb,hcovers,u,hborel | ⟨hplane,_⟩⟩
  · exact Or.inl hex
  · exact Or.inr ⟨hk,hs,hb,hcovers,u,Or.inl hborel⟩
  · exact Or.inr ⟨hk,hs,hb,hcovers,u,Or.inr ⟨hplane,
      fun hb4 hsmall => plane_small_four_forward_kernel_control h e hz hk u hplane hb4 hsmall⟩⟩

omit hk in
include h e hz in
/-- Literal C.1.32 application. The original radical, odd extension-kernel
quotient and full central attachments are retained. -/
theorem rankTwo_or_cubic_forward_kernel_control :
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
              ⁅Z Rg z ⊓ Q Rg b,localZSpan Rg b (r.walk.getVert 1)⁆ = ⊥ ∧
                ∃ k ∈ Ltilde Rg (r.walk.getVert 2),
                  act Rg k⁻¹ (r.walk.getVert 2) = r.walk.getVert 2 ∧
                  act Rg k⁻¹ (r.walk.getVert 3) = r.walk.getVert 1 ∧
                  let F₀ := Z Rg z ⊓ Q Rg b
                  let F₁ := Z Rg (act Rg k⁻¹ z) ⊓ Q Rg (act Rg k⁻¹ b)
                  ⁅F₀,Z Rg (act Rg k⁻¹ z)⁆ = ⊥ ∧
                    IsElementaryAbelian 2 ((F₀ ⊔ Z Rg (act Rg k⁻¹ z)) ⊔
                      Z Rg (r.walk.getVert 2) : Subgroup (FreeAmalgam Rg)) ∧
                    IsElementaryAbelian 2 ((F₀ ⊔ Z Rg (r.walk.getVert 2)) ⊔
                      (F₁ ⊔ Z Rg (r.walk.getVert 2)) : Subgroup (FreeAmalgam Rg))
            Nat.card H = 2 ∧ H < C ∧ 4 ≤ Nat.card C ∧
              ⁅Y,Z Rg z ⊓ Q Rg (act Rg g⁻¹ a)⁆ = C ∧
              forward a p ∧ forward (act Rg g⁻¹ a) q)) :=
  (coreExhaustion_or_cubic_forward_kernel_control h e hz).imp
    (rankTwo_of_exhaustion h e hz) id

end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
