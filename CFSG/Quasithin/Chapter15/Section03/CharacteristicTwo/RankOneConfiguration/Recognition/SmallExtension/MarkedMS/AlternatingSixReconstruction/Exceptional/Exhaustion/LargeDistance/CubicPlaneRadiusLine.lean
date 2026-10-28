module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneFourOmega
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneBackward
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicSmallBackward
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneShiftedSlices
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneShiftedConfiguration

/-!
# An unavoidable full radius kernel line in the cubic plane case

At distance four with uniformly small critical images, some original full
radius kernel Y = V_a intersect Q_c has endpoint commutator outside Z_a.
Otherwise the normalized paired selector supplies two backward critical
paths with distinct kernels. Their shared midpoint and the actual generating
edge let the same argument run a second time, forcing two different kernels
in that one midpoint core. The two-end-slice theorem supplies a strict slice
if none was initially chosen. All paths belong to the original cubic graph.

For an arbitrary radius subactor in the last edge kernel, the fixed-hyperplane
comparison shows that endpoint escape forces its full critical-kernel
commutator to have order two. This is also the entire last-edge radius
kernel commutator; no containment of the whole backward seed is required.
The proved central generation of full omega supplies X_z = Z_z, including
all central attachments. On the selected path the line lies in Z_a and Z_c,
centralizes both radii, and is strictly smaller than the full endpoint
commutator. That larger commutator lies in the last edge omega-center and
the starting core, but escapes the starting seed.

The whole-core and literal C.1.32 applications keep both moving covers of
orders sixteen and thirty-two, the original radical, and the cubic projection
with kernel E and nontrivial odd E/Q. The order-two line is an obstruction
still to exclude, not a terminal contradiction. Small-image production,
larger-distance and Borel exclusions, both core exhaustions and the final
two-branch reconstruction remain open.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (3.3)(ii), (5.6)--(5.8) and the paired kernel comparison of (5.12),
printed pp.866--867,917--920,924--927; Aschbacher--Smith C.1.31--32,
printed pp.135--136.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open Theory.SpecificGroups.SymmetricSix Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open scoped IsMulCommutative commutatorElement Pointwise
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "M" => (L ⊔ R : Subgroup G)
local notation "Rg" => edge L R
local notation "π" => CubicAction.projection h e hz hk

include h e hz hk in
/-- An escaping radius subactor determines the entire last-edge radius
kernel commutator, of order two, while its full endpoint commutator is larger. -/
theorem plane_radius_subactor_kernel_line
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    {a z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (hp : (Q Rg z).relIndex (Z Rg a) < 4)
    (Y : Subgroup (FreeAmalgam Rg)) (hYV : Y ≤ V Rg a)
    (hYt : Y ≤ Q Rg (p.walk.getVert (p.walk.length-1)))
    (hnot : ¬ ⁅Y,Z Rg z⁆ ≤ Z Rg a) :
    let H := ⁅Y,Z Rg z ⊓ Q Rg a⁆
    Nat.card H = 2 ∧
      ⁅V Rg a ⊓ Q Rg (p.walk.getVert (p.walk.length-1)),
        Z Rg z ⊓ Q Rg a⁆ = H ∧
      H ≤ Z Rg a ∧ H < ⁅Y,Z Rg z⁆ ∧
      ⁅Y,Z Rg z⁆ ≤ Z Rg (p.walk.getVert (p.walk.length-1)) ⊓ Q Rg a := by
  have hb := distance_gt_two h e hz hk
  let t := p.walk.getVert (p.walk.length-1)
  let F := Z Rg z ⊓ Q Rg a
  let W := V Rg a ⊓ Q Rg t
  let H := ⁅Y,F⁆
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb
  have hzt : Adjacent Rg z t := by
    have hh := p.walk.adj_getVert_succ (i := p.walk.length-1) (by omega)
    rw [show p.walk.length-1+1=p.walk.length by omega,p.walk.getVert_length] at hh
    exact adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp hh)
  have hYG : Y ≤ stabilizer Rg z :=
    hYt.trans (fun _ hy => hy.2 _ (adjacent_symm Rg hzt))
  have hAt : Z Rg a ≤ Q Rg t := by
    apply Z_le_Q_of_dist_lt Rg _ ((sourceGeometry h).exists_critical _ p.start_color)
    rw [(sourceGeometry h).distance_constant _ p.start_color,p.dist_start (Nat.sub_le _ _)]
    have he : p.walk.length = sourceDistance h := p.length_eq_b
    change p.walk.length-1 < sourceDistance h
    omega
  have hYW : Y ≤ W := le_inf hYV hYt
  have hfixed : F = Z Rg z ⊓ centralizer (Z Rg a : Set (FreeAmalgam Rg)) :=
    (critical_seed_centralizer_intersection h e
      (CriticalPath.ofPair p.end_color (reverse_pair h e p))).symm
  let := finite_Z Rg z
  let : Finite (U Rg z) := Finite.of_injective
    (inclusion (DistanceEight.U_le_Z Rg z)) (inclusion_injective _)
  have hi : (centralizer (Z Rg a : Set (FreeAmalgam Rg))).relIndex (U Rg z) ≤ 2 := by
    have hQC := le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q Rg a p.start_color))
    exact ((relIndex_le_of_le_left hQC index_ne_zero_of_finite).trans
      (relIndex_le_of_le_right (DistanceEight.U_le_Z Rg z) index_ne_zero_of_finite)).trans_eq
        (small_critical_indices h e hz hk p hp).2
  have hwhole : ⁅W,F⁆ ≤ Z Rg a :=
    (commutator_mono inf_le_left inf_le_right).trans
      (plane_radius_core_commutator h e hz hk u hR p.start_color)
  have hbound : Nat.card (⁅W,F⁆ : Subgroup (FreeAmalgam Rg)) ≤ 2 := by
    by_contra! hn
    have hh := plane_edge_large_fixed_commutator h e hz hk u hR.le p.end_color hzt
      (Z Rg a) W hAt inf_le_right p.critical.2 hi
      (by rw [←hfixed,commutator_comm]; exact hn)
    rw [←hfixed,commutator_comm F W] at hh
    apply hnot
    rw [commutator_comm Y]
    exact (commutator_mono le_rfl hYW).trans
      (hh.trans (sup_le hwhole (by
        rw [commutator_comm]
        exact critical_seed_commutator_le h p)))
  have hHle : H ≤ ⁅W,F⁆ := commutator_mono hYW le_rfl
  have hHZ : H ≤ Z Rg a := hHle.trans hwhole
  have hne : H ≠ ⊥ := by
    intro he
    exact hnot ((small_critical_kernel_commutator h e hz hk p hp Y hYG
      (commutator_eq_bot_iff_le_centralizer.mp he)).trans
        (critical_seed_commutator_le h p))
  let := finite_Z Rg a
  let : Finite (⁅W,F⁆ : Subgroup (FreeAmalgam Rg)) :=
    Finite.of_injective (inclusion hwhole) (inclusion_injective _)
  let : Finite H := Finite.of_injective (inclusion hHZ) (inclusion_injective _)
  have hcard : Nat.card H = 2 := by
    have hlo := (one_lt_card_iff_ne_bot H).mpr hne
    have hhi := card_le_of_le hHle
    omega
  have heq : ⁅W,F⁆ = H := (eq_of_le_of_card_ge hHle (by omega)).symm
  have hTt : ⁅Y,Z Rg z⁆ ≤ Z Rg t := by
    rw [commutator_comm]
    exact (commutator_mono le_rfl hYt).trans
      (plane_edge_seed_commutator h e hz hk u hR p.end_color hzt)
  have hTa : ⁅Y,Z Rg z⁆ ≤ Q Rg a :=
    (commutator_mono (hYV.trans ((sourceGeometry h).V_le_Q hb a p.start_color)) le_rfl).trans
      (le_normalizer_iff_commutator_le_left.mp
        ((critical_Z_le_stabilizer Rg (sourceGeometry h) a p.start_color
          (by rw [(sourceGeometry h).distance_constant _ p.start_color]; exact sourceDistance_pos h)
          p.critical).trans (Q_normalized Rg a)))
  exact ⟨hcard,heq,hHZ,lt_of_le_not_ge (commutator_mono le_rfl inf_le_left)
    (fun ht => hnot (ht.trans hHZ)),le_inf hTt hTa⟩

include h e hz hk in
/-- Full omega version on a critical four-edge path. A failure of endpoint
control selects the same order-two line in the whole last-edge radius kernel. -/
theorem plane_four_full_kernel_line
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    (hb4 : sourceDistance h = 4)
    (hsmall : ∀ a z (_p : CriticalPath Rg (sourceGeometry h) a z),
      (Q Rg z).relIndex (Z Rg a) < 4)
    {a z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (Y : Subgroup (FreeAmalgam Rg)) (hYV : Y ≤ V Rg a)
    (hYc : Y ≤ Q Rg (p.walk.getVert 2))
    (hnot : ¬ ⁅Y,X Rg z⁆ ≤ Z Rg a) :
    let H := ⁅Y,X Rg z ⊓ Q Rg a⁆
    Nat.card H = 2 ∧
      ⁅V Rg a ⊓ Q Rg (p.walk.getVert 3),X Rg z ⊓ Q Rg a⁆ = H ∧
      H ≤ Z Rg a ⊓ Z Rg (p.walk.getVert 2) ∧
      H ≤ centralizer ((V Rg a ⊔ V Rg (p.walk.getVert 2) :
        Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg)) ∧
      H < ⁅Y,X Rg z⁆ ∧
      ⁅Y,X Rg z⁆ ≤ Z Rg (p.walk.getVert 3) ⊓ Q Rg a ∧
      ⁅⁅Y,X Rg z⁆,Q Rg (p.walk.getVert 3)⁆ = ⊥ := by
  have hb := distance_gt_two h e hz hk
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb4
  have hc : color Rg (p.walk.getVert 2) = false :=
    (p.vertex_color (by omega)).mpr (by decide)
  have hct : Adjacent Rg (p.walk.getVert 2) (p.walk.getVert 3) :=
    (cosetGraph_adj Rg _ _).mp (p.walk.adj_getVert_succ (i := 2) (by omega))
  have ht : color Rg (p.walk.getVert 3) = true := by
    have hh := adjacent_color_ne Rg hct
    rw [hc] at hh
    cases he : color Rg (p.walk.getVert 3) <;> simp_all
  have hYt := hYc.trans (Q_le_adjacent_h Rg ht hct)
  have hXZ := (plane_small_four_omega_generated h e hz hk u hR hb4 hsmall z p.end_color).2
  rw [hXZ] at hnot ⊢
  have hd := plane_radius_subactor_kernel_line h e hz hk u hR p (hsmall _ _ p) Y hYV
    (by simpa only [hl,Nat.reduceSub] using hYt) hnot
  simp only [hl,Nat.reduceSub] at hd
  have hHZc : ⁅Y,Z Rg z ⊓ Q Rg a⁆ ≤ Z Rg (p.walk.getVert 2) :=
    (commutator_mono le_rfl inf_le_left).trans
      (hd.2.2.2.2.trans (inf_le_left.trans (adjacent_Z_le Rg hc hct)))
  have hHZa := hd.2.2.1
  have hfix {v : Vertex Rg} (hv : color Rg v = false) :
      Z Rg v ≤ centralizer (V Rg v : Set (FreeAmalgam Rg)) :=
    (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q Rg v hv)).trans
      (centralizer_le ((sourceGeometry h).V_le_Q hb v hv))
  refine ⟨hd.1,hd.2.1,le_inf hHZa hHZc,?_,hd.2.2.2.1,hd.2.2.2.2,?_⟩
  · apply le_centralizer_iff.mpr
    exact sup_le (le_centralizer_iff.mp (hHZa.trans (hfix p.start_color)))
      (le_centralizer_iff.mp (hHZc.trans (hfix hc)))
  · apply commutator_eq_bot_iff_le_centralizer.mpr
    intro x hx
    have hx' := hd.2.2.2.2 hx
    rw [Z,if_neg (by simp [ht])] at hx'
    exact (mem_omegaCenter_iff.mp hx'.1).2.2

include h e hz hk in
private theorem paired_strict_kernel_escape
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    (hb4 : sourceDistance h = 4)
    {a z z' c d : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) a z)
    (p' : CriticalPath Rg (sourceGeometry h) a z')
    (q : CriticalPath Rg (sourceGeometry h) d c)
    (hqa : q.walk.getVert 2 = a)
    (hq : (Q Rg c).relIndex (Z Rg d) < 4)
    (hgen : (Q Rg (q.walk.getVert 1) ⊔ Z Rg z) ⊔ Z Rg z' = stabilizer Rg a)
    (hs : 2 < (B Rg a ((sourceGeometry h).Z_normal _)).relIndex (U Rg d)) :
    ¬ ⁅Z Rg d ⊓ Q Rg c,Z Rg z⁆ ≤ Z Rg a ∨
      ¬ ⁅Z Rg d ⊓ Q Rg c,Z Rg z'⁆ ≤ Z Rg a := by
  by_contra! hn
  have hb := distance_gt_two h e hz hk
  have hql : q.walk.length = 4 := q.length_eq_b.trans hb4
  let K := Z Rg d ⊓ Q Rg c
  let N := K ⊔ Z Rg a
  let s := q.walk.getVert 1
  have has : Adjacent Rg a s := by
    rw [←hqa]
    exact adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp
      (q.walk.adj_getVert_succ (i := 1) (by omega)))
  have hda : (cosetGraph Rg).dist d a ≤ 2 := by
    rw [←hqa,q.dist_start (by omega)]
  have hKV : K ≤ V Rg a := inf_le_left.trans
    (le_iSup_of_le d (le_iSup_of_le hda le_rfl))
  have hNV : N ≤ V Rg a := sup_le hKV (Z_le_VBall Rg _ 2)
  have hNG : N ≤ stabilizer Rg a :=
    hNV.trans ((sourceGeometry h).V_local _ p.start_color (by
      rw [(sourceGeometry h).distance_constant _ p.start_color]; exact hb))
  have hKN : Q Rg s ≤ normalizer (K : Set (FreeAmalgam Rg)) :=
    plane_small_critical_first_edge_normalizes_kernel h e hz hk u hR q hq
  have hNs : Q Rg s ≤ normalizer (N : Set (FreeAmalgam Rg)) :=
    (le_inf hKN ((show Q Rg s ≤ stabilizer Rg a from
      fun _ hx => hx.2 _ (adjacent_symm Rg has)).trans (Z_normalized Rg _))).trans
        (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have move {w : Vertex Rg} (r : CriticalPath Rg (sourceGeometry h) a w)
      (hm : ⁅K,Z Rg w⁆ ≤ Z Rg a) : ⁅N,Z Rg w⁆ ≤ Z Rg a := by
    apply commutator_sup_le_of_relative_normal (stabilizer Rg a)
      K (Z Rg a) (Z Rg w) (Z Rg a) (Z_normalized Rg _)
      (le_sup_left.trans hNG) (Z_le_stabilizer Rg _) hm
    exact critical_seed_commutator_le h r
  have hpN := move p hn.1
  have hpN' := move p' hn.2
  have hNn : stabilizer Rg a ≤ normalizer (N : Set (FreeAmalgam Rg)) := by
    rw [←hgen]
    exact sup_le (sup_le hNs
      (le_normalizer_iff_commutator_le_left.mpr (hpN.trans le_sup_right)))
      (le_normalizer_iff_commutator_le_left.mpr (hpN'.trans le_sup_right))
  have hKB : K ≤ B Rg a ((sourceGeometry h).Z_normal _) :=
    le_sup_left.trans (shifted_normalized_radius_le_slice h e hz hb p N hNV hNn hpN)
  let := finite_Z Rg d
  let : Finite (U Rg d) := Finite.of_injective
    (inclusion (DistanceEight.U_le_Z Rg d)) (inclusion_injective _)
  have hi := relIndex_le_of_le_left hKB
    (index_ne_zero_of_finite (H := K.subgroupOf (Z Rg d)))
  change (B Rg a ((sourceGeometry h).Z_normal _)).relIndex (Z Rg d) ≤
    (Z Rg d ⊓ Q Rg c).relIndex (Z Rg d) at hi
  rw [inf_relIndex_left,(small_critical_indices h e hz hk q hq).1] at hi
  have hUi := (relIndex_le_of_le_right (DistanceEight.U_le_Z Rg d)
    index_ne_zero_of_finite).trans hi
  omega

include h e hz in
private theorem paired_controlled_subgroup_le_slice
    (hb : 2 < sourceDistance h)
    {a z z' t : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) a z)
    (p' : CriticalPath Rg (sourceGeometry h) a z')
    (hat : Adjacent Rg a t)
    (hgen : (Q Rg t ⊔ Z Rg z) ⊔ Z Rg z' = stabilizer Rg a)
    (Y : Subgroup (FreeAmalgam Rg)) (hYV : Y ≤ V Rg a)
    (hYN : Q Rg t ≤ normalizer (Y : Set (FreeAmalgam Rg)))
    (hm : ⁅Y,Z Rg z⁆ ≤ Z Rg a) (hm' : ⁅Y,Z Rg z'⁆ ≤ Z Rg a) :
    Y ≤ B Rg a ((sourceGeometry h).Z_normal _) := by
  let N := Y ⊔ Z Rg a
  have hNV : N ≤ V Rg a := sup_le hYV (Z_le_VBall Rg _ 2)
  have hNG : N ≤ stabilizer Rg a :=
    hNV.trans ((sourceGeometry h).V_local _ p.start_color (by
      rw [(sourceGeometry h).distance_constant _ p.start_color]; exact hb))
  have move {w : Vertex Rg} (r : CriticalPath Rg (sourceGeometry h) a w)
      (hh : ⁅Y,Z Rg w⁆ ≤ Z Rg a) : ⁅N,Z Rg w⁆ ≤ Z Rg a :=
    commutator_sup_le_of_relative_normal (stabilizer Rg a) Y (Z Rg a)
      (Z Rg w) (Z Rg a) (Z_normalized Rg _) (le_sup_left.trans hNG)
      (Z_le_stabilizer Rg _) hh (critical_seed_commutator_le h r)
  have hNs : Q Rg t ≤ normalizer (N : Set (FreeAmalgam Rg)) :=
    (le_inf hYN ((show Q Rg t ≤ stabilizer Rg a from
      fun _ hx => hx.2 _ (adjacent_symm Rg hat)).trans (Z_normalized Rg _))).trans
        (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hNn : stabilizer Rg a ≤ normalizer (N : Set (FreeAmalgam Rg)) := by
    rw [←hgen]
    exact sup_le (sup_le hNs
      (le_normalizer_iff_commutator_le_left.mpr ((move p hm).trans le_sup_right)))
      (le_normalizer_iff_commutator_le_left.mpr ((move p' hm').trans le_sup_right))
  exact le_sup_left.trans
    (shifted_normalized_radius_le_slice h e hz hb p N hNV hNn (move p hm))

include h e hz hk in
private theorem controlled_paired_backward_kernels
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    (hb4 : sourceDistance h = 4)
    (hsmall : ∀ a z (_p : CriticalPath Rg (sourceGeometry h) a z),
      (Q Rg z).relIndex (Z Rg a) < 4)
    (hcontrol : ∀ a z (p : CriticalPath Rg (sourceGeometry h) a z),
      ⁅V Rg a ⊓ Q Rg (p.walk.getVert 2),Z Rg z⁆ ≤ Z Rg a)
    {a z z' d t : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) a z)
    (p' : CriticalPath Rg (sourceGeometry h) a z')
    (hat : Adjacent Rg a t) (hdt : Adjacent Rg d t)
    (hgen : (Q Rg t ⊔ Z Rg z) ⊔ Z Rg z' = stabilizer Rg a)
    (hs : 2 < (B Rg a ((sourceGeometry h).Z_normal _)).relIndex (U Rg d)) :
    ∃ q : CriticalPath Rg (sourceGeometry h) d (p.walk.getVert 2),
      ∃ q' : CriticalPath Rg (sourceGeometry h) d (p'.walk.getVert 2),
        q.walk.getVert 1 = t ∧ q'.walk.getVert 1 = t ∧
        q.walk.getVert 2 = a ∧ q'.walk.getVert 2 = a ∧
        Z Rg d ⊓ Q Rg (p.walk.getVert 2) ≠
          Z Rg d ⊓ Q Rg (p'.walk.getVert 2) := by
  have hb := distance_gt_two h e hz hk
  have hda : (cosetGraph Rg).dist d a ≤ 2 := by
    have h1 := SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj Rg _ _).mpr hdt)
    have h2 := SimpleGraph.dist_eq_one_iff_adj.mpr
      ((cosetGraph_adj Rg _ _).mpr (adjacent_symm Rg hat))
    simpa only [h1,h2] using
      (cosetGraph_connected Rg).dist_triangle (u := d) (v := t) (w := a)
  have hZV : Z Rg d ≤ V Rg a := le_iSup_of_le d (le_iSup_of_le hda le_rfl)
  have hd : color Rg d = false := by
    have h1 := adjacent_color_ne Rg hat
    have h2 := adjacent_color_ne Rg hdt
    rw [p.start_color] at h1
    cases he : color Rg d <;> cases ht : color Rg t <;> simp_all
  have extend {w : Vertex Rg} (r : CriticalPath Rg (sourceGeometry h) a w)
      (hn : ¬ Z Rg d ≤ Q Rg (r.walk.getVert 2)) :
      ∃ q : CriticalPath Rg (sourceGeometry h) d (r.walk.getVert 2),
        q.walk.getVert 1 = t ∧ q.walk.getVert 2 = a := by
    have hl : r.walk.length = 4 := r.length_eq_b.trans hb4
    have hb' : 2 ≤ (sourceGeometry h).b Rg := by change 2 ≤ sourceDistance h; omega
    let w₀ : (cosetGraph Rg).Walk d a :=
      .cons ((cosetGraph_adj Rg _ _).mpr hdt)
        (.cons ((cosetGraph_adj Rg _ _).mpr (adjacent_symm Rg hat)) .nil)
    have hw : w₀.length = 2 := rfl
    have hn' : ¬ Z Rg d ≤ Q Rg (r.walk.getVert (r.walk.length-2)) := by
      simpa only [hl,Nat.reduceSub] using hn
    let q := r.prepend_two hb' hd w₀ hw hn'
    have he : r.walk.getVert (r.walk.length-2) = r.walk.getVert 2 := by rw [hl]
    have hh : ∃ q : CriticalPath Rg (sourceGeometry h) d
        (r.walk.getVert (r.walk.length-2)), q.walk.getVert 1 = t ∧ q.walk.getVert 2 = a := by
      refine ⟨q,?_,?_⟩
      · change (r.prepend_two _ _ _ _ _).walk.getVert 1 = t
        rw [r.prepend_two_walk]
        simp only [SimpleGraph.Walk.getVert_append,hw,show 1<2 from by decide,
          ite_true,w₀,SimpleGraph.Walk.getVert_cons_succ,SimpleGraph.Walk.getVert_zero]
      · simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using
          r.prepend_two_overlap hb' hd w₀ hw hn' (i := 0) (Nat.zero_le _)
    rwa [he] at hh
  have separated {v w : Vertex Rg}
      (r : CriticalPath Rg (sourceGeometry h) a v)
      (s : CriticalPath Rg (sourceGeometry h) a w)
      (hgens : (Q Rg t ⊔ Z Rg v) ⊔ Z Rg w = stabilizer Rg a)
      (q : CriticalPath Rg (sourceGeometry h) d (r.walk.getVert 2))
      (hq1 : q.walk.getVert 1 = t) (hq2 : q.walk.getVert 2 = a) :
      ¬ Z Rg d ⊓ Q Rg (r.walk.getVert 2) ≤ Q Rg (s.walk.getVert 2) := by
    intro hc
    have hh := paired_strict_kernel_escape h e hz hk u hR hb4 r s q hq2
      (hsmall _ _ q) (by rwa [hq1]) hs
    have hKV : Z Rg d ⊓ Q Rg (r.walk.getVert 2) ≤ V Rg a := inf_le_left.trans hZV
    exact hh.elim
      (fun hn => hn ((commutator_mono (le_inf hKV inf_le_right) le_rfl).trans (hcontrol _ _ r)))
      (fun hn => hn ((commutator_mono (le_inf hKV hc) le_rfl).trans (hcontrol _ _ s)))
  by_cases hn : Z Rg d ≤ Q Rg (p.walk.getVert 2)
  · by_cases hn' : Z Rg d ≤ Q Rg (p'.walk.getVert 2)
    · have hZB := paired_controlled_subgroup_le_slice h e hz hb p p' hat hgen
        (Z Rg d) hZV
        ((show Q Rg t ≤ stabilizer Rg d from
          fun _ hx => hx.2 _ (adjacent_symm Rg hdt)).trans (Z_normalized Rg d))
        ((commutator_mono (le_inf hZV hn) le_rfl).trans (hcontrol _ _ p))
        ((commutator_mono (le_inf hZV hn') le_rfl).trans (hcontrol _ _ p'))
      have hi := relIndex_eq_one.mpr ((DistanceEight.U_le_Z Rg d).trans hZB)
      omega
    obtain ⟨q',hq1',hq2'⟩ := extend p' hn'
    have hgens : (Q Rg t ⊔ Z Rg z') ⊔ Z Rg z = stabilizer Rg a := by
      simpa only [sup_assoc,sup_comm,sup_left_comm] using hgen
    have hc := separated p' p hgens q' hq1' hq2'
    obtain ⟨q,hq1,hq2⟩ := extend p (fun hh => hc (inf_le_left.trans hh))
    exact ⟨q,q',hq1,hq1',hq2,hq2',fun he => hc (he.symm ▸ inf_le_right)⟩
  · obtain ⟨q,hq1,hq2⟩ := extend p hn
    have hc := separated p p' hgen q hq1 hq2
    obtain ⟨q',hq1',hq2'⟩ := extend p' (fun hh => hc (inf_le_left.trans hh))
    exact ⟨q,q',hq1,hq1',hq2,hq2',fun he => hc (he ▸ inf_le_right)⟩

include h e hz hk in
private theorem controlled_strict_plane_slice_false
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    (hb4 : sourceDistance h = 4)
    (hsmall : ∀ a z (_p : CriticalPath Rg (sourceGeometry h) a z),
      (Q Rg z).relIndex (Z Rg a) < 4)
    (hcontrol : ∀ a z (p : CriticalPath Rg (sourceGeometry h) a z),
      ⁅V Rg a ⊓ Q Rg (p.walk.getVert 2),Z Rg z⁆ ≤ Z Rg a)
    {z delta : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z)
    (hd : Adjacent Rg delta (p.walk.getVert 1))
    (hs : 2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex (U Rg delta)) :
    False := by
  obtain ⟨t,hat,r,hr,p',hverts,hps,hgen,hpair,hnorm,hinside,hneq,_,_,_,_,_,_,htransport⟩ :=
    remaining_small_critical_paired_kernel_selectors h e hz hk u (Or.inl hR) p (hsmall _ _ p)
  obtain ⟨g,hg,hgt,hstrict,_⟩ := htransport delta hd hs
  let d := act Rg g delta
  have hdt : Adjacent Rg d t := by
    rw [←hgt]
    exact (adjacent_act_iff Rg g _ _).mpr hd
  rw [plane_edgeOffenderJoin_eq h e hz hk u hR rfl hat] at hgen
  obtain ⟨q,q',hq1,hq1',hqa,hqa',hne⟩ :=
    controlled_paired_backward_kernels h e hz hk u hR hb4 hsmall hcontrol p p'
      hat hdt hgen hstrict
  have hlarge := small_critical_distinct_kernels_joint_image h e hz hk q q'
    (hsmall _ _ q) (hsmall _ _ q') hne
  obtain ⟨s,hds,_,hgens⟩ := plane_paired_midpoints_generate h e hz hk u hR q q'
    hq1 hq1' (hsmall _ _ q) hlarge
  have hat₀ : Adjacent Rg (alpha Rg) (p.walk.getVert 1) := by
    apply (cosetGraph_adj Rg _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using
      p.walk.adj_getVert_succ (i := 0) (p.length_eq_b ▸ sourceDistance_pos h)
  obtain ⟨j,hj | hj⟩ := edge_transitive Rg hat₀ hds
  · have hdelta : Adjacent Rg (act Rg j delta) s := by
      rw [←hj.2]
      exact (adjacent_act_iff Rg j _ _).mpr hd
    have hstrict' : 2 < (B Rg d ((sourceGeometry h).Z_normal _)).relIndex (U Rg (act Rg j delta)) := by
      rw [←hj.1,Escape.PairingControl.FirstPairing.B_act
        (geometry := sourceGeometry h) (distance_gt_two h e hz hk) _ _ rfl,
        U_act,relIndex_map_map_of_injective _ _ (MulAut.conj _).injective]
      exact hs
    obtain ⟨b,b',_,_,_,_,hne'⟩ :=
      controlled_paired_backward_kernels h e hz hk u hR hb4 hsmall hcontrol q q'
        hds hdelta (by simpa only [sup_assoc] using hgens) hstrict'
    rw [hqa,hqa'] at hne'
    exact hne' rfl
  · have hsc : color Rg s = false := by
      rw [←hj.1,action_preserves_color]
      rfl
    exact (adjacent_color_ne Rg hds) (q.start_color.trans hsc.symm)

include h e hz hk in
/-- On the original distance-four plane graph, uniformly small critical
images cannot control every full radius kernel modulo its starting seed.
The second paired comparison uses the actual backward paths' common midpoint. -/
theorem plane_four_radius_kernel_escape
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    (hb4 : sourceDistance h = 4)
    (hsmall : ∀ a z (_p : CriticalPath Rg (sourceGeometry h) a z),
      (Q Rg z).relIndex (Z Rg a) < 4) :
    ∃ a z, ∃ p : CriticalPath Rg (sourceGeometry h) a z,
      ¬ ⁅V Rg a ⊓ Q Rg (p.walk.getVert 2),Z Rg z⁆ ≤ Z Rg a := by
  by_contra! hcontrol
  obtain ⟨z,⟨p⟩⟩ := CriticalPath.exists_from (R := Rg) (geometry := sourceGeometry h)
    (a := alpha Rg) rfl
  have hat₀ : Adjacent Rg (alpha Rg) (p.walk.getVert 1) := by
    apply (cosetGraph_adj Rg _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using
      p.walk.adj_getVert_succ (i := 0) (p.length_eq_b ▸ sourceDistance_pos h)
  have hslice {a d t : Vertex Rg} (ha : color Rg a = false)
      (hat : Adjacent Rg a t) (hdt : Adjacent Rg d t) :
      (B Rg a ((sourceGeometry h).Z_normal _)).relIndex (U Rg d) ≤ 2 := by
    by_contra! hs
    obtain ⟨j,hj | hj⟩ := edge_transitive Rg hat hat₀
    · have hdelta : Adjacent Rg (act Rg j d) (p.walk.getVert 1) := by
        rw [←hj.2]
        exact (adjacent_act_iff Rg j _ _).mpr hdt
      have hstrict : 2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
          (U Rg (act Rg j d)) := by
        rw [←hj.1,Escape.PairingControl.FirstPairing.B_act
          (geometry := sourceGeometry h) (distance_gt_two h e hz hk) _ _ ha,
          U_act,relIndex_map_map_of_injective _ _ (MulAut.conj _).injective]
        exact hs
      exact controlled_strict_plane_slice_false h e hz hk u hR hb4 hsmall hcontrol p hdelta hstrict
    · have htc : color Rg (p.walk.getVert 1) = false := by
        rw [←hj.1,action_preserves_color]
        exact ha
      exact (adjacent_color_ne Rg hat₀) htc.symm
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb4
  have hct : Adjacent Rg (p.walk.getVert 2) (p.walk.getVert 1) :=
    adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp
      (p.walk.adj_getVert_succ (i := 1) (by omega)))
  have hc : color Rg (p.walk.getVert 2) = false :=
    (p.vertex_color (by omega)).mpr (by decide)
  have hcs : Adjacent Rg (p.walk.getVert 2) (p.walk.getVert 3) :=
    (cosetGraph_adj Rg _ _).mp (p.walk.adj_getVert_succ (i := 2) (by omega))
  have hzs : Adjacent Rg z (p.walk.getVert 3) := by
    apply adjacent_symm Rg
    apply (cosetGraph_adj Rg _ _).mp
    have hh := p.walk.adj_getVert_succ (i := 3) (by omega)
    simpa only [show 3+1=p.walk.length by omega,SimpleGraph.Walk.getVert_length] using hh
  have ht := plane_four_selected_configuration_of_slices h e hz hk u hR hb4 p
    (hslice rfl hat₀ hct) (hslice hc hcs hzs)
  exact (Nat.not_lt_of_ge (hslice hc hct hat₀)) ht.2.2.2.1


include h e hz hk in
/-- The centrally generated full-omega case forces a genuine full radius
kernel line and a strictly larger endpoint commutator. No strict slice,
backward-path selection or failure-of-control premise is supplied. -/
theorem plane_small_four_radius_line
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    (hb4 : sourceDistance h = 4)
    (hsmall : ∀ a z (_p : CriticalPath Rg (sourceGeometry h) a z),
      (Q Rg z).relIndex (Z Rg a) < 4) :
    ∃ a z, ∃ p : CriticalPath Rg (sourceGeometry h) a z,
      let Y := V Rg a ⊓ Q Rg (p.walk.getVert 2)
      let H := ⁅Y,X Rg z ⊓ Q Rg a⁆
      Nat.card H = 2 ∧
      ⁅V Rg a ⊓ Q Rg (p.walk.getVert 3),X Rg z ⊓ Q Rg a⁆ = H ∧
      H ≤ Z Rg a ⊓ Z Rg (p.walk.getVert 2) ∧
      H ≤ centralizer ((V Rg a ⊔ V Rg (p.walk.getVert 2) :
        Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg)) ∧
      H < ⁅Y,X Rg z⁆ ∧
      ⁅Y,X Rg z⁆ ≤ Z Rg (p.walk.getVert 3) ⊓ Q Rg a ∧
      ⁅⁅Y,X Rg z⁆,Q Rg (p.walk.getVert 3)⁆ = ⊥ ∧
      ¬ ⁅Y,X Rg z⁆ ≤ Z Rg a := by
  obtain ⟨a,z,p,hn⟩ := plane_four_radius_kernel_escape h e hz hk u hR hb4 hsmall
  have hXZ := (plane_small_four_omega_generated h e hz hk u hR hb4 hsmall z p.end_color).2
  have hnot : ¬ ⁅V Rg a ⊓ Q Rg (p.walk.getVert 2),X Rg z⁆ ≤ Z Rg a := by
    rwa [hXZ]
  have hd := plane_four_full_kernel_line h e hz hk u hR hb4 hsmall p
    (V Rg a ⊓ Q Rg (p.walk.getVert 2)) inf_le_left inf_le_right hnot
  exact ⟨a,z,p,hd.1,hd.2.1,hd.2.2.1,hd.2.2.2.1,hd.2.2.2.2.1,
    hd.2.2.2.2.2.1,hd.2.2.2.2.2.2,hnot⟩

omit hk in
include h e hz in
/-- Whole-core application of the unavoidable full-omega radius line.
Both full moving covers, the original cubic kernel and the Borel alternative
are retained. The nonzero line still requires the terminal contradiction. -/
theorem coreExhaustion_or_cubic_plane_radius_line :
    CoreExhaustion L R ∨ ∃ hk : layerKernel L R = extensionKernel h,
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
      let Y := V Rg a ⊓ Q Rg (p.walk.getVert 2)
      let H := ⁅Y,X Rg z ⊓ Q Rg a⁆
      Nat.card H = 2 ∧
      ⁅V Rg a ⊓ Q Rg (p.walk.getVert 3),X Rg z ⊓ Q Rg a⁆ = H ∧
      H ≤ Z Rg a ⊓ Z Rg (p.walk.getVert 2) ∧
      H ≤ centralizer ((V Rg a ⊔ V Rg (p.walk.getVert 2) :
        Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg)) ∧
      H < ⁅Y,X Rg z⁆ ∧
      ⁅Y,X Rg z⁆ ≤ Z Rg (p.walk.getVert 3) ⊓ Q Rg a ∧
      ⁅⁅Y,X Rg z⁆,Q Rg (p.walk.getVert 3)⁆ = ⊥ ∧
      ¬ ⁅Y,X Rg z⁆ ≤ Z Rg a)) := by
  rcases coreExhaustion_or_cubic_plane_paths h e hz with
    hex | ⟨hk,hs,hb,hcovers,u,hborel | ⟨hplane,_⟩⟩
  · exact Or.inl hex
  · exact Or.inr ⟨hk,hs,hb,hcovers,u,Or.inl hborel⟩
  · exact Or.inr ⟨hk,hs,hb,hcovers,u,Or.inr ⟨hplane,
      fun hb4 hsmall => plane_small_four_radius_line h e hz hk u hplane hb4 hsmall⟩⟩

omit hk in
include h e hz in
/-- Literal C.1.32 application on the original cubic graph. Distance four
and uniformly small critical images remain premises of the radius assertion;
neither core exhaustion nor the full reconstruction is asserted. -/
theorem rankTwo_or_cubic_plane_radius_line :
    RankTwoAlternatives L R ∨ ∃ hk : layerKernel L R = extensionKernel h,
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
      let Y := V Rg a ⊓ Q Rg (p.walk.getVert 2)
      let H := ⁅Y,X Rg z ⊓ Q Rg a⁆
      Nat.card H = 2 ∧
      ⁅V Rg a ⊓ Q Rg (p.walk.getVert 3),X Rg z ⊓ Q Rg a⁆ = H ∧
      H ≤ Z Rg a ⊓ Z Rg (p.walk.getVert 2) ∧
      H ≤ centralizer ((V Rg a ⊔ V Rg (p.walk.getVert 2) :
        Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg)) ∧
      H < ⁅Y,X Rg z⁆ ∧
      ⁅Y,X Rg z⁆ ≤ Z Rg (p.walk.getVert 3) ⊓ Q Rg a ∧
      ⁅⁅Y,X Rg z⁆,Q Rg (p.walk.getVert 3)⁆ = ⊥ ∧
      ¬ ⁅Y,X Rg z⁆ ≤ Z Rg a)) :=
  (coreExhaustion_or_cubic_plane_radius_line h e hz).imp
    (rankTwo_of_exhaustion h e hz) id


end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
