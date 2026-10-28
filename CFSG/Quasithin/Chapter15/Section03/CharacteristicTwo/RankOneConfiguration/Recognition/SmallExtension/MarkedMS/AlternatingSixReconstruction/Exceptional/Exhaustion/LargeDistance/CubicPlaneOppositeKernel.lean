module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneOppositeStabilizer
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneBackward
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneOppositeStabilizer


/-!
# The opposite full critical kernel carries the entire radius commutator

For the retained displaced paths a--z and b--z, put T = [Z_a,Z_z]
and F_b = Z_z intersect Q_b. The reciprocal critical actions show that
T is not contained in F_b. Since F_b has index two in the full seed,
Z_z = F_b T and F_b intersects T trivially. Every subgroup of V_a
centralizes T, so its commutator with F_b equals its commutator with Z_z.
This is a statement about the full seed, including its central attachment.

Apply this to the original midpoint radius kernel Y and the entire
last-edge radius kernel W. Their equal endpoint images give
W = Y (W intersect Q_z); the extra factor centralizes Z_z. Thus their
commutators with F_b and Z_z all coincide. This common subgroup strictly
contains their order-two commutator with F_a = Z_z intersect Q_a, has at
least four elements, and escapes Z_a. It lies in the original last-edge
seed and centralizes that edge kernel. The selector retains the same
opposite-edge element and every vertex of both displaced paths.

This comparison excludes an order-two bound on the full opposite-kernel
commutator for these particular displaced paths. Such a bound cannot be
substituted for the separate shifted-path comparison in MS93 (5.12).
The two stabilizer indices in the preceding modules likewise concern
different subgroups. The terminal source contradiction, other image and
distance cases, both core exhaustions and unconditional reconstruction
remain open. Both full moving covers and the original cubic projection
with kernel E, including its nontrivial odd quotient E/Q, are retained.

The internal imports reuse the earlier index-two supplement and central
attachment calculations without changing their public boundaries.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), comparisons toward (5.12), printed pp.924--927;
Aschbacher--Smith C.1.31--32, printed pp.135--136.
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
/-- The starting critical line supplements the opposite full critical kernel.
Every subgroup of the starting radius has the same commutator with that
kernel as with the whole endpoint seed. -/
theorem plane_opposite_full_kernel_supplement
    {a b z : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) a z)
    (q : CriticalPath Rg (sourceGeometry h) b z)
    (hp : (Q Rg z).relIndex (Z Rg a) < 4)
    (hq : (Q Rg z).relIndex (Z Rg b) < 4)
    (hcross : ⁅Z Rg b,⁅Z Rg a,Z Rg z⁆⁆ = ⁅Z Rg b,Z Rg z⁆) :
    let T := ⁅Z Rg a,Z Rg z⁆
    let F := Z Rg z ⊓ Q Rg b
    F ⊔ T = Z Rg z ∧ T ⊓ F = ⊥ ∧
      ∀ Y : Subgroup (FreeAmalgam Rg), Y ≤ V Rg a →
        ⁅Y,F⁆ = ⁅Y,Z Rg z⁆ := by
  let T := ⁅Z Rg a,Z Rg z⁆
  let F := Z Rg z ⊓ Q Rg b
  have hTZ : T ≤ Z Rg z := le_normalizer_iff_commutator_le_right.mp
    ((Z_le_stabilizer_of_dist_le a _ p.critical.1.le).trans (Z_normalized Rg z))
  have hTa : T ≤ Z Rg a := le_normalizer_iff_commutator_le_left.mp
    ((critical_Z_le_stabilizer Rg (sourceGeometry h) a p.start_color
      (by rw [(sourceGeometry h).distance_constant _ p.start_color]; exact sourceDistance_pos h)
      p.critical).trans (Z_normalized Rg a))
  have hcard := small_critical_commutator_card h e hz hk p hp
  have hn : ¬ T ≤ F := by
    intro hh
    have he : ⁅Z Rg b,T⁆ = ⊥ := le_bot_iff.mp
      ((commutator_mono le_rfl (hh.trans inf_le_right)).trans_eq
        (Z_centralizes_Q Rg b q.start_color))
    change ⁅Z Rg b,⁅Z Rg a,Z Rg z⁆⁆ = ⊥ at he
    rw [hcross] at he
    have hc := small_critical_commutator_card h e hz hk q hq
    rw [he,card_bot] at hc
    omega
  have hi : F.relIndex (Z Rg z) = 2 := by
    rw [inf_relIndex_left]
    exact (small_critical_indices h e hz hk q hq).2
  have hs : F ⊔ T = Z Rg z := by
    have hh := index_two_supplement T F (Z Rg z) hTZ hi hn
    simpa only [inf_eq_right.mpr (show F ≤ Z Rg z from inf_le_left)] using hh
  have hd : T ⊓ F = ⊥ := by
    let : Finite T := Nat.finite_of_card_ne_zero (by change Nat.card T = 2 at hcard; omega)
    let : Finite (T ⊓ F : Subgroup (FreeAmalgam Rg)) :=
      Finite.of_injective (inclusion (show T ⊓ F ≤ T from inf_le_left)) (inclusion_injective _)
    have hlo : Nat.card (T ⊓ F : Subgroup (FreeAmalgam Rg)) ≤ 1 := by
      by_contra! hh
      have he : T ⊓ F = T := eq_of_le_of_card_ge inf_le_left (by
        change Nat.card T = 2 at hcard
        omega)
      exact hn (he ▸ inf_le_right)
    exact eq_bot_of_card_le _ hlo
  refine ⟨hs,hd,?_⟩
  intro Y hYV
  let := (sourceGeometry h).Z_elementary (sourceDistance_pos h) z p.end_color
  have hTF : T ≤ normalizer (F : Set (FreeAmalgam Rg)) :=
    ((hTZ.trans (le_centralizer (H := Z Rg z))).trans
      (centralizer_le (show F ≤ Z Rg z from inf_le_left))).trans
        (Subgroup.centralizer_le_normalizer _)
  have hTY : T ≤ centralizer (Y : Set (FreeAmalgam Rg)) :=
    (hTa.trans (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q Rg a p.start_color))).trans
        (centralizer_le (hYV.trans
          ((sourceGeometry h).V_le_Q (distance_gt_two h e hz hk) a p.start_color)))
  calc
    ⁅Y,F⁆ = ⁅F,Y⁆ := commutator_comm _ _
    _ = ⁅F ⊔ T,Y⁆ := (commutator_sup_of_central_attachment F T Y hTF hTY).symm
    _ = ⁅Z Rg z,Y⁆ := congrArg (fun A => ⁅A,Y⁆) hs
    _ = ⁅Y,Z Rg z⁆ := commutator_comm _ _

private theorem same_index_core_supplement {F : Type*} [Group F]
    (Y W Q : Subgroup F) (hYW : Y ≤ W)
    (hN : W ≤ normalizer (Q : Set F))
    (hiY : Q.relIndex Y = 4) (hiW : Q.relIndex W = 4) :
    Y ⊔ (W ⊓ Q) = W := by
  let K := W ⊓ Q
  have hNK : W ≤ normalizer (K : Set F) :=
    (le_inf W.le_normalizer hN).trans inf_normalizer_le_normalizer_inf
  let _ : (K.subgroupOf W).Normal := normal_subgroupOf_of_le_normalizer hNK
  have hi : K.relIndex Y = 4 := by
    change (W ⊓ Q).relIndex Y = 4
    rw [inf_comm,←relIndex_inf_mul_relIndex,inf_eq_right.mpr hYW,
      relIndex_eq_one.mpr hYW,mul_one]
    exact hiY
  have hs := relIndex_sup_left (Y.subgroupOf W) (K.subgroupOf W)
  rw [←subgroupOf_sup inf_le_left hYW,
    relIndex_subgroupOf (sup_le inf_le_left hYW),relIndex_subgroupOf hYW,hi] at hs
  have hm := relIndex_mul_relIndex K (K ⊔ Y) W le_sup_left (sup_le inf_le_left hYW)
  rw [hs,show K.relIndex W = 4 by rw [inf_relIndex_left]; exact hiW] at hm
  have he : (K ⊔ Y).relIndex W = 1 := by omega
  exact (sup_comm Y K).trans (le_antisymm (sup_le inf_le_left hYW) (relIndex_eq_one.mp he))

include h in
private theorem plane_radius_equal_endpoint_commutators
    {a z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (Y W : Subgroup (FreeAmalgam Rg)) (hYW : Y ≤ W)
    (hWG : W ≤ stabilizer Rg z)
    (hiY : (Q Rg z).relIndex Y = 4) (hiW : (Q Rg z).relIndex W = 4) :
    Y ⊔ (W ⊓ Q Rg z) = W ∧ ⁅Y,Z Rg z⁆ = ⁅W,Z Rg z⁆ := by
  have hs := same_index_core_supplement Y W (Q Rg z) hYW
    (hWG.trans (Q_normalized Rg z)) hiY hiW
  have hfix : W ⊓ Q Rg z ≤ centralizer (Z Rg z : Set (FreeAmalgam Rg)) :=
    inf_le_right.trans (le_centralizer_iff.mp
      (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q Rg z p.end_color)))
  have hCZ : ⁅Y,Z Rg z⁆ ≤ Z Rg z := le_normalizer_iff_commutator_le_right.mp
    ((hYW.trans hWG).trans (Z_normalized Rg z))
  have hCN : W ≤ normalizer ((⁅Y,Z Rg z⁆ : Subgroup (FreeAmalgam Rg)) :
      Set (FreeAmalgam Rg)) := by
    calc
      W = Y ⊔ (W ⊓ Q Rg z) := hs.symm
      _ ≤ _ := sup_le (normalizer_commutator_ge_left Y (Z Rg z))
        ((hfix.trans (centralizer_le hCZ)).trans (Subgroup.centralizer_le_normalizer _))
  refine ⟨hs,le_antisymm (commutator_mono hYW le_rfl) ?_⟩
  calc
    ⁅W,Z Rg z⁆ = ⁅Y ⊔ (W ⊓ Q Rg z),Z Rg z⁆ := congrArg (fun A => ⁅A,Z Rg z⁆) hs.symm
    _ ≤ ⁅Y,Z Rg z⁆ := commutator_sup_le_of_relative_normal W Y (W ⊓ Q Rg z)
      (Z Rg z) ⁅Y,Z Rg z⁆ hCN hYW inf_le_left le_rfl
      ((commutator_eq_bot_iff_le_centralizer.mpr hfix).le.trans bot_le)

include h e hz hk in
/-- On the same displaced critical paths, both original radius kernels have
identical commutators with the opposite full critical kernel and the entire
endpoint seed. This common commutator has at least four elements and strictly
contains their order-two commutator with the original critical kernel. -/
theorem plane_small_four_full_kernel_comparison
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
            let W := V Rg a ⊓ Q Rg (p.walk.getVert 3)
            let F := Z Rg z ⊓ Q Rg a
            let F' := Z Rg z ⊓ Q Rg (act Rg g⁻¹ a)
            let T := ⁅Z Rg a,Z Rg z⁆
            let C := ⁅Y,Z Rg z⁆
            F' ⊔ T = Z Rg z ∧ T ⊓ F' = ⊥ ∧
              Y ⊔ (W ⊓ Q Rg z) = W ∧
              ⁅Y,F'⁆ = C ∧ ⁅W,F'⁆ = C ∧ ⁅W,Z Rg z⁆ = C ∧
              ⁅Y,F⁆ = ⁅W,F⁆ ∧ Nat.card (⁅Y,F⁆ : Subgroup (FreeAmalgam Rg)) = 2 ∧
              ⁅Y,F⁆ < C ∧ 4 ≤ Nat.card C ∧ ¬ C ≤ Z Rg a ∧
              C ≤ Z Rg (p.walk.getVert 3) ⊓ Q Rg a ∧
              ⁅C,Q Rg (p.walk.getVert 3)⁆ = ⊥ := by
  obtain ⟨a,z,p,_,s,hzs,hgen,hiY,hiW,g,hg,hfix,hescape,_,hesc,_,q,hverts,_,_,_,hgeom⟩ :=
    plane_small_four_radius_line_transfer h e hz hk u hR hb4 hsmall
  let Y := V Rg a ⊓ Q Rg (p.walk.getVert 2)
  let W := V Rg a ⊓ Q Rg (p.walk.getVert 3)
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb4
  have hct : Adjacent Rg (p.walk.getVert 2) (p.walk.getVert 3) :=
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
  have hYW : Y ≤ W := le_inf inf_le_left (by simpa only [hl,Nat.reduceSub] using hYt)
  have hAY : Z Rg a ≤ Y := by
    refine le_inf (Z_le_VBall Rg _ 2) ?_
    apply Z_le_Q_of_dist_lt Rg _ ((sourceGeometry h).exists_critical _ p.start_color)
    rw [(sourceGeometry h).distance_constant _ p.start_color,p.dist_start (by omega)]
    exact distance_gt_two h e hz hk
  have hXZ := (plane_small_four_omega_generated h e hz hk u hR hb4 hsmall z p.end_color).2
  rw [hXZ] at hescape hesc
  have hWG : W ≤ stabilizer Rg z :=
    inf_le_right.trans (fun _ hx => hx.2 _ (adjacent_symm Rg hzt))
  have hYG : Y ≤ stabilizer Rg z := hYW.trans hWG
  have hHZ : ⁅Y,Z Rg z ⊓ Q Rg a⁆ ≤ Z Rg z :=
    (commutator_mono le_rfl inf_le_left).trans
      (le_normalizer_iff_commutator_le_right.mp (hYG.trans (Z_normalized Rg z)))
  have hH'Z : (⁅Y,Z Rg z ⊓ Q Rg a⁆ : Subgroup (FreeAmalgam Rg)).map
      (MulAut.conj g).toMonoidHom ≤ Z Rg z :=
    (map_mono hHZ).trans_eq (mem_normalizer_iff_map_conj_eq.mp
      (Z_normalized Rg z (hg.2 _ (adjacent_symm Rg hzs))))
  have hnot : ¬ ⁅Y,Z Rg z⁆ ≤ Z Rg a :=
    fun hh => hesc ((commutator_mono le_rfl hH'Z).trans hh)
  have hcross' := (plane_transferred_critical_plane h e hz hk u hR p (hsmall _ _ p)
    Y inf_le_left hYt hAY hnot hzs g hg hescape hesc).2.1
  have hsupp := plane_opposite_full_kernel_supplement h e hz hk p q
    (hsmall _ _ p) (hsmall _ _ q) hcross'
  have hequal := plane_radius_equal_endpoint_commutators h p Y W hYW hWG hiY hiW
  have hline := plane_radius_subactor_kernel_line h e hz hk u hR p (hsmall _ _ p)
    Y inf_le_left hYt hnot
  simp only [hl,Nat.reduceSub] at hline
  let C := ⁅Y,Z Rg z⁆
  let H := ⁅Y,Z Rg z ⊓ Q Rg a⁆
  have hCZ : C ≤ Z Rg z := hline.2.2.2.2.trans
    (inf_le_left.trans (adjacent_Z_le Rg p.end_color hzt))
  let := finite_Z Rg z
  let : Finite C := Finite.of_injective (inclusion hCZ) (inclusion_injective _)
  have hbig : 4 ≤ Nat.card C := by
    have hdiv : 2 ∣ Nat.card C := by
      rw [←hline.1]
      exact card_dvd_of_le hline.2.2.2.1.le
    have hlo : 2 < Nat.card C := by
      by_contra! hn
      have he : H = C := eq_of_le_of_card_ge hline.2.2.2.1.le (by
        have hc : Nat.card H = 2 := hline.1
        omega)
      exact (ne_of_lt hline.2.2.2.1) he
    omega
  have hCfix : ⁅C,Q Rg (p.walk.getVert 3)⁆ = ⊥ := by
    apply commutator_eq_bot_iff_le_centralizer.mpr
    intro v hv
    have hh := (hline.2.2.2.2 hv).1
    rw [Z,if_neg (by simp [ht])] at hh
    exact (mem_omegaCenter_iff.mp hh).2.2
  exact ⟨a,z,p,s,hzs,hgen,g,hg,hfix,q,hverts,hgeom,
    hsupp.1,hsupp.2.1,hequal.1,hsupp.2.2 Y inf_le_left,
    (hsupp.2.2 W inf_le_left).trans hequal.2.symm,hequal.2.symm,
    hline.2.1.symm,hline.1,hline.2.2.2.1,hbig,hnot,hline.2.2.2.2,hCfix⟩

omit hk in
include h e hz in
/-- Whole-core application of the literal full-kernel comparison. The opposite
kernel has the same large commutator as the full endpoint seed; the original
kernel still has its separate order-two commutator. -/
theorem coreExhaustion_or_cubic_full_kernel_comparison :
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
              ∃ s, Adjacent Rg z s ∧
                Q Rg s ⊔ (V Rg a ⊓ Q Rg (p.walk.getVert 2)) = stabilizer Rg z ∧
                ∃ g ∈ Q Rg s, act Rg g⁻¹ z = z ∧
                  ∃ q : CriticalPath Rg (sourceGeometry h) (act Rg g⁻¹ a) z,
                    (∀ i, q.walk.getVert i = act Rg g⁻¹ (p.walk.getVert i)) ∧
                    (∀ i j, (cosetGraph Rg).dist (p.walk.getVert i) (q.walk.getVert j) =
                      (4-i) + (4-j)) ∧
                    let Y := V Rg a ⊓ Q Rg (p.walk.getVert 2)
                    let W := V Rg a ⊓ Q Rg (p.walk.getVert 3)
                    let F := Z Rg z ⊓ Q Rg a
                    let F' := Z Rg z ⊓ Q Rg (act Rg g⁻¹ a)
                    let T := ⁅Z Rg a,Z Rg z⁆
                    let C := ⁅Y,Z Rg z⁆
                    F' ⊔ T = Z Rg z ∧ T ⊓ F' = ⊥ ∧
                      Y ⊔ (W ⊓ Q Rg z) = W ∧
                      ⁅Y,F'⁆ = C ∧ ⁅W,F'⁆ = C ∧ ⁅W,Z Rg z⁆ = C ∧
                      ⁅Y,F⁆ = ⁅W,F⁆ ∧ Nat.card (⁅Y,F⁆ : Subgroup (FreeAmalgam Rg)) = 2 ∧
                      ⁅Y,F⁆ < C ∧ 4 ≤ Nat.card C ∧ ¬ C ≤ Z Rg a ∧
                      C ≤ Z Rg (p.walk.getVert 3) ⊓ Q Rg a ∧
                      ⁅C,Q Rg (p.walk.getVert 3)⁆ = ⊥)) := by
  rcases coreExhaustion_or_cubic_plane_paths h e hz with
    hex | ⟨hk,hs,hb,hcovers,u,hborel | ⟨hplane,_⟩⟩
  · exact Or.inl hex
  · exact Or.inr ⟨hk,hs,hb,hcovers,u,Or.inl hborel⟩
  · exact Or.inr ⟨hk,hs,hb,hcovers,u,Or.inr ⟨hplane,
      fun hb4 hsmall => plane_small_four_full_kernel_comparison h e hz hk u hplane hb4 hsmall⟩⟩

omit hk in
include h e hz in
/-- Literal C.1.32 application, with both full covers and the original cubic
projection. The comparison retains the larger opposite-kernel commutator. -/
theorem rankTwo_or_cubic_full_kernel_comparison :
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
              ∃ s, Adjacent Rg z s ∧
                Q Rg s ⊔ (V Rg a ⊓ Q Rg (p.walk.getVert 2)) = stabilizer Rg z ∧
                ∃ g ∈ Q Rg s, act Rg g⁻¹ z = z ∧
                  ∃ q : CriticalPath Rg (sourceGeometry h) (act Rg g⁻¹ a) z,
                    (∀ i, q.walk.getVert i = act Rg g⁻¹ (p.walk.getVert i)) ∧
                    (∀ i j, (cosetGraph Rg).dist (p.walk.getVert i) (q.walk.getVert j) =
                      (4-i) + (4-j)) ∧
                    let Y := V Rg a ⊓ Q Rg (p.walk.getVert 2)
                    let W := V Rg a ⊓ Q Rg (p.walk.getVert 3)
                    let F := Z Rg z ⊓ Q Rg a
                    let F' := Z Rg z ⊓ Q Rg (act Rg g⁻¹ a)
                    let T := ⁅Z Rg a,Z Rg z⁆
                    let C := ⁅Y,Z Rg z⁆
                    F' ⊔ T = Z Rg z ∧ T ⊓ F' = ⊥ ∧
                      Y ⊔ (W ⊓ Q Rg z) = W ∧
                      ⁅Y,F'⁆ = C ∧ ⁅W,F'⁆ = C ∧ ⁅W,Z Rg z⁆ = C ∧
                      ⁅Y,F⁆ = ⁅W,F⁆ ∧ Nat.card (⁅Y,F⁆ : Subgroup (FreeAmalgam Rg)) = 2 ∧
                      ⁅Y,F⁆ < C ∧ 4 ≤ Nat.card C ∧ ¬ C ≤ Z Rg a ∧
                      C ≤ Z Rg (p.walk.getVert 3) ⊓ Q Rg a ∧
                      ⁅C,Q Rg (p.walk.getVert 3)⁆ = ⊥)) :=
  (coreExhaustion_or_cubic_full_kernel_comparison h e hz).imp
    (rankTwo_of_exhaustion h e hz) id

end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
