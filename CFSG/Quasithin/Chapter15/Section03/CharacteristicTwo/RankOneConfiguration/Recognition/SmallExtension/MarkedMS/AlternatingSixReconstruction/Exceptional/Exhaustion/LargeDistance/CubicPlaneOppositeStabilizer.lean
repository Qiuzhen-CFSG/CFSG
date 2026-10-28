module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneCriticalPlane

/-!
# Exact opposite-kernel stabilizers on the displaced cubic paths

On the same critical paths from a and b to z, let T = [Z_a,Z_z] and
T' = [Z_b,Z_z]. The original midpoint radius kernel and the whole last-edge
radius kernel both preserve Z_z intersect Q_a. In each of these two actors
Y, the setwise stabilizer of the full opposite kernel Z_z intersect Q_b is
exactly Y intersect Q_z. The pointwise fixer of T' has the same intersection,
and the opposite-kernel stabilizer has index four in Y. In particular,
Y intersect G_b and Y intersect Q_b lie in Q_z.

The four-element endpoint image gives an upper bound of four on the line
stabilizer index. Index one contradicts the reciprocal seed action. At
index two, the line stabilizer and the starting seed generate Y, forcing Y
to preserve T join T', contrary to the proved radius obstruction. Thus the
index is four, and multiplicativity of indices identifies the stabilizer.
The existing exact critical-kernel/line identity then transfers this
calculation to the entire seed kernel, including its central attachment.

The selector retains the original opposite-edge element and every vertex
of its displaced critical path. The whole-core and literal C.1.32 consumers
retain the projection kernel E, its odd E/Q, the nonsylow radical and both
moving covers of orders sixteen and thirty-two. These equalities do not
supply a contradictory upper bound for the opposite-kernel stabilizer.
That terminal comparison, the remaining image/distance/Borel branches,
both core exhaustions and unconditional reconstruction remain open.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), stabilizer comparisons toward (5.12), printed pp.924--927;
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

private theorem index_two_supplement {F : Type*} [Group F] (A N V : Subgroup F)
    (hAV : A ≤ V) (hidx : N.relIndex V = 2) (hne : ¬ A ≤ N) :
    (V ⊓ N) ⊔ A = V := by
  classical
  apply le_antisymm (sup_le inf_le_left hAV)
  obtain ⟨a,ha,han⟩ := Set.not_subset.mp hne
  change a ∉ N at han
  intro v hv
  by_cases hvn : v ∈ N
  · exact mem_sup_left ⟨hv,hvn⟩
  have hdiff : v*a⁻¹ ∈ N := by
    apply (N.subgroupOf V).mul_mem_iff_of_index_two hidx
      (a := (⟨v,hv⟩ : V)) (b := (⟨a,hAV ha⟩ : V)⁻¹) |>.mpr
    change v ∈ N ↔ a⁻¹ ∈ N
    simp only [inv_mem_iff,hvn,han]
  have hh : v*a⁻¹*a ∈ (V ⊓ N) ⊔ A :=
    mul_mem (mem_sup_left ⟨V.mul_mem hv (V.inv_mem (hAV ha)),hdiff⟩) (mem_sup_right ha)
  simpa only [inv_mul_cancel_right] using hh

private theorem opposite_line_stabilizer {F : Type*} [Group F]
    (Y K A T U : Subgroup F) (hi : K.relIndex Y = 4)
    (hKU : Y ⊓ K ≤ normalizer (U : Set F))
    (hYT : Y ≤ normalizer (T : Set F))
    (hAY : A ≤ Y) (hAP : A ≤ normalizer ((T ⊔ U : Subgroup F) : Set F))
    (hAn : ¬ A ≤ normalizer (U : Set F))
    (hYn : ¬ Y ≤ normalizer ((T ⊔ U : Subgroup F) : Set F)) :
    Y ⊓ normalizer (U : Set F) = Y ⊓ K ∧
      (normalizer (U : Set F)).relIndex Y = 4 := by
  let N := normalizer (U : Set F)
  have hle : Y ⊓ K ≤ Y ⊓ N := le_inf inf_le_left hKU
  have hd : N.relIndex Y ∣ 4 := by
    have hh := relIndex_dvd_of_le_left Y hle
    simpa only [inf_relIndex_left,hi] using hh
  have hnp : Y ⊓ N ≤ normalizer ((T ⊔ U : Subgroup F) : Set F) :=
    (le_inf (inf_le_left.trans hYT) inf_le_right).trans
      (normalizer_inf_normalizer_le_normalizer_sup T U)
  have hn1 : N.relIndex Y ≠ 1 := fun he => hAn (hAY.trans (relIndex_eq_one.mp he))
  have hn2 : N.relIndex Y ≠ 2 := by
    intro he
    exact hYn ((index_two_supplement A N Y hAY he hAn) ▸ sup_le hnp hAP)
  have hin : N.relIndex Y = 4 := by
    have hle := Nat.le_of_dvd (by decide : 0 < 4) hd
    have hn0 : N.relIndex Y ≠ 0 := by intro he; simp [he] at hd
    have hn3 : N.relIndex Y ≠ 3 := by intro he; norm_num [he] at hd
    omega
  refine ⟨le_antisymm ?_ hle,hin⟩
  have hm := relIndex_mul_relIndex (Y ⊓ K) (Y ⊓ N) Y hle inf_le_left
  rw [inf_relIndex_left,inf_relIndex_left,hi,hin] at hm
  exact relIndex_eq_one.mp (by omega : (Y ⊓ K).relIndex (Y ⊓ N) = 1)

universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "Rg" => edge L R
local notation "π" => CubicAction.projection h e hz hk

include h e hz hk in
/-- The full critical seed kernel at the common endpoint has exactly the
endpoint two-core as stabilizer inside an escaping radius actor. -/
theorem plane_radius_opposite_kernel_stabilizer
    {a b z : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) a z)
    (q : CriticalPath Rg (sourceGeometry h) b z)
    (hp : (Q Rg z).relIndex (Z Rg a) < 4)
    (hq : (Q Rg z).relIndex (Z Rg b) < 4)
    (Y : Subgroup (FreeAmalgam Rg)) (hYV : Y ≤ V Rg a)
    (hYG : Y ≤ stabilizer Rg z) (hAY : Z Rg a ≤ Y)
    (hi : (Q Rg z).relIndex Y = 4)
    (hAP : Z Rg a ≤ normalizer
      ((⁅Z Rg a,Z Rg z⁆ ⊔ ⁅Z Rg b,Z Rg z⁆ : Subgroup (FreeAmalgam Rg)) :
        Set (FreeAmalgam Rg)))
    (hcross : ⁅Z Rg a,⁅Z Rg b,Z Rg z⁆⁆ = ⁅Z Rg a,Z Rg z⁆)
    (hYn : ¬ Y ≤ normalizer
      ((⁅Z Rg a,Z Rg z⁆ ⊔ ⁅Z Rg b,Z Rg z⁆ : Subgroup (FreeAmalgam Rg)) :
        Set (FreeAmalgam Rg))) :
    Y ⊓ normalizer ((Z Rg z ⊓ Q Rg b : Subgroup (FreeAmalgam Rg)) :
      Set (FreeAmalgam Rg)) = Y ⊓ Q Rg z ∧
    Y ⊓ centralizer ((⁅Z Rg b,Z Rg z⁆ : Subgroup (FreeAmalgam Rg)) :
      Set (FreeAmalgam Rg)) = Y ⊓ Q Rg z ∧
    (normalizer ((Z Rg z ⊓ Q Rg b : Subgroup (FreeAmalgam Rg)) :
      Set (FreeAmalgam Rg))).relIndex Y = 4 ∧
    Y ⊓ stabilizer Rg b ≤ Q Rg z ∧ Y ⊓ Q Rg b ≤ Q Rg z ∧
    Y ≤ normalizer ((Z Rg z ⊓ Q Rg a : Subgroup (FreeAmalgam Rg)) :
      Set (FreeAmalgam Rg)) := by
  let T := ⁅Z Rg a,Z Rg z⁆
  let T' := ⁅Z Rg b,Z Rg z⁆
  have hcT : Nat.card T = 2 := small_critical_commutator_card h e hz hk p hp
  have hcT' : Nat.card T' = 2 := small_critical_commutator_card h e hz hk q hq
  have hAZ : Z Rg z ≤ stabilizer Rg a := critical_Z_le_stabilizer Rg (sourceGeometry h)
    a p.start_color (by rw [(sourceGeometry h).distance_constant _ p.start_color]; exact sourceDistance_pos h)
    p.critical
  have hTZ : T ≤ Z Rg a := le_normalizer_iff_commutator_le_left.mp
    (hAZ.trans (Z_normalized Rg a))
  have hT'Z : T' ≤ Z Rg z := le_normalizer_iff_commutator_le_right.mp
    ((Z_le_stabilizer_of_dist_le b _ q.critical.1.le).trans (Z_normalized Rg z))
  have hYa : Y ≤ Q Rg a := hYV.trans
    ((sourceGeometry h).V_le_Q (distance_gt_two h e hz hk) a p.start_color)
  have hYT : Y ≤ normalizer (T : Set (FreeAmalgam Rg)) :=
    ((hYa.trans (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q Rg a p.start_color)))).trans (centralizer_le hTZ)).trans
        (Subgroup.centralizer_le_normalizer _)
  have hKU : Y ⊓ Q Rg z ≤ normalizer (T' : Set (FreeAmalgam Rg)) :=
    ((inf_le_right.trans (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q Rg z p.end_color)))).trans (centralizer_le hT'Z)).trans
        (Subgroup.centralizer_le_normalizer _)
  have hAn : ¬ Z Rg a ≤ normalizer (T' : Set (FreeAmalgam Rg)) := by
    intro hh
    have he := commutator_eq_bot_iff_le_centralizer.mpr
      (hh.trans (normalizer_le_centralizer_of_card_two _ hcT'))
    change ⁅Z Rg a,⁅Z Rg b,Z Rg z⁆⁆ = ⊥ at he
    rw [hcross] at he
    change Nat.card (⁅Z Rg a,Z Rg z⁆ : Subgroup (FreeAmalgam Rg)) = 2 at hcT
    rw [he,card_bot] at hcT
    omega
  have hh := opposite_line_stabilizer Y (Q Rg z) (Z Rg a) T T' hi hKU hYT hAY hAP hAn hYn
  have hNC : normalizer (T' : Set (FreeAmalgam Rg)) =
      centralizer (T' : Set (FreeAmalgam Rg)) := le_antisymm
    (normalizer_le_centralizer_of_card_two _ hcT') (Subgroup.centralizer_le_normalizer _)
  have hC : Y ⊓ centralizer (T' : Set (FreeAmalgam Rg)) = Y ⊓ Q Rg z := by
    rw [←hNC]; exact hh.1
  have hrev := critical_reverse Rg (sourceGeometry h) (sourceEdgeCentralizer h e)
    b q.start_color (by rw [(sourceGeometry h).distance_constant _ q.start_color]; exact sourceDistance_pos h)
    z q.end_color q.critical
  let r : CriticalPath Rg (sourceGeometry h) z b := CriticalPath.ofPair q.end_color hrev
  have hrs : (Q Rg b).relIndex (Z Rg z) < 4 := by
    rw [(small_critical_indices h e hz hk q hq).2]; decide
  have he := small_critical_kernel_normalizer_eq_line_centralizer h e hz hk r hrs
  rw [commutator_comm (Z Rg z)] at he
  have hN : Y ⊓ normalizer ((Z Rg z ⊓ Q Rg b : Subgroup (FreeAmalgam Rg)) :
      Set (FreeAmalgam Rg)) = Y ⊓ Q Rg z := by
    calc
      _ = Y ⊓ (stabilizer Rg z ⊓ normalizer
          ((Z Rg z ⊓ Q Rg b : Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg))) :=
        by rw [←inf_assoc,inf_eq_left.mpr hYG]
      _ = Y ⊓ (stabilizer Rg z ⊓ centralizer (T' : Set (FreeAmalgam Rg))) := by rw [he]
      _ = Y ⊓ Q Rg z := by rw [←inf_assoc,inf_eq_left.mpr hYG,hC]
  have hb : Y ⊓ stabilizer Rg b ≤ Q Rg z := by
    intro x hx
    apply (show Y ⊓ Q Rg z ≤ Q Rg z from inf_le_right)
    rw [←hN]
    exact ⟨hx.1,inf_normalizer_le_normalizer_inf
      ⟨Z_normalized Rg z (hYG hx.1),Q_normalized Rg b hx.2⟩⟩
  refine ⟨hN,hC,?_,hb,(inf_le_inf_left Y (show Q Rg b ≤ stabilizer Rg b from fun _ hx => hx.1)).trans hb,
    (le_inf (hYG.trans (Z_normalized Rg z)) (hYa.trans (Q Rg a).le_normalizer)).trans
      inf_normalizer_le_normalizer_inf⟩
  rw [←inf_relIndex_left Y,hN,inf_relIndex_left,hi]

include h e hz hk in
/-- Both original radius kernels have index four on the full critical
kernel belonging to the same opposite-edge-displaced path. Their intersections
with the opposite starting stabilizer lie in the common endpoint two-core. -/
theorem plane_small_four_opposite_kernel_stabilizers
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
            ∀ i, i = 2 ∨ i = 3 →
              let Y := V Rg a ⊓ Q Rg (p.walk.getVert i)
              let b := act Rg g⁻¹ a
              Y ⊓ normalizer ((Z Rg z ⊓ Q Rg b : Subgroup (FreeAmalgam Rg)) :
                Set (FreeAmalgam Rg)) = Y ⊓ Q Rg z ∧
              Y ⊓ centralizer ((⁅Z Rg b,Z Rg z⁆ : Subgroup (FreeAmalgam Rg)) :
                Set (FreeAmalgam Rg)) = Y ⊓ Q Rg z ∧
              (normalizer ((Z Rg z ⊓ Q Rg b : Subgroup (FreeAmalgam Rg)) :
                Set (FreeAmalgam Rg))).relIndex Y = 4 ∧
              Y ⊓ stabilizer Rg b ≤ Q Rg z ∧ Y ⊓ Q Rg b ≤ Q Rg z ∧
              Y ≤ normalizer ((Z Rg z ⊓ Q Rg a : Subgroup (FreeAmalgam Rg)) :
                Set (FreeAmalgam Rg)) := by
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
  obtain ⟨hcross,_,_,_,_,hN,_,_,_,_,hYN⟩ :=
    plane_transferred_critical_plane h e hz hk u hR p (hsmall _ _ p) Y inf_le_left hYt hAY
      hnot hzs g hg hescape hesc
  have hWN := fun hh => hYN (hYW.trans hh)
  refine ⟨a,z,p,s,hzs,hgen,g,hg,hfix,q,hverts,hgeom,?_⟩
  intro i hi
  rcases hi with rfl | rfl
  · exact plane_radius_opposite_kernel_stabilizer h e hz hk p q (hsmall _ _ p)
      (hsmall _ _ q) Y inf_le_left hYG hAY hiY (le_sup_left.trans hN) hcross hYN
  · exact plane_radius_opposite_kernel_stabilizer h e hz hk p q (hsmall _ _ p)
      (hsmall _ _ q) W inf_le_left hWG (hAY.trans hYW) hiW (le_sup_left.trans hN) hcross hWN

omit hk in
include h e hz in
/-- Whole-core application retaining the literal opposite seed kernel,
both radius kernels, the cubic projection kernel and both full covers. -/
theorem coreExhaustion_or_cubic_opposite_kernel_stabilizers :
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
                    ∀ i, i = 2 ∨ i = 3 →
                      let Y := V Rg a ⊓ Q Rg (p.walk.getVert i)
                      let b := act Rg g⁻¹ a
                      Y ⊓ normalizer ((Z Rg z ⊓ Q Rg b : Subgroup (FreeAmalgam Rg)) :
                        Set (FreeAmalgam Rg)) = Y ⊓ Q Rg z ∧
                      Y ⊓ centralizer ((⁅Z Rg b,Z Rg z⁆ : Subgroup (FreeAmalgam Rg)) :
                        Set (FreeAmalgam Rg)) = Y ⊓ Q Rg z ∧
                      (normalizer ((Z Rg z ⊓ Q Rg b : Subgroup (FreeAmalgam Rg)) :
                        Set (FreeAmalgam Rg))).relIndex Y = 4 ∧
                      Y ⊓ stabilizer Rg b ≤ Q Rg z ∧ Y ⊓ Q Rg b ≤ Q Rg z ∧
                      Y ≤ normalizer ((Z Rg z ⊓ Q Rg a : Subgroup (FreeAmalgam Rg)) :
                        Set (FreeAmalgam Rg)))) := by
  rcases coreExhaustion_or_cubic_plane_paths h e hz with
    hex | ⟨hk,hs,hb,hcovers,u,hborel | ⟨hplane,_⟩⟩
  · exact Or.inl hex
  · exact Or.inr ⟨hk,hs,hb,hcovers,u,Or.inl hborel⟩
  · exact Or.inr ⟨hk,hs,hb,hcovers,u,Or.inr ⟨hplane,
      fun hb4 hsmall => plane_small_four_opposite_kernel_stabilizers h e hz hk u hplane hb4 hsmall⟩⟩

omit hk in
include h e hz in
/-- Literal C.1.32 application. The index-four stabilizer comparison does
not yet provide the opposite bound needed for the terminal contradiction. -/
theorem rankTwo_or_cubic_opposite_kernel_stabilizers :
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
                    ∀ i, i = 2 ∨ i = 3 →
                      let Y := V Rg a ⊓ Q Rg (p.walk.getVert i)
                      let b := act Rg g⁻¹ a
                      Y ⊓ normalizer ((Z Rg z ⊓ Q Rg b : Subgroup (FreeAmalgam Rg)) :
                        Set (FreeAmalgam Rg)) = Y ⊓ Q Rg z ∧
                      Y ⊓ centralizer ((⁅Z Rg b,Z Rg z⁆ : Subgroup (FreeAmalgam Rg)) :
                        Set (FreeAmalgam Rg)) = Y ⊓ Q Rg z ∧
                      (normalizer ((Z Rg z ⊓ Q Rg b : Subgroup (FreeAmalgam Rg)) :
                        Set (FreeAmalgam Rg))).relIndex Y = 4 ∧
                      Y ⊓ stabilizer Rg b ≤ Q Rg z ∧ Y ⊓ Q Rg b ≤ Q Rg z ∧
                      Y ≤ normalizer ((Z Rg z ⊓ Q Rg a : Subgroup (FreeAmalgam Rg)) :
                        Set (FreeAmalgam Rg)))) :=
  (coreExhaustion_or_cubic_opposite_kernel_stabilizers h e hz).imp
    (rankTwo_of_exhaustion h e hz) id

end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
