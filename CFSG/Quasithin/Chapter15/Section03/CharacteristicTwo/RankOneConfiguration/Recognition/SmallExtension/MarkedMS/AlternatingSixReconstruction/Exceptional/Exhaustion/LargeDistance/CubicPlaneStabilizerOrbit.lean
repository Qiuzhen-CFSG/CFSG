module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneOppositeStabilizer


/-!
# Stabilizers and displacement of the genuine cubic critical plane

On the same displaced paths from a and b to z, put T = [Z_a,Z_z],
T' = [Z_b,Z_z] and P = T join T'. For each original radius kernel Y,
its stabilizer of P is exactly (Y intersect Q_z) join Z_a, of index two
in Y. Its commutator with P is exactly T. In contrast, the stabilizer
of the full opposite critical seed kernel Z_z intersect Q_b has index
four in Y. A conjugate of P under Y meets P in exactly T, and their
join has order eight inside the full endpoint seed.

The endpoint-core intersection fixes the entire endpoint seed and has
index four in Y. The starting seed has image of order two and preserves
P, whereas Y does not preserve P. Relative index multiplication therefore
identifies the unique possible intermediate stabilizer. Relative normal
generation computes its commutator. The order-four plane and its conjugate
contain the same order-two critical line; their distinctness gives the
exact intersection, and the normalized product formula gives order eight.

The selector and its whole-core and literal C.1.32 applications retain
the original opposite-edge element, every displaced path vertex, both
radius kernels, and both full moving covers of orders sixteen and
thirty-two. The cubic projection still has kernel E, with its nontrivial
odd quotient E/Q, and R remains the original proper odd-index radical.
The retained radius line is never identified with the genuine critical
line, and the order-eight subgroup is not identified with the full cover.

The two stabilizer indices concern different subgroups and give no
contradiction by themselves. The terminal full-kernel comparison in
MS93 (5.12), the remaining image/distance/Borel cases, both core
exhaustions and the unconditional reconstruction remain open.

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

private theorem index_four_intermediate {F : Type*} [Group F]
    (K A N Y : Subgroup F) (hKY : K ≤ Y) (hAY : A ≤ Y)
    (hKN : K ≤ N) (hAN : A ≤ N) (hNY : N ≤ Y)
    (hYn : ¬ Y ≤ N) (hNK : Y ≤ normalizer (K : Set F))
    (hKA : K.relIndex A = 2) (hKYidx : K.relIndex Y = 4) :
    N = K ⊔ A ∧ N.relIndex Y = 2 := by
  let _ : (K.subgroupOf Y).Normal := normal_subgroupOf_of_le_normalizer hNK
  have hS : K.relIndex (K ⊔ A) = 2 := by
    have hh := relIndex_sup_left (A.subgroupOf Y) (K.subgroupOf Y)
    rw [←subgroupOf_sup hKY hAY,relIndex_subgroupOf (sup_le hKY hAY),
      relIndex_subgroupOf hAY] at hh
    exact hh.trans hKA
  have hSN : K ⊔ A ≤ N := sup_le hKN hAN
  have hiS : (K ⊔ A).relIndex Y = 2 := by
    have hh := relIndex_mul_relIndex K (K ⊔ A) Y le_sup_left (sup_le hKY hAY)
    rw [hS,hKYidx] at hh
    omega
  have hm := relIndex_mul_relIndex (K ⊔ A) N Y hSN hNY
  rw [hiS] at hm
  have hn1 : N.relIndex Y ≠ 1 := fun hh => hYn (relIndex_eq_one.mp hh)
  have hn0 : N.relIndex Y ≠ 0 := by intro hh; rw [hh,mul_zero] at hm; omega
  have hn : N.relIndex Y = 2 := by
    have hd : N.relIndex Y ∣ 2 := ⟨(K ⊔ A).relIndex N,by rw [mul_comm]; exact hm.symm⟩
    have hh := Nat.le_of_dvd (by decide : 0<2) hd
    omega
  rw [hn] at hm
  exact ⟨le_antisymm (relIndex_eq_one.mp (by omega : (K ⊔ A).relIndex N = 1)) hSN,hn⟩

private theorem four_conjugate_intersection {F : Type*} [Group F]
    (P T : Subgroup F) (hP : Nat.card P = 4) (hT : Nat.card T = 2)
    (hTP : T ≤ P) (g : F) (hTg : T.map (MulAut.conj g).toMonoidHom = T)
    (hPg : P.map (MulAut.conj g).toMonoidHom ≠ P) :
    P ⊓ P.map (MulAut.conj g).toMonoidHom = T := by
  let P' := P.map (MulAut.conj g).toMonoidHom
  let I := P ⊓ P'
  let : Finite P := Nat.finite_of_card_ne_zero (by omega)
  let : Finite P' := Nat.finite_of_card_ne_zero (by
    change Nat.card (P.map (MulAut.conj g).toMonoidHom) ≠ 0
    rw [card_map_of_injective (MulAut.conj g).injective,hP]; decide)
  let : Finite I := Finite.of_injective (inclusion (show I ≤ P from inf_le_left))
    (inclusion_injective _)
  have hTI : T ≤ I := le_inf hTP (by rw [←hTg]; exact map_mono hTP)
  have hle := card_le_of_le (show I ≤ P from inf_le_left)
  have hlo := card_le_of_le hTI
  have hdiv : Nat.card I ∣ 4 := hP ▸ card_dvd_of_le (show I ≤ P from inf_le_left)
  have hne : Nat.card I ≠ 4 := by
    intro hh
    have he : I = P := eq_of_le_of_card_ge inf_le_left (by omega)
    have hp : P ≤ P' := he ▸ inf_le_right
    apply hPg
    exact (eq_of_le_of_card_ge hp (by
      change Nat.card (P.map (MulAut.conj g).toMonoidHom) ≤ Nat.card P
      rw [card_map_of_injective (MulAut.conj g).injective])).symm
  have hc : Nat.card I = 2 := by
    rw [hP] at hle
    rw [hT] at hlo
    have hn3 : Nat.card I ≠ 3 := by intro hh; norm_num [hh] at hdiv
    omega
  exact (eq_of_le_of_card_ge hTI (by omega)).symm

private theorem two_planes_card {F : Type*} [Group F]
    (P P' T : Subgroup F) (hP : Nat.card P = 4) (hP' : Nat.card P' = 4)
    (hT : Nat.card T = 2) (hI : P ⊓ P' = T)
    (hn : P' ≤ normalizer (P : Set F)) : Nat.card (P ⊔ P' : Subgroup F) = 8 := by
  have hindex := relIndex_mul_relIndex (⊥ : Subgroup F) (P ⊓ P') P' bot_le inf_le_right
  rw [relIndex_bot_left,relIndex_bot_left,hI,hT,hP'] at hindex
  have hi : P.relIndex P' = 2 := by
    have he := inf_relIndex_right P P'
    rw [hI] at he
    rw [←he]
    omega
  let W := P ⊔ P'
  let _ : (P.subgroupOf W).Normal :=
    normal_subgroupOf_of_le_normalizer (sup_le P.le_normalizer hn)
  have hs := relIndex_sup_left (P'.subgroupOf W) (P.subgroupOf W)
  rw [←subgroupOf_sup le_sup_left le_sup_right,relIndex_subgroupOf le_rfl,
    relIndex_subgroupOf le_sup_right,hi] at hs
  have hc := relIndex_mul_relIndex (⊥ : Subgroup F) P W bot_le le_sup_left
  rw [relIndex_bot_left,relIndex_bot_left,hP,hs] at hc
  exact hc.symm

universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "Rg" => edge L R
local notation "π" => CubicAction.projection h e hz hk

include h e hz hk in
/-- The critical plane has the exact index-two stabilizer supplied by the
starting seed and endpoint two-core. Its full opposite seed-kernel stabilizer
has index four; displacing the plane produces a literal order-eight join. -/
theorem plane_radius_critical_plane_stabilizer
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
    (hcard : Nat.card (⁅Z Rg a,Z Rg z⁆ ⊔ ⁅Z Rg b,Z Rg z⁆ :
      Subgroup (FreeAmalgam Rg)) = 4)
    (hYn : ¬ Y ≤ normalizer
      ((⁅Z Rg a,Z Rg z⁆ ⊔ ⁅Z Rg b,Z Rg z⁆ : Subgroup (FreeAmalgam Rg)) :
        Set (FreeAmalgam Rg))) :
    let T := ⁅Z Rg a,Z Rg z⁆
    let P := T ⊔ ⁅Z Rg b,Z Rg z⁆
    Y ⊓ normalizer (P : Set (FreeAmalgam Rg)) = (Y ⊓ Q Rg z) ⊔ Z Rg a ∧
      (normalizer (P : Set (FreeAmalgam Rg))).relIndex Y = 2 ∧
      (normalizer ((Z Rg z ⊓ Q Rg b : Subgroup (FreeAmalgam Rg)) :
        Set (FreeAmalgam Rg))).relIndex Y = 4 ∧
      ⁅Y ⊓ normalizer (P : Set (FreeAmalgam Rg)),P⁆ = T ∧
      ∃ y ∈ Y, P.map (MulAut.conj y).toMonoidHom ≠ P ∧
        P ⊓ P.map (MulAut.conj y).toMonoidHom = T ∧
        Nat.card (P ⊔ P.map (MulAut.conj y).toMonoidHom :
          Subgroup (FreeAmalgam Rg)) = 8 := by
  let T := ⁅Z Rg a,Z Rg z⁆
  let T' := ⁅Z Rg b,Z Rg z⁆
  let P := T ⊔ T'
  let := (sourceGeometry h).Z_elementary (sourceDistance_pos h) z p.end_color
  have hZaG := critical_Z_le_stabilizer Rg (sourceGeometry h) a p.start_color
    (by rw [(sourceGeometry h).distance_constant _ p.start_color]; exact sourceDistance_pos h)
    p.critical
  have hTZa : T ≤ Z Rg a := le_normalizer_iff_commutator_le_left.mp
    (hZaG.trans (Z_normalized Rg a))
  have hTZ : T ≤ Z Rg z := le_normalizer_iff_commutator_le_right.mp
    ((Z_le_stabilizer_of_dist_le a _ p.critical.1.le).trans (Z_normalized Rg z))
  have hT'Z : T' ≤ Z Rg z := le_normalizer_iff_commutator_le_right.mp
    ((Z_le_stabilizer_of_dist_le b _ q.critical.1.le).trans (Z_normalized Rg z))
  have hPZ : P ≤ Z Rg z := sup_le hTZ hT'Z
  have hK : Y ⊓ Q Rg z ≤ centralizer (Z Rg z : Set (FreeAmalgam Rg)) :=
    inf_le_right.trans (le_centralizer_iff.mp
      (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q Rg z p.end_color)))
  have hKN : Y ⊓ Q Rg z ≤ normalizer (P : Set (FreeAmalgam Rg)) :=
    ((hK.trans (centralizer_le hPZ))).trans (Subgroup.centralizer_le_normalizer _)
  have hNK : Y ≤ normalizer ((Y ⊓ Q Rg z : Subgroup (FreeAmalgam Rg)) :
      Set (FreeAmalgam Rg)) :=
    (le_inf Y.le_normalizer (hYG.trans (Q_normalized Rg z))).trans
      inf_normalizer_le_normalizer_inf
  have hKA : (Y ⊓ Q Rg z).relIndex (Z Rg a) = 2 := by
    rw [inf_comm,←relIndex_inf_mul_relIndex,inf_eq_right.mpr hAY,
      relIndex_eq_one.mpr hAY,mul_one]
    exact (small_critical_indices h e hz hk p hp).1
  have hh := index_four_intermediate (Y ⊓ Q Rg z) (Z Rg a)
    (Y ⊓ normalizer (P : Set (FreeAmalgam Rg))) Y inf_le_left hAY
    (le_inf inf_le_left hKN) (le_inf hAY hAP) inf_le_left
    (fun hn => hYn (hn.trans inf_le_right)) hNK hKA (by rwa [inf_relIndex_left])
  have hop := plane_radius_opposite_kernel_stabilizer h e hz hk p q hp hq Y hYV
    hYG hAY hi hAP hcross hYn

  have hYa : Y ≤ Q Rg a := hYV.trans
    ((sourceGeometry h).V_le_Q (distance_gt_two h e hz hk) a p.start_color)
  have hYT : Y ≤ normalizer (T : Set (FreeAmalgam Rg)) :=
    (((hYa.trans (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q Rg a p.start_color)))).trans (centralizer_le hTZa))).trans
        (Subgroup.centralizer_le_normalizer _)
  have hAc : ⁅Z Rg a,P⁆ ≤ T := by
    rw [commutator_comm]
    apply commutator_sup_le_of_relative_normal (Z Rg z) T T' (Z Rg a) T
      (((le_centralizer (H := Z Rg z)).trans (centralizer_le hTZ)).trans
        (Subgroup.centralizer_le_normalizer _)) hTZ hT'Z
    · exact (commutator_eq_bot_iff_le_centralizer.mpr
        ((hTZa.trans (commutator_eq_bot_iff_le_centralizer.mp
          (Z_centralizes_Q Rg a p.start_color))).trans
            (centralizer_le (hAY.trans hYa)))).le.trans bot_le
    · rw [commutator_comm]
      exact hcross.le
  have hcomm : ⁅Y ⊓ normalizer (P : Set (FreeAmalgam Rg)),P⁆ = T := by
    apply le_antisymm
    · rw [hh.1]
      apply commutator_sup_le_of_relative_normal Y (Y ⊓ Q Rg z) (Z Rg a) P T
        hYT inf_le_left hAY
      · exact (commutator_eq_bot_iff_le_centralizer.mpr
          (hK.trans (centralizer_le hPZ))).le.trans bot_le
      · exact hAc
    · exact hcross.symm.le.trans (commutator_mono (le_inf hAY hAP) le_sup_right)
  refine ⟨hh.1,by simpa only [inf_relIndex_left] using hh.2,hop.2.2.1,hcomm,?_⟩
  obtain ⟨y,hy,hyn⟩ := Set.not_subset.mp hYn
  have hne : P.map (MulAut.conj y).toMonoidHom ≠ P :=
    fun he => hyn (mem_normalizer_iff_map_conj_eq.mpr he)
  have hI := four_conjugate_intersection P T hcard
    (small_critical_commutator_card h e hz hk p hp) le_sup_left
      y (mem_normalizer_iff_map_conj_eq.mp (hYT hy)) hne
  have hP'Z : P.map (MulAut.conj y).toMonoidHom ≤ Z Rg z :=
    (map_mono hPZ).trans_eq (mem_normalizer_iff_map_conj_eq.mp
      (Z_normalized Rg z (hYG hy)))
  exact ⟨y,hy,hne,hI,two_planes_card P (P.map (MulAut.conj y).toMonoidHom) T
    hcard (by rwa [card_map_of_injective (MulAut.conj y).injective])
    (small_critical_commutator_card h e hz hk p hp) hI
    (((hP'Z.trans (le_centralizer (H := Z Rg z))).trans (centralizer_le hPZ)).trans
      (Subgroup.centralizer_le_normalizer _))⟩

include h e hz hk in
/-- On the same displaced paths, both original radius kernels have an
index-two stabilizer of the critical four-group, with an explicit supplement
and critical commutator. A conjugate four-group intersects it in the starting
critical line and their join has order eight. The opposite full seed-kernel
stabilizer retains index four. -/
theorem plane_small_four_critical_plane_stabilizers
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
              let T := ⁅Z Rg a,Z Rg z⁆
              let P := T ⊔ ⁅Z Rg b,Z Rg z⁆
              Y ⊓ normalizer (P : Set (FreeAmalgam Rg)) = (Y ⊓ Q Rg z) ⊔ Z Rg a ∧
                (normalizer (P : Set (FreeAmalgam Rg))).relIndex Y = 2 ∧
                (normalizer ((Z Rg z ⊓ Q Rg b : Subgroup (FreeAmalgam Rg)) :
                  Set (FreeAmalgam Rg))).relIndex Y = 4 ∧
                ⁅Y ⊓ normalizer (P : Set (FreeAmalgam Rg)),P⁆ = T ∧
                ∃ y ∈ Y, P.map (MulAut.conj y).toMonoidHom ≠ P ∧
                  P ⊓ P.map (MulAut.conj y).toMonoidHom = T ∧
                  Nat.card (P ⊔ P.map (MulAut.conj y).toMonoidHom :
                    Subgroup (FreeAmalgam Rg)) = 8 := by
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
  obtain ⟨hcross,_,_,hcard,_,hN,_,_,_,_,hYN⟩ :=
    plane_transferred_critical_plane h e hz hk u hR p (hsmall _ _ p) Y inf_le_left hYt hAY
      hnot hzs g hg hescape hesc
  have hWN := fun hh => hYN (hYW.trans hh)
  refine ⟨a,z,p,s,hzs,hgen,g,hg,hfix,q,hverts,hgeom,?_⟩
  intro i hi
  rcases hi with rfl | rfl
  · exact plane_radius_critical_plane_stabilizer h e hz hk p q (hsmall _ _ p)
      (hsmall _ _ q) Y inf_le_left hYG hAY hiY (le_sup_left.trans hN) hcross hcard hYN
  · exact plane_radius_critical_plane_stabilizer h e hz hk p q (hsmall _ _ p)
      (hsmall _ _ q) W inf_le_left hWG (hAY.trans hYW) hiW (le_sup_left.trans hN) hcross hcard hWN

omit hk in
include h e hz in
/-- Whole-core application of the two distinct stabilizer indices and
the same critical plane orbit, retaining the actual cubic kernel and both covers. -/
theorem coreExhaustion_or_cubic_critical_plane_stabilizers :
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
                      let T := ⁅Z Rg a,Z Rg z⁆
                      let P := T ⊔ ⁅Z Rg b,Z Rg z⁆
                      Y ⊓ normalizer (P : Set (FreeAmalgam Rg)) = (Y ⊓ Q Rg z) ⊔ Z Rg a ∧
                        (normalizer (P : Set (FreeAmalgam Rg))).relIndex Y = 2 ∧
                        (normalizer ((Z Rg z ⊓ Q Rg b : Subgroup (FreeAmalgam Rg)) :
                          Set (FreeAmalgam Rg))).relIndex Y = 4 ∧
                        ⁅Y ⊓ normalizer (P : Set (FreeAmalgam Rg)),P⁆ = T ∧
                        ∃ y ∈ Y, P.map (MulAut.conj y).toMonoidHom ≠ P ∧
                          P ⊓ P.map (MulAut.conj y).toMonoidHom = T ∧
                          Nat.card (P ⊔ P.map (MulAut.conj y).toMonoidHom :
                            Subgroup (FreeAmalgam Rg)) = 8)) := by
  rcases coreExhaustion_or_cubic_plane_paths h e hz with
    hex | ⟨hk,hs,hb,hcovers,u,hborel | ⟨hplane,_⟩⟩
  · exact Or.inl hex
  · exact Or.inr ⟨hk,hs,hb,hcovers,u,Or.inl hborel⟩
  · exact Or.inr ⟨hk,hs,hb,hcovers,u,Or.inr ⟨hplane,
      fun hb4 hsmall => plane_small_four_critical_plane_stabilizers h e hz hk u hplane hb4 hsmall⟩⟩

omit hk in
include h e hz in
/-- Literal C.1.32 application of the critical-plane stabilizer and orbit
comparison. The full opposite seed kernel remains a distinct subgroup. -/
theorem rankTwo_or_cubic_critical_plane_stabilizers :
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
                      let T := ⁅Z Rg a,Z Rg z⁆
                      let P := T ⊔ ⁅Z Rg b,Z Rg z⁆
                      Y ⊓ normalizer (P : Set (FreeAmalgam Rg)) = (Y ⊓ Q Rg z) ⊔ Z Rg a ∧
                        (normalizer (P : Set (FreeAmalgam Rg))).relIndex Y = 2 ∧
                        (normalizer ((Z Rg z ⊓ Q Rg b : Subgroup (FreeAmalgam Rg)) :
                          Set (FreeAmalgam Rg))).relIndex Y = 4 ∧
                        ⁅Y ⊓ normalizer (P : Set (FreeAmalgam Rg)),P⁆ = T ∧
                        ∃ y ∈ Y, P.map (MulAut.conj y).toMonoidHom ≠ P ∧
                          P ⊓ P.map (MulAut.conj y).toMonoidHom = T ∧
                          Nat.card (P ⊔ P.map (MulAut.conj y).toMonoidHom :
                            Subgroup (FreeAmalgam Rg)) = 8)) :=
  (coreExhaustion_or_cubic_critical_plane_stabilizers h e hz).imp
    (rankTwo_of_exhaustion h e hz) id

end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
