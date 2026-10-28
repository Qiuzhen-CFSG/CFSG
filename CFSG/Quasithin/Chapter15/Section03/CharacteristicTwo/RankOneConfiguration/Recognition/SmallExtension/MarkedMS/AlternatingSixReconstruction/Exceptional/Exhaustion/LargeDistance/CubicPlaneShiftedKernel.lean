module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneOppositeKernel
public import Theory.GroupTheory.Commutator.SplitPair
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneOppositeKernel
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneRadiusImage
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneBackward

/-!
# Shifted kernels recover the retained cubic radius line

Keep the escaping radius Y = V_a intersect Q_c on the selected critical
path a--z, and its full reverse-kernel line H = [Y,Z_z intersect Q_a].
For an overlapping critical path d--c through a, consider either the full
kernel Z_d intersect Q_c or the moving kernel U_d intersect Q_c.

If the shifted comparison [K,Z_z] <= [K,Z_z intersect Q_a] join [Z_a,Z_z]
fails, the shifted reverse-kernel commutator is nonzero. It lies in the
already retained order-two H, so it equals H. The actual edge-cover
calculation gives K join Z_a endpoint image of order four. Relative index
multiplication then gives Y = (K join Z_a)(Y intersect Q_z), and the second
factor fixes Z_z. Consequently [K,Z_z] join [Z_a,Z_z] is the entire
original endpoint commutator, also carried by the opposite full kernel.

The shifted kernel lies in Z_d, and Q_a stabilizes d. Thus its commutator
with Z_z intersect Q_a lies in Z_d. The same H already lies in Z_a, Z_c,
and Z_z, so it centralizes all four corresponding two-cores. This is
opposite-core control of the retained line, without replacing the larger
full endpoint commutator by that line.

The selector retains the original opposite-edge conjugator and displaced
paths. Its whole-core and literal C.1.32 applications specialize to both
actual shifted kernels, keeping both moving covers, all central attachments,
the original nonsylow radical, and the projection with kernel E and
nontrivial odd E/Q. The failure alternative still requires elimination.
This does not prove (5.12)(1), the terminal contradiction, the other image
and distance branches, either core exhaustion, or final reconstruction.

Internal imports reuse the already checked edge-cover and equal-image
calculations without widening their public boundaries.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), the shifted comparison and its failure branch in (5.12)(1),
printed pp.924--925; Aschbacher--Smith C.1.31--32, printed pp.135--136.
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
private theorem plane_radius_subactor_failure_saturates
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    (hb4 : sourceDistance h = 4)
    {a z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (hp : (Q Rg z).relIndex (Z Rg a) < 4)
    (hescape : ¬ ⁅V Rg a ⊓ Q Rg (p.walk.getVert 2),Z Rg z⁆ ≤ Z Rg a)
    (K : Subgroup (FreeAmalgam Rg))
    (hK : K ≤ V Rg a ⊓ Q Rg (p.walk.getVert 2))
    (hfail : ¬ ⁅K,Z Rg z⁆ ≤ ⁅K,Z Rg z ⊓ Q Rg a⁆ ⊔ ⁅Z Rg a,Z Rg z⁆) :
    let Y := V Rg a ⊓ Q Rg (p.walk.getVert 2)
    let H := ⁅Y,Z Rg z ⊓ Q Rg a⁆
    ⁅K,Z Rg z ⊓ Q Rg a⁆ = H ∧
      (Q Rg z).relIndex (K ⊔ Z Rg a) = 4 ∧
      (K ⊔ Z Rg a) ⊔ (Y ⊓ Q Rg z) = Y ∧
      ⁅K,Z Rg z⁆ ⊔ ⁅Z Rg a,Z Rg z⁆ = ⁅Y,Z Rg z⁆ := by
  let Y := V Rg a ⊓ Q Rg (p.walk.getVert 2)
  let F := Z Rg z ⊓ Q Rg a
  let A := Z Rg a
  let J := K ⊔ A
  have hb := distance_gt_two h e hz hk
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb4
  have hc : color Rg (p.walk.getVert 2) = false :=
    (p.vertex_color (by omega)).mpr (by decide)
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
  have hYG : Y ≤ stabilizer Rg z := by
    have hh := hYt
    simp only [hl,Nat.reduceSub] at hh
    exact hh.trans (fun _ hx => hx.2 _ (adjacent_symm Rg hzt))
  have hAY : A ≤ Y := by
    refine le_inf (Z_le_VBall Rg _ 2) ?_
    apply Z_le_Q_of_dist_lt Rg _ ((sourceGeometry h).exists_critical _ p.start_color)
    rw [(sourceGeometry h).distance_constant _ p.start_color,p.dist_start (by omega)]
    exact hb
  have hJY : J ≤ Y := sup_le hK hAY
  have hKC : K ≤ centralizer (A : Set (FreeAmalgam Rg)) :=
    ((hK.trans inf_le_left).trans ((sourceGeometry h).V_le_Q hb a p.start_color)).trans
      (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
        (Z_centralizes_Q Rg a p.start_color)))
  have hACF : A ≤ centralizer (F : Set (FreeAmalgam Rg)) :=
    (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q Rg a p.start_color)).trans
      (centralizer_le inf_le_right)
  have hJF : ⁅J,F⁆ = ⁅K,F⁆ :=
    commutator_sup_of_central_attachment K A F
      ((le_centralizer_iff.mp hKC).trans (Subgroup.centralizer_le_normalizer _)) hACF
  have hfixed : F = Z Rg z ⊓ centralizer (A : Set (FreeAmalgam Rg)) :=
    (critical_seed_centralizer_intersection h e
      (CriticalPath.ofPair p.end_color (critical_reverse Rg (sourceGeometry h)
        (sourceEdgeCentralizer h e) a p.start_color
        (by rw [(sourceGeometry h).distance_constant _ p.start_color]; exact sourceDistance_pos h)
        z p.end_color p.critical))).symm
  have hne : ⁅K,F⁆ ≠ ⊥ := by
    intro he
    apply hfail
    have hh := small_critical_kernel_commutator h e hz hk p hp K (hK.trans hYG)
      (commutator_eq_bot_iff_le_centralizer.mp he)
    exact hh.trans le_sup_right
  have hline := plane_radius_subactor_kernel_line h e hz hk u hR p hp Y
    inf_le_left hYt hescape
  have hle : ⁅K,F⁆ ≤ ⁅Y,F⁆ := commutator_mono hK le_rfl
  have hHZ : ⁅Y,F⁆ ≤ Z Rg a := hline.2.2.1
  let := finite_Z Rg a
  let : Finite (⁅Y,F⁆ : Subgroup (FreeAmalgam Rg)) :=
    Finite.of_injective (inclusion hHZ) (inclusion_injective _)
  let : Finite (⁅K,F⁆ : Subgroup (FreeAmalgam Rg)) :=
    Finite.of_injective (inclusion hle) (inclusion_injective _)
  have hequal : ⁅K,F⁆ = ⁅Y,F⁆ := eq_of_le_of_card_ge hle (by
    have hh := (one_lt_card_iff_ne_bot _).mpr hne
    have hcard : Nat.card (⁅Y,F⁆ : Subgroup (FreeAmalgam Rg)) = 2 := hline.1
    omega)
  have hidx : (Q Rg z).relIndex J = 4 := by
    let := finite_Z Rg z
    let : Finite (U Rg z) := Finite.of_injective
      (inclusion (DistanceEight.U_le_Z Rg z)) (inclusion_injective _)
    have hi : (centralizer (A : Set (FreeAmalgam Rg))).relIndex (U Rg z) ≤ 2 :=
      ((relIndex_le_of_le_left
        (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
          (Z_centralizes_Q Rg a p.start_color))) index_ne_zero_of_finite).trans
        (relIndex_le_of_le_right (DistanceEight.U_le_Z Rg z) index_ne_zero_of_finite)).trans_eq
          (small_critical_indices h e hz hk p hp).2
    apply plane_edge_kernel_image h e hz hk u hR.le p.end_color hzt A J
      (by simpa only [hl,Nat.reduceSub] using hAY.trans hYt)
      (by simpa only [hl,Nat.reduceSub] using hJY.trans hYt)
      p.critical.2 hi le_sup_right
    · rw [←hfixed,commutator_comm,hJF]
      exact hne
    · intro hh
      rw [←hfixed,commutator_comm (Z Rg z) J,commutator_comm F J,hJF,
        commutator_comm (Z Rg z) A] at hh
      exact hfail ((commutator_mono le_sup_left le_rfl).trans hh)
  have hYidx := plane_radius_subactor_index_four h e hz hk u hR p hp Y
    inf_le_left hYt hAY hescape
  have hfull := plane_radius_equal_endpoint_commutators h p J Y hJY hYG hidx hYidx
  have hAZ : Z Rg z ≤ normalizer (A : Set (FreeAmalgam Rg)) :=
    (critical_Z_le_stabilizer Rg (sourceGeometry h) a p.start_color
      (by rw [(sourceGeometry h).distance_constant _ p.start_color]; exact sourceDistance_pos h)
      p.critical).trans (Z_normalized Rg a)
  have hsplit : ⁅J,Z Rg z⁆ = ⁅K,Z Rg z⁆ ⊔ ⁅A,Z Rg z⁆ :=
    commutator_sup_of_commuting_factors K A (Z Rg z) hKC hAZ
  exact ⟨hequal,hidx,hfull.1,hsplit.symm.trans hfull.2⟩

include h e hz hk in
/-- Failure of the source shifted comparison recovers the same original
radius line and the same full endpoint commutator. The line then lies in
the shifted starting seed and centralizes all four component two-cores. -/
theorem plane_shifted_kernel_failure_transfer
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    (hb4 : sourceDistance h = 4)
    (hsmall : ∀ a z (_p : CriticalPath Rg (sourceGeometry h) a z),
      (Q Rg z).relIndex (Z Rg a) < 4)
    {a z d : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (q : CriticalPath Rg (sourceGeometry h) d (p.walk.getVert 2))
    (hqa : q.walk.getVert 2 = a)
    (hescape : ¬ ⁅V Rg a ⊓ Q Rg (p.walk.getVert 2),Z Rg z⁆ ≤ Z Rg a)
    (K : Subgroup (FreeAmalgam Rg)) (hK : K ≤ Z Rg d ⊓ Q Rg (p.walk.getVert 2))
    (hfail : ¬ ⁅K,Z Rg z⁆ ≤ ⁅K,Z Rg z ⊓ Q Rg a⁆ ⊔ ⁅Z Rg a,Z Rg z⁆) :
    let Y := V Rg a ⊓ Q Rg (p.walk.getVert 2)
    let H := ⁅Y,Z Rg z ⊓ Q Rg a⁆
    ⁅K,Z Rg z ⊓ Q Rg a⁆ = H ∧ H ≤ Z Rg d ∧
      ⁅H,(Q Rg d ⊔ Q Rg a) ⊔ (Q Rg (p.walk.getVert 2) ⊔ Q Rg z)⁆ = ⊥ ∧
      (Q Rg z).relIndex (K ⊔ Z Rg a) = 4 ∧
      (K ⊔ Z Rg a) ⊔ (Y ⊓ Q Rg z) = Y ∧
      ⁅K,Z Rg z⁆ ⊔ ⁅Z Rg a,Z Rg z⁆ = ⁅Y,Z Rg z⁆ := by
  let Y := V Rg a ⊓ Q Rg (p.walk.getVert 2)
  let F := Z Rg z ⊓ Q Rg a
  let H := ⁅Y,F⁆
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb4
  have hql : q.walk.length = 4 := q.length_eq_b.trans hb4
  have hda : (cosetGraph Rg).dist d a = 2 := by
    rw [←hqa,q.dist_start (by omega)]
  have hdV : Z Rg d ≤ V Rg a :=
    le_iSup_of_le d (le_iSup_of_le (by omega : (cosetGraph Rg).dist d a ≤ 2) le_rfl)
  have hKY : K ≤ Y := le_inf ((hK.trans inf_le_left).trans hdV) (hK.trans inf_le_right)
  obtain ⟨hline,hi,hs,hfull⟩ := plane_radius_subactor_failure_saturates h e hz hk u hR
    hb4 p (hsmall _ _ p) hescape K hKY hfail
  have hFNd : F ≤ normalizer (Z Rg d : Set (FreeAmalgam Rg)) :=
    (inf_le_right.trans (Q_le_stabilizer_of_dist_le_two a d p.start_color q.start_color
      (by rw [SimpleGraph.dist_comm,hda]))).trans (Z_normalized Rg d)
  have hHd : H ≤ Z Rg d := by
    change ⁅K,F⁆ = H at hline
    rw [←hline]
    exact (commutator_mono (hK.trans inf_le_left) le_rfl).trans
      (le_normalizer_iff_commutator_le_left.mp hFNd)
  have hXZ := (plane_small_four_omega_generated h e hz hk u hR hb4 hsmall z p.end_color).2
  have hlineData := plane_four_full_kernel_line h e hz hk u hR hb4 hsmall p Y
    inf_le_left inf_le_right (by rwa [hXZ])
  rw [hXZ] at hlineData
  have hc : color Rg (p.walk.getVert 2) = false :=
    (p.vertex_color (by omega)).mpr (by decide)
  have hzt : Adjacent Rg z (p.walk.getVert 3) := by
    have hh := p.walk.adj_getVert_succ (i := 3) (by omega)
    rw [show 3+1=p.walk.length by omega,p.walk.getVert_length] at hh
    exact adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp hh)
  have hHZ : H ≤ Z Rg z :=
    hlineData.2.2.2.2.1.le.trans (hlineData.2.2.2.2.2.1.trans
      (inf_le_left.trans (adjacent_Z_le Rg p.end_color hzt)))
  have hfix {v : Vertex Rg} (hv : color Rg v = false) (hHv : H ≤ Z Rg v) :
      Q Rg v ≤ centralizer (H : Set (FreeAmalgam Rg)) :=
    le_centralizer_iff.mp (hHv.trans (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q Rg v hv)))
  have hcores : ⁅H,(Q Rg d ⊔ Q Rg a) ⊔
      (Q Rg (p.walk.getVert 2) ⊔ Q Rg z)⁆ = ⊥ := by
    apply commutator_eq_bot_iff_le_centralizer.mpr
    apply le_centralizer_iff.mpr
    exact sup_le (sup_le (hfix q.start_color hHd)
      (hfix p.start_color (hlineData.2.2.1.trans inf_le_left)))
      (sup_le (hfix hc (hlineData.2.2.1.trans inf_le_right)) (hfix p.end_color hHZ))
  exact ⟨hline,hHd,hcores,hi,hs,hfull⟩


include h e hz hk in
/-- Apply the overlapping-path comparison to the very same selected radius,
opposite kernel, and displaced paths. It applies in particular to both
the full shifted kernel and the moving shifted kernel. -/
theorem plane_small_four_shifted_kernel_comparison
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
              ∀ d (r : CriticalPath Rg (sourceGeometry h) d (p.walk.getVert 2)),
                r.walk.getVert 2 = a →
                ∀ K : Subgroup (FreeAmalgam Rg),
                  (K = Z Rg d ⊓ Q Rg (p.walk.getVert 2) ∨
                    K = U Rg d ⊓ Q Rg (p.walk.getVert 2)) →
                  ⁅K,Z Rg z⁆ ≤ ⁅K,F⁆ ⊔ T ∨
                  (⁅K,F⁆ = H ∧ H ≤ Z Rg d ∧
                    ⁅H,(Q Rg d ⊔ Q Rg a) ⊔ (Q Rg (p.walk.getVert 2) ⊔ Q Rg z)⁆ = ⊥ ∧
                    (Q Rg z).relIndex (K ⊔ Z Rg a) = 4 ∧
                    (K ⊔ Z Rg a) ⊔ (Y ⊓ Q Rg z) = Y ∧
                    ⁅K,Z Rg z⁆ ⊔ T = C) := by
  obtain ⟨a,z,p,s,hzs,hgen,g,hg,hfix,q,hverts,hgeom,
    _,_,_,hopp,_,_,_,hcard,hstrict,hbig,hescape,_,_⟩ :=
    plane_small_four_full_kernel_comparison h e hz hk u hR hb4 hsmall
  refine ⟨a,z,p,s,hzs,hgen,g,hg,hfix,q,hverts,hgeom,hcard,hstrict,hbig,hopp,?_⟩
  intro d r hra K hkernel
  have hK : K ≤ Z Rg d ⊓ Q Rg (p.walk.getVert 2) := by
    rcases hkernel with rfl | rfl
    · exact le_rfl
    · exact inf_le_inf_right _ (DistanceEight.U_le_Z Rg d)
  by_cases hc : ⁅K,Z Rg z⁆ ≤ ⁅K,Z Rg z ⊓ Q Rg a⁆ ⊔ ⁅Z Rg a,Z Rg z⁆
  · exact Or.inl hc
  · exact Or.inr (plane_shifted_kernel_failure_transfer h e hz hk u hR hb4 hsmall
      p r hra hescape K hK hc)

omit hk in
include h e hz in
/-- Whole-core application retaining the original cubic projection and both
full covers. The shifted comparison's failure is reduced on the same
selected paths; its elimination is still required. -/
theorem coreExhaustion_or_cubic_shifted_kernel_comparison :
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
            let F := Z Rg z ⊓ Q Rg a
            let T := ⁅Z Rg a,Z Rg z⁆
            let H := ⁅Y,F⁆
            let C := ⁅Y,Z Rg z⁆
            Nat.card H = 2 ∧ H < C ∧ 4 ≤ Nat.card C ∧
              ⁅Y,Z Rg z ⊓ Q Rg (act Rg g⁻¹ a)⁆ = C ∧
              ∀ d (r : CriticalPath Rg (sourceGeometry h) d (p.walk.getVert 2)),
                r.walk.getVert 2 = a →
                ∀ K : Subgroup (FreeAmalgam Rg),
                  (K = Z Rg d ⊓ Q Rg (p.walk.getVert 2) ∨
                    K = U Rg d ⊓ Q Rg (p.walk.getVert 2)) →
                  ⁅K,Z Rg z⁆ ≤ ⁅K,F⁆ ⊔ T ∨
                  (⁅K,F⁆ = H ∧ H ≤ Z Rg d ∧
                    ⁅H,(Q Rg d ⊔ Q Rg a) ⊔ (Q Rg (p.walk.getVert 2) ⊔ Q Rg z)⁆ = ⊥ ∧
                    (Q Rg z).relIndex (K ⊔ Z Rg a) = 4 ∧
                    (K ⊔ Z Rg a) ⊔ (Y ⊓ Q Rg z) = Y ∧
                    ⁅K,Z Rg z⁆ ⊔ T = C))) := by
  rcases coreExhaustion_or_cubic_plane_paths h e hz with
    hex | ⟨hk,hs,hb,hcovers,u,hborel | ⟨hplane,_⟩⟩
  · exact Or.inl hex
  · exact Or.inr ⟨hk,hs,hb,hcovers,u,Or.inl hborel⟩
  · exact Or.inr ⟨hk,hs,hb,hcovers,u,Or.inr ⟨hplane,
      fun hb4 hsmall => plane_small_four_shifted_kernel_comparison h e hz hk u hplane hb4 hsmall⟩⟩

omit hk in
include h e hz in
/-- Literal C.1.32 application of the shifted-kernel comparison on the
original cubic graph, including the full central attachments. -/
theorem rankTwo_or_cubic_shifted_kernel_comparison :
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
            let F := Z Rg z ⊓ Q Rg a
            let T := ⁅Z Rg a,Z Rg z⁆
            let H := ⁅Y,F⁆
            let C := ⁅Y,Z Rg z⁆
            Nat.card H = 2 ∧ H < C ∧ 4 ≤ Nat.card C ∧
              ⁅Y,Z Rg z ⊓ Q Rg (act Rg g⁻¹ a)⁆ = C ∧
              ∀ d (r : CriticalPath Rg (sourceGeometry h) d (p.walk.getVert 2)),
                r.walk.getVert 2 = a →
                ∀ K : Subgroup (FreeAmalgam Rg),
                  (K = Z Rg d ⊓ Q Rg (p.walk.getVert 2) ∨
                    K = U Rg d ⊓ Q Rg (p.walk.getVert 2)) →
                  ⁅K,Z Rg z⁆ ≤ ⁅K,F⁆ ⊔ T ∨
                  (⁅K,F⁆ = H ∧ H ≤ Z Rg d ∧
                    ⁅H,(Q Rg d ⊔ Q Rg a) ⊔ (Q Rg (p.walk.getVert 2) ⊔ Q Rg z)⁆ = ⊥ ∧
                    (Q Rg z).relIndex (K ⊔ Z Rg a) = 4 ∧
                    (K ⊔ Z Rg a) ⊔ (Y ⊓ Q Rg z) = Y ∧
                    ⁅K,Z Rg z⁆ ⊔ T = C))) :=
  (coreExhaustion_or_cubic_shifted_kernel_comparison h e hz).imp
    (rankTwo_of_exhaustion h e hz) id


end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
