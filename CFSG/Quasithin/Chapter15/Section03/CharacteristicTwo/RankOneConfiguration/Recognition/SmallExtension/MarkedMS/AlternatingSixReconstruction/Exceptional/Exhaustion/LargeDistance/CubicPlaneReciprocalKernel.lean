module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneShiftedKernel
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneRadiusAlignment
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicBackwardRigidity

/-!
# Reciprocal full and moving kernels in the shifted failure branch

Keep the original critical path a--c--z and the overlapping critical path
d--a--c, with c the original midpoint. Suppose a shifted kernel fails the
comparison of MS93 (5.12)(1). The previously recovered order-two radius line
H is the commutator of the full kernels Z_d intersect Q_c and Z_z intersect
Q_a. Removing either or both central edge attachments leaves that same H.
Thus H lies in both U_d and U_z, including when either cover has order 32.

The first shifted edge fixes H. Nevertheless H has trivial intersection
with the center of G_d: adjoin Z_c to the reverse kernel and apply the
full-cover fixed-hyperplane commutator theorem at d. A nonzero fixed-kernel
commutator cannot be central there. Since H has order two, normalization
would mean centralization, and local residual/edge generation shows that
the actual residual at d does not normalize H.

The selected-path application retains the original radius, its full endpoint
commutator, the opposite full kernel and the same displaced paths. Whole-core
and literal C.1.32 applications keep both covers, the original radical and
projection kernel E, including the nontrivial odd E/Q. This removes the
central-attachment ambiguity from the failure branch. The source's paired
selection still has to force normalization by the shifted residual; no
terminal contradiction or unconditional core exhaustion is asserted here.

Internal imports reuse the checked full-seed fixed-kernel calculation and
its noncentrality theorem without changing their public boundaries.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (3.3)(ii) and the failure branch of (5.12)(1), printed pp.866--867,
924--925; Aschbacher--Smith C.1.31--32, printed pp.135--136.
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
/-- The failure line is a reciprocal full-kernel commutator, and also the
moving-kernel commutator at the shifted start. It is noncentral at that start,
although the whole first shifted edge fixes it. -/
theorem plane_shifted_kernel_failure_reciprocal
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
    let F := Z Rg z ⊓ Q Rg a
    let H := ⁅V Rg a ⊓ Q Rg (p.walk.getVert 2),F⁆
    ⁅Z Rg d ⊓ Q Rg (p.walk.getVert 2),F⁆ = H ∧
      ⁅U Rg d ⊓ Q Rg (p.walk.getVert 2),F⁆ = H ∧
      ⁅Z Rg d ⊓ Q Rg (p.walk.getVert 2),U Rg z ⊓ Q Rg a⁆ = H ∧
      ⁅U Rg d ⊓ Q Rg (p.walk.getVert 2),U Rg z ⊓ Q Rg a⁆ = H ∧
      H ≤ U Rg d ⊓ U Rg z ∧
      H ≤ Z Rg (q.walk.getVert 1) ∧
      H ⊓ centralizer (stabilizer Rg d : Set (FreeAmalgam Rg)) = ⊥ ∧
      ¬ Ltilde Rg d ≤ normalizer (H : Set (FreeAmalgam Rg)) := by
  let c := p.walk.getVert 2
  let t := q.walk.getVert 1
  let F := Z Rg z ⊓ Q Rg a
  let A := Z Rg c
  let D := Z Rg d ⊓ Q Rg c
  let H := ⁅V Rg a ⊓ Q Rg c,F⁆
  let P := F ⊔ A
  have hb := distance_gt_two h e hz hk
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb4
  have hql : q.walk.length = 4 := q.length_eq_b.trans hb4
  have hdt : Adjacent Rg d t := by
    apply (cosetGraph_adj Rg _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using
      q.walk.adj_getVert_succ (i := 0) (by omega)
  have hat : Adjacent Rg a t := by
    rw [←hqa]
    exact adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp
      (q.walk.adj_getVert_succ (i := 1) (by omega)))
  have ht : color Rg t = true := by
    have hh := adjacent_color_ne Rg hdt
    rw [q.start_color] at hh
    cases he : color Rg t <;> simp_all
  have hAt : A ≤ Q Rg t := by
    apply Z_le_Q_of_dist_lt Rg _ ((sourceGeometry h).exists_critical _ q.end_color)
    rw [(sourceGeometry h).distance_constant _ q.end_color]
    have hh := q.dist_end 1
    rw [hql] at hh
    change (cosetGraph Rg).dist c t < sourceDistance h
    rw [SimpleGraph.dist_comm,hh,hb4]
    decide
  have hFt : F ≤ Q Rg t := inf_le_right.trans (Q_le_adjacent_h Rg ht hat)
  have hPt : P ≤ Q Rg t := sup_le hFt hAt
  have hda : (cosetGraph Rg).dist d a ≤ 2 := by
    rw [←hqa,q.dist_start (by omega)]
  have hDY : D ≤ V Rg a ⊓ Q Rg c := le_inf
    (inf_le_left.trans (le_iSup_of_le d (le_iSup_of_le hda le_rfl))) inf_le_right
  have hd := plane_shifted_kernel_failure_transfer h e hz hk u hR hb4 hsmall
    p q hqa hescape K hK hfail
  have hDF : ⁅D,F⁆ = H := le_antisymm (commutator_mono hDY le_rfl)
    ((show ⁅K,F⁆ = H from hd.1).symm.le.trans (commutator_mono hK le_rfl))
  have hfixed : D = Z Rg d ⊓ centralizer (A : Set (FreeAmalgam Rg)) :=
    (critical_seed_centralizer_intersection h e q).symm
  let qr := CriticalPath.ofPair (geometry := sourceGeometry h) q.end_color
    (critical_reverse Rg (sourceGeometry h) (sourceEdgeCentralizer h e)
      d q.start_color (by
        rw [(sourceGeometry h).distance_constant d q.start_color]
        exact sourceDistance_pos h) c q.end_color q.critical)
  have hmoving : U Rg d ⊓ Q Rg c =
      U Rg d ⊓ centralizer (A : Set (FreeAmalgam Rg)) :=
    critical_moving_kernel_eq_fixed h e qr
  have hUF : ⁅U Rg d ⊓ Q Rg c,F⁆ = H := by
    rw [hmoving]
    rw [←full_fixed_seed_edge_commutator h e hz q.start_color hdt A hAt F hFt,
      ←hfixed,hDF]
  have hc : color Rg c = false := q.end_color
  have hct : Adjacent Rg c (p.walk.getVert 3) :=
    (cosetGraph_adj Rg _ _).mp (p.walk.adj_getVert_succ (i := 2) (by omega))
  have hzt : Adjacent Rg z (p.walk.getVert 3) := by
    have hh := p.walk.adj_getVert_succ (i := 3) (by omega)
    rw [show 3+1=p.walk.length by omega,p.walk.getVert_length] at hh
    exact adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp hh)
  have ht' : color Rg (p.walk.getVert 3) = true := by
    have hh := adjacent_color_ne Rg hzt
    rw [p.end_color] at hh
    cases he : color Rg (p.walk.getVert 3) <;> simp_all
  have hDt : D ≤ Q Rg (p.walk.getVert 3) :=
    inf_le_right.trans (Q_le_adjacent_h Rg ht' hct)
  have hAt' : Z Rg a ≤ Q Rg (p.walk.getVert 3) := by
    apply Z_le_Q_of_dist_lt Rg _ ((sourceGeometry h).exists_critical _ p.start_color)
    rw [(sourceGeometry h).distance_constant _ p.start_color,p.dist_start (by omega)]
    change 3 < sourceDistance h
    omega
  let pr := CriticalPath.ofPair (geometry := sourceGeometry h) p.end_color
    (critical_reverse Rg (sourceGeometry h) (sourceEdgeCentralizer h e)
      a p.start_color (by
        rw [(sourceGeometry h).distance_constant a p.start_color]
        exact sourceDistance_pos h) z p.end_color p.critical)
  have hFfixed : F = Z Rg z ⊓ centralizer (Z Rg a : Set (FreeAmalgam Rg)) :=
    (critical_seed_centralizer_intersection h e pr).symm
  have hmoving' := critical_moving_kernel_eq_fixed h e p
  have strip (B : Subgroup (FreeAmalgam Rg)) (hBD : B ≤ D) :
      ⁅B,U Rg z ⊓ Q Rg a⁆ = ⁅B,F⁆ := by
    rw [hmoving',commutator_comm B,commutator_comm B,
      ←full_fixed_seed_edge_commutator h e hz p.end_color hzt
        (Z Rg a) hAt' B (hBD.trans hDt),←hFfixed]
  have hDF' : ⁅D,U Rg z ⊓ Q Rg a⁆ = H := (strip D le_rfl).trans hDF
  have hUF' : ⁅U Rg d ⊓ Q Rg c,U Rg z ⊓ Q Rg a⁆ = H :=
    (strip _ (inf_le_inf_right _ (DistanceEight.U_le_Z Rg d))).trans hUF
  have hHmoving : H ≤ U Rg d ⊓ U Rg z := by
    apply le_inf
    · rw [←hUF]
      exact (commutator_mono inf_le_left le_rfl).trans
        (le_normalizer_iff_commutator_le_left.mp
          ((hFt.trans (fun _ hx => hx.2 _ (adjacent_symm Rg hdt))).trans (U_normalized d)))
    · rw [←hDF']
      exact (commutator_mono le_rfl inf_le_left).trans
        (le_normalizer_iff_commutator_le_right.mp
          ((hDt.trans (fun _ hx => hx.2 _ (adjacent_symm Rg hzt))).trans (U_normalized z)))
  have hHedge : H ≤ Z Rg t := by
    rw [←hDF]
    exact (commutator_mono inf_le_left hFt).trans
      (plane_edge_seed_commutator h e hz hk u hR q.start_color hdt)
  have hDP : ⁅D,P⁆ = H := by
    have hDA : ⁅D,A⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr
      (hfixed ▸ inf_le_right)
    have hFA : F ≤ centralizer (A : Set (FreeAmalgam Rg)) := by
      have hzc : Z Rg z ≤ Q Rg c := by
        apply Z_le_Q_of_dist_lt Rg _ ((sourceGeometry h).exists_critical _ p.end_color)
        rw [(sourceGeometry h).distance_constant _ p.end_color,SimpleGraph.dist_comm,
          p.dist_end,hl]
        exact hb
      exact (inf_le_left.trans hzc).trans
        (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
          (Z_centralizes_Q Rg c q.end_color)))
    rw [commutator_comm]
    rw [show P = F ⊔ A from rfl,
      commutator_sup_of_commuting_factors F A D hFA
        ((show D ≤ centralizer (A : Set (FreeAmalgam Rg)) from hfixed ▸ inf_le_right).trans
          (Subgroup.centralizer_le_normalizer _)),commutator_comm F D,
      commutator_comm A D,hDF,hDA,sup_bot_eq]
  have hHcard : Nat.card H = 2 := by
    have hh := plane_four_full_kernel_line h e hz hk u hR hb4 hsmall p
      (V Rg a ⊓ Q Rg c) inf_le_left inf_le_right
      (by rwa [(plane_small_four_omega_generated h e hz hk u hR hb4 hsmall z p.end_color).2])
    rw [(plane_small_four_omega_generated h e hz hk u hR hb4 hsmall z p.end_color).2] at hh
    exact hh.1
  have hne : H ≠ ⊥ := by
    intro he
    rw [he,card_bot] at hHcard
    omega
  have hnon : ¬ H ≤ centralizer (stabilizer Rg d : Set (FreeAmalgam Rg)) := by
    let := finite_Z Rg d
    let : Finite (U Rg d) := Finite.of_injective
      (inclusion (DistanceEight.U_le_Z Rg d)) (inclusion_injective _)
    have hidx : (centralizer (A : Set (FreeAmalgam Rg))).relIndex (U Rg d) ≤ 2 :=
      ((relIndex_le_of_le_left
        (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
          (Z_centralizes_Q Rg c q.end_color))) index_ne_zero_of_finite).trans
        (relIndex_le_of_le_right (DistanceEight.U_le_Z Rg d) index_ne_zero_of_finite)).trans_eq
          (small_critical_indices h e hz hk q (hsmall _ _ q)).1
    have hn := full_seed_fixed_commutator_noncentral h e hz hk q.start_color hdt
      A P hAt hPt le_sup_right qr.critical.2 hidx
    rw [←hfixed,hDP] at hn
    exact hn hne
  have hdis : H ⊓ centralizer (stabilizer Rg d : Set (FreeAmalgam Rg)) = ⊥ := by
    let : Finite H := Nat.finite_of_card_ne_zero (by omega)
    let : Finite (H ⊓ centralizer (stabilizer Rg d : Set (FreeAmalgam Rg)) :
        Subgroup (FreeAmalgam Rg)) :=
      Finite.of_injective (inclusion inf_le_left) (inclusion_injective _)
    by_contra hn
    have hlo := (one_lt_card_iff_ne_bot _).mpr hn
    have he := eq_of_le_of_card_ge (show H ⊓ centralizer
      (stabilizer Rg d : Set (FreeAmalgam Rg)) ≤ H from inf_le_left) (by omega)
    exact hnon (he ▸ inf_le_right)
  refine ⟨hDF,hUF,hDF',hUF',hHmoving,hHedge,hdis,?_⟩
  intro hnormal
  apply hnon
  apply le_centralizer_iff.mpr
  rw [←CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.local_residual_edge_generation Rg
    (by rw [h.relative_residual]; exact (codisjoint_subgroupOf_sup L R).eq_top)
    q.start_color hdt]
  refine sup_le (hnormal.trans (normalizer_le_centralizer_of_card_two H hHcard)) ?_
  apply le_centralizer_iff.mpr
  intro x hx
  have he := hHedge hx
  rw [Z,if_neg (by simp [ht])] at he
  exact (mem_omegaCenter_iff.mp he).2.2


include h e hz hk in
/-- On the same selected radius and displaced paths, a failed shifted
comparison gives all four identical mixed kernel commutators. The common
line lies in both moved seeds, is fixed by the first shifted edge, and is
moved by the shifted local residual. -/
theorem plane_small_four_reciprocal_shifted_kernels
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
                    ⁅K,Z Rg z⁆ ⊔ T = C ∧
                    ⁅Z Rg d ⊓ Q Rg (p.walk.getVert 2),F⁆ = H ∧
                    ⁅U Rg d ⊓ Q Rg (p.walk.getVert 2),F⁆ = H ∧
                    ⁅Z Rg d ⊓ Q Rg (p.walk.getVert 2),U Rg z ⊓ Q Rg a⁆ = H ∧
                    ⁅U Rg d ⊓ Q Rg (p.walk.getVert 2),U Rg z ⊓ Q Rg a⁆ = H ∧
                    H ≤ U Rg d ⊓ U Rg z ∧ H ≤ Z Rg (r.walk.getVert 1) ∧
                    H ⊓ centralizer (stabilizer Rg d : Set (FreeAmalgam Rg)) = ⊥ ∧
                    ¬ Ltilde Rg d ≤ normalizer (H : Set (FreeAmalgam Rg))) := by
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
  · obtain ⟨hline,hHd,hfix,hi,hs,hfull⟩ :=
      plane_shifted_kernel_failure_transfer h e hz hk u hR hb4 hsmall
        p r hra hescape K hK hc
    obtain ⟨hDF,hUF,hDF',hUF',hHU,hHe,hdis,hn⟩ :=
      plane_shifted_kernel_failure_reciprocal h e hz hk u hR hb4 hsmall
        p r hra hescape K hK hc
    exact Or.inr ⟨hline,hHd,hfix,hi,hs,hfull,hDF,hUF,hDF',hUF',hHU,hHe,hdis,hn⟩

omit hk in
include h e hz in
/-- Whole-core application of the reciprocal shifted-kernel comparison.
It retains the original cubic projection and both full covers, and makes
shifted residual normalization the precise remaining failure obstruction. -/
theorem coreExhaustion_or_cubic_reciprocal_shifted_kernels :
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
                    ⁅K,Z Rg z⁆ ⊔ T = C ∧
                    ⁅Z Rg d ⊓ Q Rg (p.walk.getVert 2),F⁆ = H ∧
                    ⁅U Rg d ⊓ Q Rg (p.walk.getVert 2),F⁆ = H ∧
                    ⁅Z Rg d ⊓ Q Rg (p.walk.getVert 2),U Rg z ⊓ Q Rg a⁆ = H ∧
                    ⁅U Rg d ⊓ Q Rg (p.walk.getVert 2),U Rg z ⊓ Q Rg a⁆ = H ∧
                    H ≤ U Rg d ⊓ U Rg z ∧ H ≤ Z Rg (r.walk.getVert 1) ∧
                    H ⊓ centralizer (stabilizer Rg d : Set (FreeAmalgam Rg)) = ⊥ ∧
                    ¬ Ltilde Rg d ≤ normalizer (H : Set (FreeAmalgam Rg))))) := by
  rcases coreExhaustion_or_cubic_plane_paths h e hz with
    hex | ⟨hk,hs,hb,hcovers,u,hborel | ⟨hplane,_⟩⟩
  · exact Or.inl hex
  · exact Or.inr ⟨hk,hs,hb,hcovers,u,Or.inl hborel⟩
  · exact Or.inr ⟨hk,hs,hb,hcovers,u,Or.inr ⟨hplane,
      fun hb4 hsmall => plane_small_four_reciprocal_shifted_kernels h e hz hk u hplane hb4 hsmall⟩⟩

omit hk in
include h e hz in
/-- Literal C.1.32 application of the reciprocal comparison, keeping both
covers and all attachments in the original cubic graph. -/
theorem rankTwo_or_cubic_reciprocal_shifted_kernels :
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
                    ⁅K,Z Rg z⁆ ⊔ T = C ∧
                    ⁅Z Rg d ⊓ Q Rg (p.walk.getVert 2),F⁆ = H ∧
                    ⁅U Rg d ⊓ Q Rg (p.walk.getVert 2),F⁆ = H ∧
                    ⁅Z Rg d ⊓ Q Rg (p.walk.getVert 2),U Rg z ⊓ Q Rg a⁆ = H ∧
                    ⁅U Rg d ⊓ Q Rg (p.walk.getVert 2),U Rg z ⊓ Q Rg a⁆ = H ∧
                    H ≤ U Rg d ⊓ U Rg z ∧ H ≤ Z Rg (r.walk.getVert 1) ∧
                    H ⊓ centralizer (stabilizer Rg d : Set (FreeAmalgam Rg)) = ⊥ ∧
                    ¬ Ltilde Rg d ≤ normalizer (H : Set (FreeAmalgam Rg))))) :=
  (coreExhaustion_or_cubic_reciprocal_shifted_kernels h e hz).imp
    (rankTwo_of_exhaustion h e hz) id


end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
