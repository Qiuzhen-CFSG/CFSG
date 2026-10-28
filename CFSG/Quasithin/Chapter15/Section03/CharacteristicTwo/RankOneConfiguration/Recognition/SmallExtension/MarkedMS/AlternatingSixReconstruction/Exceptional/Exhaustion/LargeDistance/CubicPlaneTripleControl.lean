module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneForwardStrictControl
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneRadiusAlignment
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneBackward

/-!
# One second backward kernel from two central triples

For the critical path c--a--v, let b lie within two edges of c.
The full kernel Z_b intersect Q_a has reverse-kernel commutator in all
four seeds Z_b, Z_c, Z_a and Z_v. Two literal central triple intersections
therefore fix it at a and c. The retained transporter in G_a taking v to c
fixes the same subgroup and transports centrality to v. The full-cover
fixed-hyperplane comparison makes the commutator trivial.

The resulting full endpoint action is along the critical line in Z_c,
so the endpoint normalizes (Z_b intersect Q_a) join Z_c. The same kernel
can be used for two different critical endpoints. No equality of distinct
first backward kernels is required. Both moving covers and the full cubic
extension kernel E, including odd E/Q, remain in the original graph.

Source: MS93 (5.12)(1),(3), printed pp.924--927.
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



include h e hz hk in
/-- Two central seed triples control the same entire second backward kernel. -/
theorem plane_two_central_triples_kernel_control
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    (hb4 : sourceDistance h = 4)
    {a c v b : Vertex Rg} (q : CriticalPath Rg (sourceGeometry h) c v)
    (hqa : q.walk.getVert 2 = a)
    (hsmall : (Q Rg v).relIndex (Z Rg c) < 4)
    (hbc : (cosetGraph Rg).dist b c ≤ 2) (hbcol : color Rg b = false)
    (g : FreeAmalgam Rg) (hg : g ∈ stabilizer Rg a)
    (hgv : act Rg g v = c)
    (hfirst : Z Rg c ⊓ Z Rg a ⊓ Z Rg v ≤
      centralizer (stabilizer Rg a : Set (FreeAmalgam Rg)))
    (hsecond : Z Rg b ⊓ Z Rg c ⊓ Z Rg a ≤
      centralizer (stabilizer Rg c : Set (FreeAmalgam Rg))) :
    ⁅Z Rg b ⊓ Q Rg a,Z Rg v ⊓ Q Rg c⁆ = ⊥ ∧
      ⁅Z Rg b ⊓ Q Rg a,Z Rg v⁆ ≤ ⁅Z Rg c,Z Rg v⁆ ∧
      Z Rg v ≤ normalizer
        (((Z Rg b ⊓ Q Rg a) ⊔ Z Rg c : Subgroup (FreeAmalgam Rg)) : Set _) := by
  let K := Z Rg b ⊓ Q Rg a
  let F := Z Rg v ⊓ Q Rg c
  let H := ⁅K,F⁆
  let A := Z Rg c
  let P := K ⊔ A
  have hb := distance_gt_two h e hz hk
  have hl : q.walk.length = 4 := q.length_eq_b.trans hb4
  have ha : color Rg a = false := by
    rw [←hqa]
    exact (q.vertex_color (by omega)).mpr (by decide)
  have hat : Adjacent Rg a (q.walk.getVert 3) := by
    rw [←hqa]
    exact (cosetGraph_adj Rg _ _).mp (q.walk.adj_getVert_succ (i := 2) (by omega))
  have hvt : Adjacent Rg v (q.walk.getVert 3) := by
    have hh := q.walk.adj_getVert_succ (i := 3) (by omega)
    rw [show 3+1=q.walk.length by omega,q.walk.getVert_length] at hh
    exact adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp hh)
  have ht : color Rg (q.walk.getVert 3) = true := by
    have hh := adjacent_color_ne Rg hvt
    rw [q.end_color] at hh
    cases he : color Rg (q.walk.getVert 3) <;> simp_all
  have hKt : K ≤ Q Rg (q.walk.getVert 3) :=
    inf_le_right.trans (Q_le_adjacent_h Rg ht hat)
  have hKG : K ≤ stabilizer Rg v :=
    hKt.trans (fun _ hx => hx.2 _ (adjacent_symm Rg hvt))
  have hHt : H ≤ Z Rg (q.walk.getVert 3) := by
    change ⁅K,F⁆ ≤ _
    rw [commutator_comm]
    exact (commutator_mono inf_le_left hKt).trans
      (plane_edge_seed_commutator h e hz hk u hR q.end_color hvt)
  have hHa : H ≤ Z Rg a := hHt.trans (adjacent_Z_le Rg ha hat)
  have hHv : H ≤ Z Rg v := hHt.trans (adjacent_Z_le Rg q.end_color hvt)
  have hKV : K ≤ V Rg c := inf_le_left.trans
    (le_iSup_of_le b (le_iSup_of_le hbc le_rfl))
  have hHc : H ≤ Z Rg c :=
    (commutator_mono hKV inf_le_right).trans
      (plane_radius_core_commutator h e hz hk u hR q.start_color)
  have hFGb : F ≤ stabilizer Rg b := inf_le_right.trans
    (Q_le_stabilizer_of_dist_le_two c b q.start_color hbcol (by rwa [SimpleGraph.dist_comm]))
  have hHb : H ≤ Z Rg b :=
    (commutator_mono inf_le_left le_rfl).trans
      (le_normalizer_iff_commutator_le_left.mp (hFGb.trans (Z_normalized Rg b)))
  have hcA : H ≤ centralizer (stabilizer Rg a : Set (FreeAmalgam Rg)) :=
    (le_inf (le_inf hHc hHa) hHv).trans hfirst
  have hcC : H ≤ centralizer (stabilizer Rg c : Set (FreeAmalgam Rg)) :=
    (le_inf (le_inf hHb hHc) hHa).trans hsecond
  have hrestore : act Rg g⁻¹ c = v := by
    rw [←hgv,←act_mul,mul_inv_cancel,act_one]
  have hcV : H ≤ centralizer (stabilizer Rg v : Set (FreeAmalgam Rg)) := by
    rw [←hrestore,stabilizer_act]
    have hh := (map_mono (f := (MulAut.conj g).toMonoidHom) hcC).trans
      (map_centralizer_le_centralizer_image _ _)
    have hf : H.map (MulAut.conj g).toMonoidHom = H :=
      mem_normalizer_iff_map_conj_eq.mp (Subgroup.centralizer_le_normalizer _
        (le_centralizer_iff.mp hcA hg))
    simpa only [inv_inv,hf,Subgroup.coe_map] using hh
  have hAt : A ≤ Q Rg (q.walk.getVert 3) := by
    apply Z_le_Q_of_dist_lt Rg _ ((sourceGeometry h).exists_critical _ q.start_color)
    rw [(sourceGeometry h).distance_constant _ q.start_color,q.dist_start (by omega)]
    change 3 < sourceDistance h
    omega
  let qr := CriticalPath.ofPair (geometry := sourceGeometry h) q.end_color
    (critical_reverse Rg (sourceGeometry h) (sourceEdgeCentralizer h e)
      c q.start_color (by
        rw [(sourceGeometry h).distance_constant _ q.start_color]
        exact sourceDistance_pos h) v q.end_color q.critical)
  have hfixed : F = Z Rg v ⊓ centralizer (A : Set (FreeAmalgam Rg)) :=
    (critical_seed_centralizer_intersection h e qr).symm
  have hKQc : K ≤ Q Rg c := inf_le_left.trans (by
    apply Z_le_Q_of_dist_lt Rg _ ((sourceGeometry h).exists_critical _ hbcol)
    rw [(sourceGeometry h).distance_constant _ hbcol]
    exact hbc.trans_lt hb)
  have hKA : K ≤ centralizer (A : Set (FreeAmalgam Rg)) := hKQc.trans
    (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q Rg c q.start_color)))
  have hFP : ⁅F,P⁆ = H := by
    have hFA : ⁅F,A⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr (hfixed ▸ inf_le_right)
    rw [commutator_comm]
    rw [show P = K ⊔ A from rfl,
      commutator_sup_of_commuting_factors K A F hKA
        ((show F ≤ centralizer (A : Set (FreeAmalgam Rg)) from hfixed ▸ inf_le_right).trans
          (Subgroup.centralizer_le_normalizer _)),commutator_comm A F,hFA,sup_bot_eq]
  have hzero : H = ⊥ := by
    by_contra hne
    let := finite_Z Rg v
    let : Finite (U Rg v) := Finite.of_injective
      (inclusion (DistanceEight.U_le_Z Rg v)) (inclusion_injective _)
    have hidx : (centralizer (A : Set (FreeAmalgam Rg))).relIndex (U Rg v) ≤ 2 :=
      ((relIndex_le_of_le_left
        (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
          (Z_centralizes_Q Rg c q.start_color))) index_ne_zero_of_finite).trans
        (relIndex_le_of_le_right (DistanceEight.U_le_Z Rg v) index_ne_zero_of_finite)).trans_eq
          (small_critical_indices h e hz hk q hsmall).2
    have hn := full_seed_fixed_commutator_noncentral h e hz hk q.end_color hvt
      A P hAt (sup_le hKt hAt) le_sup_right q.critical.2 hidx
    rw [←hfixed,hFP] at hn
    exact hn hne hcV
  have hcontrol : ⁅K,Z Rg v⁆ ≤ ⁅Z Rg c,Z Rg v⁆ :=
    small_critical_kernel_commutator h e hz hk q hsmall K hKG
      (commutator_eq_bot_iff_le_centralizer.mp hzero)
  refine ⟨hzero,hcontrol,?_⟩
  apply le_normalizer_iff_commutator_le_left.mpr
  apply le_trans _ le_sup_right
  apply commutator_sup_le_of_relative_normal (stabilizer Rg c)
      K (Z Rg c) (Z Rg v) (Z Rg c) (Z_normalized Rg c)
      (hKQc.trans (fun _ hx => hx.1)) (Z_le_stabilizer Rg c)
  · exact hcontrol.trans (critical_seed_commutator_le h q)
  · exact critical_seed_commutator_le h q

end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
