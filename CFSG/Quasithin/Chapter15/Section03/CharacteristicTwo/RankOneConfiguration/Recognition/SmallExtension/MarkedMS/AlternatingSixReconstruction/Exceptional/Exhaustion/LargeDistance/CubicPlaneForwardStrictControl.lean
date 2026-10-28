module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneRawComparison
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlanePredecessor
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneSuccessiveKernels
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneRadiusPair

/-!
# Raw shifted kernels with a strict forward and small opposite slice

For a critical path a--v--c--t--z, retain a preceding segment d--s--a,
its generating edge cores at a, and an actual element of G_a taking c to d.
A strict forward slice puts the full shifted-kernel commutator in Z_v.
Its placement in Z_s then fixes it under G_a. The small opposite slice
fixes the same commutator under G_c, so the retained element transfers
this fixation to G_d.

If d--s--a--v--c is critical, the full-cover fixed-hyperplane comparison
makes the commutator trivial. Otherwise the entire seed Z_d is in Q_c;
the central attachment disappears from its commutator, and faithfulness
of the natural quotient kills the remaining moving-cover action.
Thus both raw cases give literal full-kernel control. The original cubic
kernel E, its odd E/Q and both moving covers of orders sixteen and thirty-two
are retained. No containment between two differently shifted kernels is
asserted, and the terminal exclusion still requires the paired comparison.

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
/-- The same raw backward kernel fixes the reverse endpoint kernel and
moves the full endpoint seed only along the original critical line. -/
theorem plane_raw_shifted_kernels_of_forward_strict_opposite_small
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    (hb4 : sourceDistance h = 4)
    (hsmall : ∀ a z (_p : CriticalPath Rg (sourceGeometry h) a z),
      (Q Rg z).relIndex (Z Rg a) < 4)
    {a z d : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    {s : Vertex Rg} (hds : Adjacent Rg d s) (has : Adjacent Rg a s)
    (K : Subgroup (FreeAmalgam Rg)) (hK : K ≤ Z Rg d ⊓ Q Rg (p.walk.getVert 2))
    (hgen : Q Rg s ⊔ Q Rg (p.walk.getVert 1) = stabilizer Rg a)
    (g : FreeAmalgam Rg) (hg : g ∈ stabilizer Rg a)
    (hgd : act Rg g (p.walk.getVert 2) = d)
    (hforward : 2 < (B Rg a ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (p.walk.getVert 2)))
    (hopposite : (B Rg (p.walk.getVert 2) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg z) ≤ 2) :
    ⁅K,Z Rg z ⊓ Q Rg a⁆ = ⊥ ∧ ⁅K,Z Rg z⁆ ≤ ⁅Z Rg a,Z Rg z⁆ := by
  have hb := distance_gt_two h e hz hk
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb4
  have hsc : color Rg s = true := by
    have hh := adjacent_color_ne Rg has
    rw [p.start_color] at hh
    cases he : color Rg s <;> simp_all
  have hd : color Rg d = false := by
    have hh := adjacent_color_ne Rg hds
    rw [hsc] at hh
    cases he : color Rg d <;> simp_all
  have hc : color Rg (p.walk.getVert 2) = false :=
    (p.vertex_color (by omega)).mpr (by decide)
  let w : (cosetGraph Rg).Walk d a :=
    .cons ((cosetGraph_adj Rg _ _).mpr hds)
      (.cons ((cosetGraph_adj Rg _ _).mpr (adjacent_symm Rg has)) .nil)
  have hw : w.length = 2 := rfl
  let H := ⁅Z Rg d ⊓ Q Rg (p.walk.getVert 2),Z Rg z ⊓ Q Rg a⁆
  have hda : (cosetGraph Rg).dist d a ≤ 2 := (cosetGraph Rg).dist_le w
  have hDV : Z Rg d ⊓ Q Rg (p.walk.getVert 2) ≤ V Rg a :=
    inf_le_left.trans (le_iSup_of_le d (le_iSup_of_le hda le_rfl))
  have hHa : H ≤ Z Rg a :=
    (commutator_mono hDV inf_le_right).trans
      (plane_radius_core_commutator h e hz hk u hR p.start_color)
  have hav : Adjacent Rg a (p.walk.getVert 1) := by
    apply (cosetGraph_adj Rg _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using
      p.walk.adj_getVert_succ (i := 0) (by omega)
  have hcv : Adjacent Rg (p.walk.getVert 2) (p.walk.getVert 1) :=
    adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp
      (p.walk.adj_getVert_succ (i := 1) (by omega)))
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
  have hDt : Z Rg d ⊓ Q Rg (p.walk.getVert 2) ≤ Q Rg (p.walk.getVert 3) :=
    inf_le_right.trans (Q_le_adjacent_h Rg ht hct)
  have hHt : H ≤ Z Rg (p.walk.getVert 3) := by
    rw [show H = ⁅Z Rg d ⊓ Q Rg (p.walk.getVert 2),Z Rg z ⊓ Q Rg a⁆ from rfl,
      commutator_comm]
    exact (commutator_mono inf_le_left hDt).trans
      (plane_edge_seed_commutator h e hz hk u hR p.end_color hzt)
  have hHc : H ≤ Z Rg (p.walk.getVert 2) := hHt.trans
    (adjacent_Z_le Rg hc hct)
  have hHv : H ≤ Z Rg (p.walk.getVert 1) :=
    (le_inf hHc hHa).trans_eq
      (plane_strict_slice_eq_edge h e hz hk u hR p.start_color hc hav hcv hforward).2.1
  have hHs : H ≤ Z Rg s :=
    (commutator_mono inf_le_left (inf_le_right.trans (Q_le_adjacent_h Rg hsc has))).trans
      (plane_edge_seed_commutator h e hz hk u hR hd hds)
  have hcA : H ≤ centralizer (stabilizer Rg a : Set (FreeAmalgam Rg)) :=
    (le_inf hHs hHv).trans
      ((plane_generating_edge_seed_intersection h e hz hk u hR p.start_color
        has hav hgen).le.trans inf_le_right)
  have hop : (B Rg (p.walk.getVert (p.walk.length-2))
      ((sourceGeometry h).Z_normal _)).relIndex (U Rg z) ≤ 2 := by
    simpa only [hl,Nat.reduceSub] using hopposite
  have hmid := (plane_predecessor_slice_commutator_central h e hz hk u hR p hop).2.2
  have hcC : H ≤ centralizer (stabilizer Rg (p.walk.getVert 2) : Set (FreeAmalgam Rg)) := by
    change ⁅_,_⁆ ≤ _
    rw [commutator_comm]
    exact (commutator_mono le_rfl inf_le_right).trans
      (by simpa only [hl,Nat.reduceSub] using hmid)
  have hm : H.map (MulAut.conj g⁻¹).toMonoidHom = H :=
    mem_normalizer_iff_map_conj_eq.mp
      ((le_centralizer_iff.mp hcA).trans (Subgroup.centralizer_le_normalizer _)
        ((stabilizer Rg a).inv_mem hg))
  have hcD := (map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hcC).trans
    (map_centralizer_le_centralizer_image _ _)
  change H.map (MulAut.conj g⁻¹).toMonoidHom ≤
    centralizer (((stabilizer Rg (p.walk.getVert 2)).map
      (MulAut.conj g⁻¹).toMonoidHom) : Set (FreeAmalgam Rg)) at hcD
  rw [hm,←stabilizer_act,hgd] at hcD
  have hFs : Z Rg z ⊓ Q Rg a ≤ Q Rg s :=
    inf_le_right.trans (Q_le_adjacent_h Rg hsc has)
  have hFG : Z Rg z ⊓ Q Rg a ≤ stabilizer Rg d :=
    hFs.trans (fun _ hv => hv.2 _ (adjacent_symm Rg hds))
  have he : H = ⊥ := by
    by_cases hn : Z Rg d ≤ Q Rg (p.walk.getVert 2)
    ·
      have hHU : H = ⁅U Rg d,Z Rg z ⊓ Q Rg a⁆ := by
        change ⁅Z Rg d ⊓ Q Rg (p.walk.getVert 2),Z Rg z ⊓ Q Rg a⁆ = _
        rw [inf_eq_left.mpr hn]
        exact full_seed_commutator_eq_moving h e hz hd hds _ hFs
      exact hHU.trans
        (graph_moving_central_commutator_eq_bot h e hz hk hd _ hFG (hHU ▸ hcD))
    ·
      have hns : ¬ Z Rg d ≤ Q Rg (p.walk.getVert (p.walk.length-2)) := by
        simpa only [hl,Nat.reduceSub] using hn
      let q := p.prepend_two (Nat.le_of_lt hb) hd w hw hns
      have he : p.walk.getVert (p.walk.length-2) = p.walk.getVert 2 := by rw [hl]
      have hq : ∃ q : CriticalPath Rg (sourceGeometry h) d
          (p.walk.getVert (p.walk.length-2)),
          q.walk.getVert 1 = s ∧ q.walk.getVert 2 = a := by
        refine ⟨q,?_,?_⟩
        · simp only [q,CriticalPath.prepend_two_walk,SimpleGraph.Walk.getVert_append,
            hw,show 1<2 from by decide,ite_true,w,SimpleGraph.Walk.getVert_cons_succ,
            SimpleGraph.Walk.getVert_zero]
        · simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using
            p.prepend_two_overlap (Nat.le_of_lt hb) hd w hw hns (i := 0) (by omega)
      rw [he] at hq
      obtain ⟨q,hq1,hq2⟩ := hq
      by_contra hne
      exact full_shifted_kernel_noncentral h e hz hk hb4 p q hq2
        (hsmall _ _ q) hne hcD
  have hKF : ⁅K,Z Rg z ⊓ Q Rg a⁆ = ⊥ :=
    bot_unique ((commutator_mono hK le_rfl).trans_eq he)
  have hKG : K ≤ stabilizer Rg z :=
    (hK.trans hDt).trans (fun _ hx => hx.2 _ (adjacent_symm Rg hzt))
  exact ⟨hKF,small_critical_kernel_commutator h e hz hk p (hsmall _ _ p) K hKG
    (commutator_eq_bot_iff_le_centralizer.mp hKF)⟩

end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
