module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneSecondBackward
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlanePairedKernelSlice
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneShiftedConfiguration
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneRadiusLine

/-!
# A strict forward cubic plane slice has a strict opposite slice

Use the original normalized paired selector and its same component switch.
A small opposite slice controls both raw backward kernels by the strict-forward
comparison. Their common kernel is normalized by the joint endpoint actors,
so it lies in the Baumann subgroup. The transported strict slice then forces
both backward candidates to be critical with distinct full kernels.

Their joint midpoint image has order greater than two, so the original
large-subactor generation theorem supplies a compatible edge. The same two
central triple intersections and their actual transporters now invoke the
second backward kernel contradiction. This discharges the small opposite
case from the original source inputs, preserving both full moving covers,
the nonsylow radical, and the cubic kernel E with its odd quotient E/Q.

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
/-- A strict forward slice and small opposite slice are impossible on the
original plane graph at distance four with uniformly small critical images. -/
theorem plane_strict_forward_small_opposite_false
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    (hb4 : sourceDistance h = 4)
    (hsmall : ∀ a z (_p : CriticalPath Rg (sourceGeometry h) a z),
      (Q Rg z).relIndex (Z Rg a) < 4)
    {a z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (hforward : 2 < (B Rg a ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (p.walk.getVert 2)))
    (hopposite : (B Rg (p.walk.getVert 2) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg z) ≤ 2) : False := by
  have hb := distance_gt_two h e hz hk
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb4
  have hc : color Rg (p.walk.getVert 2) = false :=
    (p.vertex_color (by omega)).mpr (by decide)
  have hav : Adjacent Rg a (p.walk.getVert 1) := by
    simpa only [SimpleGraph.Walk.getVert_zero] using
      (cosetGraph_adj Rg _ _).mp (p.walk.adj_getVert_succ (i := 0) (by omega))
  have hcv : Adjacent Rg (p.walk.getVert 2) (p.walk.getVert 1) :=
    adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp
      (p.walk.adj_getVert_succ (i := 1) (by omega)))
  obtain ⟨s,has,x,hx,hgen,hpair,hnorm,hinside⟩ :=
    normalized_plane_selectors_at h e hz hk u hR p (hsmall _ _ p)
  have hfirst : Q Rg s ⊔ Q Rg (p.walk.getVert 1) = stabilizer Rg a := by
    apply le_antisymm
    · exact sup_le (fun _ hv => hv.2 _ (adjacent_symm Rg has))
        (fun _ hv => hv.2 _ (adjacent_symm Rg hav))
    · rw [←hgen]
      exact sup_le (sup_le le_sup_left ((le_sup_left.trans hinside).trans le_sup_right))
        ((le_sup_right.trans hinside).trans le_sup_right)
  have hxa : act Rg x a = a := hx
  obtain ⟨p',hverts⟩ : ∃ p' : CriticalPath Rg (sourceGeometry h) a (act Rg x z),
      ∀ i, p'.walk.getVert i = act Rg x (p.walk.getVert i) := by
    have hh : ∃ p' : CriticalPath Rg (sourceGeometry h) (act Rg x a) (act Rg x z),
        ∀ i, p'.walk.getVert i = act Rg x (p.walk.getVert i) :=
      ⟨p.act x,fun _ => by simp only [CriticalPath.act,actWalk_getVert]⟩
    rwa [hxa] at hh
  have hl' : p'.walk.length = 4 := p'.length_eq_b.trans hb4
  have hav' : Adjacent Rg a (p'.walk.getVert 1) := by
    simpa only [SimpleGraph.Walk.getVert_zero] using
      (cosetGraph_adj Rg _ _).mp (p'.walk.adj_getVert_succ (i := 0) (by omega))
  have hcv' : Adjacent Rg (p'.walk.getVert 2) (p'.walk.getVert 1) :=
    adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp
      (p'.walk.adj_getVert_succ (i := 1) (by omega)))
  have hQfirst : Q Rg (p'.walk.getVert 1) = Q Rg (p.walk.getVert 1) := by
    rw [hverts 1,Q_act]
    exact mem_normalizer_iff_map_conj_eq.mp
      ((normalizer (Q Rg (p.walk.getVert 1) : Set (FreeAmalgam Rg))).inv_mem hnorm)
  have hfirst' : Q Rg s ⊔ Q Rg (p'.walk.getVert 1) = stabilizer Rg a := by
    rwa [hQfirst]
  have hforward' : 2 < (B Rg a ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (p'.walk.getVert 2)) := by
    have hB := Escape.PairingControl.FirstPairing.B_act
      (geometry := sourceGeometry h) hb x a p.start_color
    rw [hxa] at hB
    rw [hverts 2,hB,U_act,relIndex_map_map_of_injective _ _ (MulAut.conj x⁻¹).injective]
    exact hforward
  have hopposite' : (B Rg (p'.walk.getVert 2) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (act Rg x z)) ≤ 2 := by
    rw [hverts 2,Escape.PairingControl.FirstPairing.B_act hb x _ hc,U_act,
      relIndex_map_map_of_injective _ _ (MulAut.conj x⁻¹).injective]
    exact hopposite
  obtain ⟨g,hg,hgs⟩ := stabilizer_transitive_neighbors Rg a hav has
  let d := act Rg g (p.walk.getVert 2)
  have hds : Adjacent Rg d s := by
    rw [←hgs]
    exact (adjacent_act_iff Rg g _ _).mpr hcv
  have hd : color Rg d = false := (action_preserves_color Rg _ _).trans hc
  have hBmap : (B Rg a ((sourceGeometry h).Z_normal _)).map
      (MulAut.conj g⁻¹).toMonoidHom = B Rg a ((sourceGeometry h).Z_normal _) :=
    mem_normalizer_iff_map_conj_eq.mp (Escape.Propagation.Rigidity.B_normalized
      hb a p.start_color ((stabilizer Rg a).inv_mem hg))
  have hstrict : 2 < (B Rg a ((sourceGeometry h).Z_normal _)).relIndex (U Rg d) := by
    dsimp only [d]
    rw [U_act,←hBmap,relIndex_map_map_of_injective _ _ (MulAut.conj g⁻¹).injective]
    exact hforward
  let k := x⁻¹*g
  have hkG : k ∈ stabilizer Rg a := mul_mem (inv_mem hx) hg
  have hkd : act Rg k (p'.walk.getVert 2) = d := by
    rw [hverts 2,show k = x⁻¹*g from rfl,←act_mul,mul_inv_cancel_left]
  let I := (Z Rg d ⊓ Q Rg (p.walk.getVert 2)) ⊓
    (Z Rg d ⊓ Q Rg (p'.walk.getVert 2))
  have hiControl := plane_raw_shifted_kernels_of_forward_strict_opposite_small
    h e hz hk u hR hb4 hsmall p hds has I inf_le_left hfirst g hg rfl hforward hopposite
  have hiControl' := plane_raw_shifted_kernels_of_forward_strict_opposite_small
    h e hz hk u hR hb4 hsmall p' hds has I inf_le_right hfirst' k hkG hkd hforward' hopposite'
  have hraw := raw_preceding_kernel_normalized h e hz hk u hR hb4 hsmall p has hds
  have hraw' := raw_preceding_kernel_normalized h e hz hk u hR hb4 hsmall p' has hds
  have hIN : Q Rg s ≤ normalizer (I : Set (FreeAmalgam Rg)) :=
    (le_inf hraw.1 hraw'.1).trans inf_normalizer_le_normalizer_inf
  let w : (cosetGraph Rg).Walk d a :=
    .cons ((cosetGraph_adj Rg _ _).mpr hds)
      (.cons ((cosetGraph_adj Rg _ _).mpr (adjacent_symm Rg has)) .nil)
  have hda : (cosetGraph Rg).dist d a ≤ 2 := (cosetGraph Rg).dist_le w
  have hIV : I ≤ V Rg a := (inf_le_left.trans inf_le_left).trans
    (le_iSup_of_le d (le_iSup_of_le hda le_rfl))
  have hIB : I ≤ B Rg a ((sourceGeometry h).Z_normal _) :=
    paired_controlled_subgroup_le_slice h e hz hb p p' has hgen I hIV hIN
      (hiControl.2.trans (critical_seed_commutator_le h p))
      (hiControl'.2.trans (critical_seed_commutator_le h p'))
  obtain ⟨q,q',hq1,hq1',hqv,hqv',hI,hjoin,hne⟩ :=
    raw_paired_paths_of_strict_slice h e hz hk u hR hb4 hsmall p p' has hds hIB hstrict
  have hqa : q.walk.getVert 2 = a := by
    simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using hqv 0 (by omega)
  have hqa' : q'.walk.getVert 2 = a := by
    simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using hqv' 0 (by omega)
  have hlarge := small_critical_distinct_kernels_joint_image h e hz hk q q'
    (hsmall _ _ q) (hsmall _ _ q') hne
  obtain ⟨t,hdt,hpairD,hactors⟩ := plane_paired_midpoints_generate h e hz hk u hR q q'
    hq1 hq1' (hsmall _ _ q) hlarge
  have triple {c v : Vertex Rg} (hc : color Rg c = false)
      (hav : Adjacent Rg a v) (hcv : Adjacent Rg c v)
      (hforw : 2 < (B Rg a ((sourceGeometry h).Z_normal _)).relIndex (U Rg c))
      (hgen : Q Rg s ⊔ Q Rg v = stabilizer Rg a) :
      Z Rg d ⊓ Z Rg a ⊓ Z Rg c ≤ centralizer (stabilizer Rg a : Set (FreeAmalgam Rg)) := by
    have hdsEq := (plane_strict_slice_eq_edge h e hz hk u hR p.start_color hd has hds hstrict).2.1
    have hcvEq := (plane_strict_slice_eq_edge h e hz hk u hR p.start_color hc hav hcv hforw).2.1
    exact (le_inf (inf_le_left.trans_eq hdsEq)
      ((le_inf inf_le_right (inf_le_left.trans inf_le_right)).trans_eq hcvEq)).trans
      ((plane_generating_edge_seed_intersection h e hz hk u hR p.start_color has hav hgen).le.trans
        inf_le_right)
  have htriple := triple hc hav hcv hforward hfirst
  have htriple' := triple ((p'.vertex_color (by omega)).mpr (by decide))
    hav' hcv' hforward' hfirst'
  exact plane_paired_second_backward_strict_false h e hz hk hb4 u hR hsmall
    q q' hqa hqa' has hds hdt hstrict ((sup_comm _ _).trans hpairD)
    (by simpa only [sup_assoc] using hactors) g hg rfl k hkG hkd htriple htriple'

end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
