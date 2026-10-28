module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneSmallOpposite
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneSuccessiveKernels
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneRadiusPair
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlanePairedKernelSlice
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneShiftedConfiguration
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneRadiusLine

/-!
# The central forward triple in the original cubic plane branch

The raw strict-forward comparison also holds when the forward seed triple
is central at the midpoint. Its commutator lies in that literal triple,
so this supplies the midpoint fixation directly. The retained transporter
and the full-cover fixed-hyperplane argument again kill both trapped and
critical raw cases.

Applying the original paired selector transports the same central triple.
The common kernel lies in the Baumann subgroup, and strictness forces two
critical backward paths with distinct kernels. Their joint image supplies
compatible endpoint generation, and the second backward kernel contradiction
closes this branch. The cubic kernel E, odd E/Q, and both moving covers remain.

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
theorem plane_raw_shifted_kernels_of_forward_strict_triple
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
    (hforwardTriple : Z Rg a ⊓ Z Rg (p.walk.getVert 2) ⊓ Z Rg z ≤
      centralizer (stabilizer Rg (p.walk.getVert 2) : Set (FreeAmalgam Rg))) :
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
  have hHz : H ≤ Z Rg z := hHt.trans (adjacent_Z_le Rg p.end_color hzt)
  have hcC : H ≤ centralizer (stabilizer Rg (p.walk.getVert 2) : Set (FreeAmalgam Rg)) :=
    (le_inf (le_inf hHa hHc) hHz).trans hforwardTriple
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

include h e hz hk in
/-- The original strict forward slice is incompatible with a central
forward seed triple. The actual paired selector supplies every later actor. -/
theorem plane_strict_forward_central_triple_false
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    (hb4 : sourceDistance h = 4)
    (hsmall : ∀ a z (_p : CriticalPath Rg (sourceGeometry h) a z),
      (Q Rg z).relIndex (Z Rg a) < 4)
    {a z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (hforward : 2 < (B Rg a ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (p.walk.getVert 2)))
    (hforwardTriple : Z Rg a ⊓ Z Rg (p.walk.getVert 2) ⊓ Z Rg z ≤
      centralizer (stabilizer Rg (p.walk.getVert 2) : Set (FreeAmalgam Rg))) : False := by
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
  have hforwardTriple' : Z Rg a ⊓ Z Rg (p'.walk.getVert 2) ⊓
      Z Rg (act Rg x z) ≤
      centralizer (stabilizer Rg (p'.walk.getVert 2) : Set (FreeAmalgam Rg)) := by
    have hh := (map_mono (f := (MulAut.conj x⁻¹).toMonoidHom) hforwardTriple).trans
      (map_centralizer_le_centralizer_image _ _)
    rw [Subgroup.map_inf _ _ _ (MulAut.conj x⁻¹).injective,
      Subgroup.map_inf _ _ _ (MulAut.conj x⁻¹).injective] at hh
    rw [←Subgroup.coe_map,←stabilizer_act] at hh
    simpa only [←Z_act,hxa,hverts] using hh
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
  have hiControl := plane_raw_shifted_kernels_of_forward_strict_triple
    h e hz hk u hR hb4 hsmall p hds has I inf_le_left hfirst g hg rfl hforward hforwardTriple
  have hiControl' := plane_raw_shifted_kernels_of_forward_strict_triple
    h e hz hk u hR hb4 hsmall p' hds has I inf_le_right hfirst' k hkG hkd hforward' hforwardTriple'
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
