module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.DistanceFourAllImages
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.DistanceFourKernels
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.DistanceFourTrapped
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.DistanceFourStabilizers
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.TerminalKernels
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.SmallShifts
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.EqualKernels

/-!
# Equal-mover selections at distance four on the original Borel graph

Two selected full kernels act on the same reverse critical kernel. Equal
incident Thompson movers place each displacement in the original seed and
fix it. If both full-omega normalizations fail, their nonzero displacements
are lines. The combined quadratic-actor bound makes those lines equal,
and the two generating movers consequently fix the common line under the
whole starting stabilizer. The compatible forward path and actual residual
transporter carry this centrality to the selected endpoint, contradicting
its full-cover movement calculation.

This also handles a selected seed trapped in the midpoint core: its kernel
is the entire seed and the whole-seed movement theorem supplies the endpoint
contradiction. Once one kernel is normalized, a trapped seed would give a
normal two-seed span of section order dividing eight. The genuine A6 action
places it in the Baumann slice, contrary to forward eligibility. Thus the
same residual selectors give an actual normalized backward critical path.

Combining this equal-mover argument with the distinct-mover result removes
the distinctness premise from backward selection. Forward smallness, the
initial compatible generating path, and the full fixed-subgroup comparison
in the distinct case remain explicit. No backward image bound, replacement
graph, or identification of the cubic kernel E with its two-core is used.
Both moving covers and their full central attachments are retained.
OriginalSylowExceptional applies the results to the literal c.L,d.S graph.
CoreExhaustion and the final exceptional reconstruction remain open.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (5.6)--(5.7) and (5.12)(1), printed pp.917--919,924--925;
Aschbacher--Smith C.1.31--32, printed pp.135--136.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender BinaryPermutation
open Theory.SpecificGroups.SymmetricSix Theory.SpecificGroups.SymmetricSix.BinaryFlags
open Theory.GroupTheory Representation.NormalElementaryQuotient
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open scoped IsMulCommutative commutatorElement Pointwise
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.OriginalSylow
open Exhaustion Exhaustion.LargeDistance Exhaustion.LargeDistance.CubicFull
local notation "borel" => Theory.SpecificGroups.SymmetricSix.borel
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "Rg" => edge L R
local notation "π" => CubicAction.projection h e hz hk


private theorem normalize_join_of_commutator {F : Type*} [Group F]
    (K Z A : Subgroup F) (hAZ : A ≤ normalizer (Z : Set F))
    (hm : ⁅K,A⁆ ≤ Z) : A ≤ normalizer ((K ⊔ Z : Subgroup F) : Set F) := by
  apply le_normalizer_iff.mpr
  intro x hx v hv
  have hmap : (K ⊔ Z).map (MulAut.conj x).toMonoidHom ≤ K ⊔ Z := by
    rw [Subgroup.map_sup]
    refine sup_le ?_ ((mem_normalizer_iff_map_conj_eq.mp (hAZ hx)).le.trans le_sup_right)
    rintro _ ⟨k,hk,rfl⟩
    have hh := (K ⊔ Z).mul_mem (mem_sup_right (hm (by
      rw [commutator_comm]; exact commutator_mem_commutator hx hk))) (mem_sup_left hk)
    simpa [MulAut.conj_apply,commutatorElement_def,mul_assoc] using hh
  exact hmap (mem_map_of_mem (MulAut.conj x).toMonoidHom hv)

include h in
private theorem four_prepend_selected
    (hb : sourceDistance h = 4)
    {a z d t : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (hd : color Rg d = false) (hat : Adjacent Rg a t) (hdt : Adjacent Rg d t)
    (hne : ¬ Z Rg d ≤ Q Rg (p.walk.getVert 2)) :
    ∃ q : CriticalPath Rg (sourceGeometry h) d (p.walk.getVert 2),
      q.walk.getVert 1 = t ∧ ∀ i ≤ 2, q.walk.getVert (i+2) = p.walk.getVert i := by
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  let w : (cosetGraph Rg).Walk d a :=
    .cons ((cosetGraph_adj Rg _ _).mpr hdt)
      (.cons ((cosetGraph_adj Rg _ _).mpr (adjacent_symm Rg hat)) .nil)
  have hw : w.length = 2 := rfl
  have hne' : ¬ Z Rg d ≤ Q Rg (p.walk.getVert (p.walk.length-2)) := by
    simpa only [hl,Nat.reduceSub] using hne
  have hb2 : 2 ≤ (sourceGeometry h).b Rg := by change 2 ≤ sourceDistance h; omega
  let q := p.prepend_two hb2 hd w hw hne'
  have hq : ∃ q' : CriticalPath Rg (sourceGeometry h) d (p.walk.getVert (p.walk.length-2)),
      q'.walk.getVert 1 = t ∧ ∀ i ≤ 2, q'.walk.getVert (i+2) = p.walk.getVert i := by
    refine ⟨q,?_,?_⟩
    · change (p.prepend_two hb2 hd w hw hne').walk.getVert 1 = t
      rw [p.prepend_two_walk hb2 hd w hw hne']
      simp only [SimpleGraph.Walk.getVert_append,
        hw,show 1<2 from by decide,ite_true,w,SimpleGraph.Walk.getVert_cons_succ,
        SimpleGraph.Walk.getVert_zero]
    · intro i hi
      exact p.prepend_two_overlap _ _ _ _ _ (by omega)
  rw [show p.walk.length-2=2 by omega] at hq
  exact hq

include h e hz hk in
private theorem equal_selected_failure
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {a z d t : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (hp : (Q Rg z).relIndex (Z Rg a) < 4)
    (hd : color Rg d = false) (hat : Adjacent Rg a t) (hdt : Adjacent Rg d t)
    (heq : edgeOffenderJoin a t = edgeOffenderJoin d t)
    (hn : ¬ X Rg z ≤ normalizer
      (((Z Rg d ⊓ Q Rg (p.walk.getVert 2)) ⊔ Z Rg a : Subgroup (FreeAmalgam Rg)) : Set _)) :
    let K := Z Rg d ⊓ Q Rg (p.walk.getVert 2)
    let H := ⁅K,Z Rg z ⊓ Q Rg a⁆
    Nat.card H = 2 ∧ H ≤ Z Rg a ∧ H ≤ Z Rg z ∧
      H ≤ centralizer (edgeOffenderJoin a t : Set (FreeAmalgam Rg)) ∧
      ¬ H ≤ centralizer (stabilizer Rg d : Set (FreeAmalgam Rg)) ∧
      ¬ ⁅K,Z Rg z⁆ ≤ Z Rg a := by
  let c := p.walk.getVert 2
  let K := Z Rg d ⊓ Q Rg c
  let F := Z Rg z ⊓ Q Rg a
  let H := ⁅K,F⁆
  have hb := borel_distance_eq_four h e hz hk u hR
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hc : color Rg c = false := (p.vertex_color (by omega)).mpr (by decide)
  have ht : color Rg t = true := by
    have hh := adjacent_color_ne Rg hat
    rw [p.start_color] at hh
    exact Bool.eq_true_of_not_eq_false (Ne.symm hh)
  have hKV : K ≤ V Rg a := inf_le_left.trans (terminal_neighbor_seed_radius hat hdt)
  have htrap : K ≤ Q Rg (p.walk.getVert (p.walk.length-2)) := by
    simpa only [hl,Nat.reduceSub] using (inf_le_right : K ≤ Q Rg c)
  have hZd : Q Rg a ≤ stabilizer Rg d :=
    (Q_le_adjacent_h Rg ht hat).trans (fun _ hv => hv.2 _ (adjacent_symm Rg hdt))
  have hzdist : (cosetGraph Rg).dist z c = 2 := by
    rw [SimpleGraph.dist_comm,p.dist_end,hl]
  have hXZc : X Rg z ≤ stabilizer Rg c := (omegaCenter_le (Q Rg z)).trans
    (Q_le_stabilizer_of_dist_two Rg z c p.end_color hzdist)
  have hNK : X Rg z ⊓ Q Rg a ≤ normalizer (K : Set (FreeAmalgam Rg)) :=
    (le_inf ((inf_le_right.trans hZd).trans (Z_normalized Rg d))
      ((inf_le_left.trans hXZc).trans (Q_normalized Rg c))).trans inf_normalizer_le_normalizer_inf
  have hsplit := (restricted_omega_generation_or_control h e hz hk p hp K hKV htrap hNK).resolve_right
    (fun hh => hn hh.2)
  have hXZ : X Rg z = Z Rg z := omega_eq_seed_of_central_generation h z p.end_color hsplit
  have hnZ : ¬ Z Rg z ≤ normalizer ((K ⊔ Z Rg a : Subgroup (FreeAmalgam Rg)) : Set _) := by
    rwa [hXZ] at hn
  have hFN : F ≤ normalizer (K : Set (FreeAmalgam Rg)) := by
    simpa only [hXZ] using hNK
  let := (sourceGeometry h).Z_elementary (sourceDistance_pos h) d hd
  let : IsElementaryAbelian 2 K := IsElementaryAbelian.of_le inf_le_left
  let := (sourceGeometry h).Z_elementary (sourceDistance_pos h) z p.end_color
  let : IsElementaryAbelian 2 F := IsElementaryAbelian.of_le inf_le_left
  have hline := restricted_kernel_line h e hz hk u hR p hp K hKV htrap hFN hnZ
  have halign := restricted_kernel_alignment h e hz hk p hp K hKV htrap hFN hnZ
  have hDZz : ⁅Z Rg a,Z Rg z⁆ ≤ Z Rg z := by
    rw [commutator_comm]
    exact critical_seed_commutator_le h (CriticalPath.ofPair p.end_color (reverse_pair h e p))
  have hHZz : H ≤ Z Rg z := halign.trans (sup_le hDZz
    (inf_le_left.trans (DistanceEight.U_le_Z Rg z)))
  have hcore := borel_equal_thompson_core_commutator h e hz hk u hR p hp hd hat hdt heq
  have hHcore : H ≤ ⁅Z Rg d,Q Rg a⁆ := commutator_mono inf_le_left inf_le_right
  have hHZa : H ≤ Z Rg a := hHcore.trans (hcore.1.trans inf_le_left)
  have hHfix := hHcore.trans (commutator_eq_bot_iff_le_centralizer.mp hcore.2)
  have hHne : H ≠ ⊥ := by intro he; have hh : Nat.card H = 2 := hline.1; rw [he,card_bot] at hh; omega
  have hnon : ¬ H ≤ centralizer (stabilizer Rg d : Set (FreeAmalgam Rg)) := by
    by_cases htr : Z Rg d ≤ Q Rg c
    · have hK : K = Z Rg d := inf_eq_left.mpr htr
      rw [show H=⁅K,F⁆ from rfl,hK] at hHne ⊢
      exact whole_seed_edge_movement_not_central h e hz hk hd hdt F
        (inf_le_right.trans (Q_le_adjacent_h Rg ht hat)) hHne
    · obtain ⟨q,hqt,hverts⟩ := four_prepend_selected h hb p hd hat hdt htr
      have hqa : q.walk.getVert 2 = a := by
        simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using hverts 0 (by decide)
      intro hcent
      apply hHne
      apply le_bot_iff.mp
      intro v hv
      exact (borel_four_kernel_properties h e hz hk u hR p q hqa).2 v hv (hcent hv)
  refine ⟨hline.1,hHZa,hHZz,hHfix,hnon,?_⟩
  intro hmove
  exact hnZ (normalize_join_of_commutator K (Z Rg a) (Z Rg z)
    (le_normalizer_iff_commutator_le_left.mpr (critical_seed_commutator_le h p)) hmove)

include h e hz hk in
/-- Two equal-mover selections cannot both fail normalization. Their restricted
kernels act on the same reverse kernel; the combined movement bound identifies
the two nonzero lines, so the two generating movers fix that line. -/
theorem borel_four_equal_paired_normalization
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {a z d d' t t' y : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (r : CriticalPath Rg (sourceGeometry h) (p.walk.getVert 2) y)
    (hrz : r.walk.getVert 2 = z)
    (hgen : Q Rg (p.walk.getVert 1) ⊔ Z Rg y = stabilizer Rg (p.walk.getVert 2))
    (hp : (Q Rg z).relIndex (Z Rg a) < 4)
    (hd : color Rg d = false) (hd' : color Rg d' = false)
    (hat : Adjacent Rg a t) (hdt : Adjacent Rg d t)
    (hat' : Adjacent Rg a t') (hdt' : Adjacent Rg d' t')
    (heq : edgeOffenderJoin a t = edgeOffenderJoin d t)
    (heq' : edgeOffenderJoin a t' = edgeOffenderJoin d' t')
    (hpair : edgeOffenderJoin a t ⊔ edgeOffenderJoin a t' = stabilizer Rg a)
    (x : FreeAmalgam Rg) (hx : x ∈ stabilizer Rg a)
    (hxd : act Rg x (p.walk.getVert 2) = d) :
    (X Rg z ≤ normalizer
      (((Z Rg d ⊓ Q Rg (p.walk.getVert 2)) ⊔ Z Rg a : Subgroup (FreeAmalgam Rg)) : Set _)) ∨
    (X Rg z ≤ normalizer
      (((Z Rg d' ⊓ Q Rg (p.walk.getVert 2)) ⊔ Z Rg a : Subgroup (FreeAmalgam Rg)) : Set _)) := by
  by_contra! hn
  let c := p.walk.getVert 2
  let K := Z Rg d ⊓ Q Rg c
  let K' := Z Rg d' ⊓ Q Rg c
  let F := Z Rg z ⊓ Q Rg a
  let T := K ⊔ K'
  let H := ⁅T,F⁆
  have hfirst := equal_selected_failure h e hz hk u hR p hp hd hat hdt heq hn.1
  have hsecond := equal_selected_failure h e hz hk u hR p hp hd' hat' hdt' heq' hn.2
  have hKV : K ≤ V Rg a := inf_le_left.trans (terminal_neighbor_seed_radius hat hdt)
  have hK'V : K' ≤ V Rg a := inf_le_left.trans (terminal_neighbor_seed_radius hat' hdt')
  have hTQ : T ≤ Q Rg a := (sup_le hKV hK'V).trans
    ((sourceGeometry h).V_le_Q (distance_gt_two h e hz hk) a p.start_color)
  have hVG : V Rg a ≤ stabilizer Rg a := (sourceGeometry h).V_local a p.start_color (by
    rw [(sourceGeometry h).distance_constant _ p.start_color]
    exact distance_gt_two h e hz hk)
  have hHZ : H ≤ Z Rg a := by
    apply commutator_sup_le_of_relative_normal (stabilizer Rg a) K K' F (Z Rg a)
      (Z_normalized Rg a) (hKV.trans hVG) (hK'V.trans hVG) hfirst.2.1 hsecond.2.1
  have hb := borel_distance_eq_four h e hz hk u hR
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hcard : Nat.card H ≤ 2 := by
    rw [show H=⁅T,F⁆ from rfl,commutator_comm]
    apply borel_quadratic_reverse_kernel_card h e hz hk u hR p hp T
    · simpa only [hl,Nat.reduceSub] using (sup_le inf_le_right inf_le_right : T ≤ Q Rg c)
    · exact hTQ
    · change ⁅F,T⁆ ≤ Z Rg a
      rw [commutator_comm]
      exact hHZ
    · intro hh
      exact hfirst.2.2.2.2.2 ((commutator_mono le_sup_left le_rfl).trans hh)
  let := finite_Z Rg a
  let : Finite H := Finite.of_injective (inclusion hHZ) (inclusion_injective _)
  have hKHeq : ⁅K,F⁆ = H := eq_of_le_of_card_ge (commutator_mono le_sup_left le_rfl) (by
    rw [hfirst.1]
    exact hcard)
  have hK'Heq : ⁅K',F⁆ = H := eq_of_le_of_card_ge (commutator_mono le_sup_right le_rfl) (by
    rw [hsecond.1]
    exact hcard)
  have hHG : H ≤ centralizer (stabilizer Rg a : Set (FreeAmalgam Rg)) := by
    apply le_centralizer_iff.mpr
    rw [←hpair]
    exact sup_le (le_centralizer_iff.mp (hKHeq.symm ▸ hfirst.2.2.2.1))
      (le_centralizer_iff.mp (hK'Heq.symm ▸ hsecond.2.2.2.1))
  have hab : Adjacent Rg a (p.walk.getVert 1) := by
    apply (cosetGraph_adj Rg _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) (by omega)
  have htcol : color Rg (p.walk.getVert 1) = true := by
    have hh := adjacent_color_ne Rg hab
    rw [p.start_color] at hh
    exact Bool.eq_true_of_not_eq_false (Ne.symm hh)
  have hHedge : H ≤ Z Rg (p.walk.getVert 1) :=
    (le_inf hHZ hHG).trans (seed_center_le_incident_edge h p.start_color hab)
  have hHZz : H ≤ Z Rg z := hKHeq.symm ▸ hfirst.2.2.1
  have hyQ : Z Rg y ≤ Q Rg z := by
    apply Z_le_Q_of_dist_lt Rg _ ((sourceGeometry h).exists_critical _ r.end_color)
    have hrl : r.walk.length = 4 := r.length_eq_b.trans hb
    have hyz : (cosetGraph Rg).dist z y = 2 := by
      simpa only [hrz,hrl,Nat.reduceSub] using r.dist_end 2
    rw [SimpleGraph.dist_comm,hyz,(sourceGeometry h).distance_constant _ r.end_color]
    exact distance_gt_two h e hz hk
  have hHy : H ≤ centralizer (Z Rg y : Set (FreeAmalgam Rg)) := hHZz.trans
    ((commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q Rg z p.end_color)).trans
      (centralizer_le hyQ))
  have hHC : H ≤ centralizer (stabilizer Rg c : Set (FreeAmalgam Rg)) := by
    apply le_centralizer_iff.mpr
    rw [←hgen]
    exact sup_le (le_centralizer_iff.mp (hHedge.trans (terminal_edge_seed_central htcol)))
      (le_centralizer_iff.mp hHy)
  have hHD : H ≤ centralizer (stabilizer Rg d : Set (FreeAmalgam Rg)) := by
    have hh := (map_mono (f := (MulAut.conj x⁻¹).toMonoidHom) hHC).trans
      (map_centralizer_le_centralizer_image _ _)
    rw [terminal_fixed_map H (stabilizer Rg a) hHG ((stabilizer Rg a).inv_mem hx)] at hh
    change H ≤ centralizer ((stabilizer Rg c).map (MulAut.conj x⁻¹).toMonoidHom : Set _) at hh
    rwa [←stabilizer_act,hxd] at hh
  exact hfirst.2.2.2.2.1 (hKHeq.le.trans hHD)

include h e hz hk in
private theorem selected_normalized_path
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {a z d t : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (hd : color Rg d = false) (hat : Adjacent Rg a t) (hdt : Adjacent Rg d t)
    (hgen' : Q Rg t ⊔ Z Rg z = stabilizer Rg a)
    (x : FreeAmalgam Rg) (hx : x ∈ stabilizer Rg a)
    (hxd : act Rg x (p.walk.getVert 2) = d)
    (hnorm : X Rg z ≤ normalizer
      (((Z Rg d ⊓ Q Rg (p.walk.getVert 2)) ⊔ Z Rg a : Subgroup (FreeAmalgam Rg)) : Set _)) :
    ∃ q : CriticalPath Rg (sourceGeometry h) d (p.walk.getVert 2),
      q.walk.getVert 1 = t ∧ ∀ i ≤ 2, q.walk.getVert (i+2) = p.walk.getVert i := by
  have hb := borel_distance_eq_four h e hz hk u hR
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hescape : ¬ Z Rg d ≤ Q Rg (p.walk.getVert 2) := by
    intro htrap
    let N := Z Rg d ⊔ Z Rg a
    have hn : X Rg z ≤ normalizer (N : Set (FreeAmalgam Rg)) := by
      simpa only [inf_eq_left.mpr htrap] using hnorm
    have hZX : Z Rg z ≤ X Rg z := (sourceGeometry h).omega_bound z p.end_color (by
      rw [(sourceGeometry h).distance_constant _ p.end_color]; exact sourceDistance_pos h)
    have hTGv (v : Vertex Rg) (hvt : Adjacent Rg v t) : Q Rg t ≤ stabilizer Rg v :=
      fun _ hv => hv.2 _ (adjacent_symm Rg hvt)
    have hTN : Q Rg t ≤ normalizer (N : Set (FreeAmalgam Rg)) :=
      (le_inf ((hTGv d hdt).trans (Z_normalized Rg d))
        ((hTGv a hat).trans (Z_normalized Rg a))).trans
        (normalizer_inf_normalizer_le_normalizer_sup _ _)
    have hGN : stabilizer Rg a ≤ normalizer (N : Set (FreeAmalgam Rg)) := by
      rw [←hgen']
      exact sup_le hTN (hZX.trans hn)
    have hNV : N ≤ V Rg a := sup_le (terminal_neighbor_seed_radius hat hdt) (Z_le_VBall Rg a 2)
    have ht : color Rg t = true := by
      have hh := adjacent_color_ne Rg hat
      rw [p.start_color] at hh
      exact Bool.eq_true_of_not_eq_false (Ne.symm hh)
    have hZaQ : Z Rg a ≤ Q Rg a := ((sourceGeometry h).omega_bound a p.start_color (by
      rw [(sourceGeometry h).distance_constant _ p.start_color]; exact sourceDistance_pos h)).trans (omegaCenter_le _)
    have hZaN : Z Rg a ≤ normalizer (Z Rg d : Set (FreeAmalgam Rg)) :=
      ((hZaQ.trans (Q_le_adjacent_h Rg ht hat)).trans (hTGv d hdt)).trans (Z_normalized Rg d)
    let := finite_Z Rg a
    have hi : (Z Rg a).relIndex N ∣ 8 := by
      change (Z Rg a).relIndex (Z Rg d ⊔ Z Rg a) ∣ 8
      rw [relIndex_sup_of_normalizes (Z Rg d) (Z Rg a) hZaN]
      have hh := relIndex_dvd_of_le_left (Z Rg d) (adjacent_Z_le Rg p.start_color hat)
      rw [borel_full_seed_edge_index h e hz hk u hR hd hdt] at hh
      exact hh
    have hNB := terminal_residual_small_radius_le_slice h e hz hk p.start_color N
      hNV ((Ltilde_le_stabilizer a).trans hGN) hi
    have hUdB : U Rg d ≤ B Rg a ((sourceGeometry h).Z_normal _) :=
      (DistanceEight.U_le_Z Rg d).trans (le_sup_left.trans hNB)
    have hB : (B Rg a ((sourceGeometry h).Z_normal _)).map (MulAut.conj x⁻¹).toMonoidHom =
        B Rg a ((sourceGeometry h).Z_normal _) := mem_normalizer_iff_map_conj_eq.mp
      (Escape.Propagation.Rigidity.B_normalized (distance_gt_two h e hz hk) a p.start_color
        ((stabilizer Rg a).inv_mem hx))
    rw [←hxd,U_act,←hB] at hUdB
    exact (borel_critical_paths h e hz hk u hR p).2.2.2
      ((map_le_map_iff_of_injective (MulAut.conj x⁻¹).injective).mp hUdB)
  exact four_prepend_selected h hb p hd hat hdt hescape

include h e hz hk in
/-- Equal incident movers admit a normalized backward critical selection.
The paired residual selectors, both full covers and the original kernel are
retained. No backward criticality or image-size premise is needed. -/
theorem borel_four_equal_normalized_backward_selection
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {a z y : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (r : CriticalPath Rg (sourceGeometry h) (p.walk.getVert 2) y)
    (hrz : r.walk.getVert 2 = z)
    (hgen : Q Rg (p.walk.getVert 1) ⊔ Z Rg y = stabilizer Rg (p.walk.getVert 2))
    (hp : (Q Rg z).relIndex (Z Rg a) < 4)
    (heq : edgeOffenderJoin a (p.walk.getVert 1) =
      edgeOffenderJoin (p.walk.getVert 2) (p.walk.getVert 1)) :
    ∃ d t, ∃ x ∈ Ltilde Rg a,
      act Rg x (p.walk.getVert 2) = d ∧ act Rg x (p.walk.getVert 1) = t ∧
      Adjacent Rg a t ∧ Adjacent Rg d t ∧
      Q Rg t ⊔ Z Rg z = stabilizer Rg a ∧
      (Z Rg (p.walk.getVert 1) ⊓ centralizer (edgeOffenderJoin a t : Set (FreeAmalgam Rg)) ≤
        centralizer (stabilizer Rg a : Set (FreeAmalgam Rg))) ∧
      ∃ q : CriticalPath Rg (sourceGeometry h) d (p.walk.getVert 2),
        q.walk.getVert 1 = t ∧ (∀ i ≤ 2, q.walk.getVert (i+2) = p.walk.getVert i) ∧
        X Rg z ≤ normalizer
            (((Z Rg d ⊓ Q Rg (p.walk.getVert 2)) ⊔ Z Rg a :
              Subgroup (FreeAmalgam Rg)) : Set _) := by
  obtain ⟨t,hat,x,hx,k,hkL,hkt,_,hpair,hgen₀,hgen₁,hfix₀,hfix₁,_⟩ :=
    borel_small_residual_selectors h e hz hk u hR p hp
  let c := p.walk.getVert 2
  let b := p.walk.getVert 1
  have hb := borel_distance_eq_four h e hz hk u hR
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hab : Adjacent Rg a b := by
    apply (cosetGraph_adj Rg _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) (by omega)
  have hcb : Adjacent Rg c b := adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp
    (p.walk.adj_getVert_succ (i := 1) (by omega)))
  have hxG := Ltilde_le_stabilizer a hx
  have hkG := Ltilde_le_stabilizer a hkL
  have hxa : act Rg x a = a := hxG
  have hka : act Rg k a = a := hkG
  have hkc : color Rg (act Rg k c) = false := by rw [action_preserves_color]; exact r.start_color
  have hkxc : color Rg (act Rg x (act Rg k c)) = false := by rw [action_preserves_color]; exact hkc
  have hdt : Adjacent Rg (act Rg k c) t := by
    rw [←hkt]
    exact (adjacent_act_iff Rg k _ _).mpr hcb
  have hat' : Adjacent Rg a (act Rg x t) := by
    rw [←hxa]
    exact (adjacent_act_iff Rg x _ _).mpr hat
  have hdt' : Adjacent Rg (act Rg x (act Rg k c)) (act Rg x t) :=
    (adjacent_act_iff Rg x _ _).mpr hdt
  have hEq : edgeOffenderJoin a t = edgeOffenderJoin (act Rg k c) t := by
    have hh := congrArg (Subgroup.map (MulAut.conj k⁻¹).toMonoidHom) heq
    rw [←remaining_edge_join_act h e hz hk u (Or.inr hR) p.start_color hab k,
      ←remaining_edge_join_act h e hz hk u (Or.inr hR) r.start_color hcb k,hka,hkt] at hh
    exact hh
  have hEq' : edgeOffenderJoin a (act Rg x t) =
      edgeOffenderJoin (act Rg x (act Rg k c)) (act Rg x t) := by
    have hh := congrArg (Subgroup.map (MulAut.conj x⁻¹).toMonoidHom) hEq
    rw [←remaining_edge_join_act h e hz hk u (Or.inr hR) p.start_color hat x,
      ←remaining_edge_join_act h e hz hk u (Or.inr hR) hkc hdt x,hxa] at hh
    exact hh
  rcases borel_four_equal_paired_normalization h e hz hk u hR p r hrz hgen hp
    hkc hkxc hat hdt hat' hdt' hEq hEq' hpair k hkG rfl with hn | hn
  · obtain ⟨q,hqt,hover⟩ := selected_normalized_path h e hz hk u hR p hkc hat hdt hgen₀ k hkG rfl hn
    exact ⟨_,t,k,hkL,rfl,hkt,hat,hdt,hgen₀,hfix₀,q,hqt,hover,hn⟩
  · have hkxL : k*x ∈ Ltilde Rg a := (Ltilde Rg a).mul_mem hkL hx
    have hkxc' : act Rg (k*x) c = act Rg x (act Rg k c) := act_mul Rg k x c
    have hkxt : act Rg (k*x) b = act Rg x t := by rw [act_mul,hkt]
    obtain ⟨q,hqt,hover⟩ := selected_normalized_path h e hz hk u hR p hkxc hat' hdt' hgen₁
      (k*x) (Ltilde_le_stabilizer a hkxL) hkxc' hn
    exact ⟨_,_,k*x,hkxL,hkxc',hkxt,hat',hdt',hgen₁,hfix₁,q,hqt,hover,hn⟩

include h e hz hk in
/-- Compatible forward data now gives a normalized backward critical path
for both equal and distinct movers and every backward image. The initial
forward small image and same-path fixed-subgroup comparison remain explicit. -/
theorem borel_four_normalized_backward_selection
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {a z y : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (r : CriticalPath Rg (sourceGeometry h) (p.walk.getVert 2) y)
    (hrz : r.walk.getVert 2 = z)
    (hgen : Q Rg (p.walk.getVert 1) ⊔ Z Rg y = stabilizer Rg (p.walk.getVert 2))
    (hp : (Q Rg z).relIndex (Z Rg a) < 4)
    (hfixed : Z Rg (p.walk.getVert 3) ⊓ centralizer
        (edgeOffenderJoin (p.walk.getVert 2) (p.walk.getVert 1) : Set (FreeAmalgam Rg)) ≤
      centralizer (stabilizer Rg (p.walk.getVert 2) : Set (FreeAmalgam Rg))) :
    ∃ d t, ∃ x ∈ Ltilde Rg a,
      act Rg x (p.walk.getVert 2) = d ∧ act Rg x (p.walk.getVert 1) = t ∧
      Adjacent Rg a t ∧ Adjacent Rg d t ∧
      Q Rg t ⊔ Z Rg z = stabilizer Rg a ∧
      (Z Rg (p.walk.getVert 1) ⊓ centralizer (edgeOffenderJoin a t : Set (FreeAmalgam Rg)) ≤
        centralizer (stabilizer Rg a : Set (FreeAmalgam Rg))) ∧
      ∃ q : CriticalPath Rg (sourceGeometry h) d (p.walk.getVert 2),
        q.walk.getVert 1 = t ∧ (∀ i ≤ 2, q.walk.getVert (i+2) = p.walk.getVert i) ∧
        X Rg z ≤ normalizer
            (((Z Rg d ⊓ Q Rg (p.walk.getVert 2)) ⊔ Z Rg a :
              Subgroup (FreeAmalgam Rg)) : Set _) := by
  by_cases heq : edgeOffenderJoin a (p.walk.getVert 1) =
      edgeOffenderJoin (p.walk.getVert 2) (p.walk.getVert 1)
  · exact borel_four_equal_normalized_backward_selection h e hz hk u hR p r hrz hgen hp heq
  · exact borel_four_distinct_normalized_backward_selection h e hz hk u hR p r hrz hgen hp heq hfixed

end AlternatingSixReconstruction.Exceptional.OriginalSylow
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
