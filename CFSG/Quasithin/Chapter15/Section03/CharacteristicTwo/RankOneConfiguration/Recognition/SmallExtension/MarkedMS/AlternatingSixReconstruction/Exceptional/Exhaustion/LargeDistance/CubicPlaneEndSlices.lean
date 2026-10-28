module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneTerminal
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneComparison
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPredecessorSlice

/-!
# Selected end slices on the original cubic plane graph

A seed in the second predecessor core has endpoint commutator inside the
starting seed when its forward slice and the endpoint's predecessor slice
both have index at most two. A contrary commutator constructs a residual-
shifted critical path. Reversing that same path puts its predecessor at the
original base, so the forward slice supplies its small critical image.
The original full-cover alignment argument then excludes the resulting
nonzero fixed-kernel displacement. Only these two literal slices are used;
there is no uniform-slice or whole-radius-containment assumption.

At distance four, apply this control to every conjugate generator of the
original selected span P. If P lay in its midpoint core, normal generation
would put P in the starting Baumann subgroup, contradicting forward escape.
An abelian P would lie in that core, so P is nonabelian. The existing selected
span algebra supplies its derived line of order two, index two over its
common-core intersection, and transfer of the derived line to that intersection.
It also constructs a genuine critical pair in the midpoint orbit. Applying
the terminal two-slice exclusion to this pair makes the original reciprocal
slice strict, without assuming a midpoint conjugator for the initial path.

The whole-core and literal C.1.32 consumers use the same original projection,
retain both full covers and the nontrivial odd extension-kernel quotient E/Q,
and preserve the Borel branch. The two end-slice bounds, exact-four selection,
larger-distance exclusions and both final core exhaustions remain necessary.
In particular, the strict reciprocal slice is not itself a contradiction.
The internal imports reuse the existing cover comparison and residual
transporter without changing their public boundaries.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (5.8) and the kernel and terminal arguments of (5.12), printed
pp.919--920,924--927; Aschbacher--Smith C.1.31--32, printed pp.135--136.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open Theory.SpecificGroups.SymmetricSix Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open Representation.NormalElementaryQuotient
open scoped IsMulCommutative commutatorElement Pointwise
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "M" => (L ⊔ R : Subgroup G)
local notation "W₀" => (⁅centralOmega L R,L.subgroupOf M⁆ : Subgroup M)
local notation "Rg" => edge L R
local notation "π" => CubicAction.projection h e hz hk
local instance : IsElementaryAbelian 2 W₀ := IsElementaryAbelian.of_le (commutator_le_left _ _)

include h e hz hk in
private theorem plane_two_slices_residual_path
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    {z c t : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z)
    (hforward : (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex (U Rg c) ≤ 2)
    (hpre : (B Rg (p.walk.getVert (p.walk.length-2))
      ((sourceGeometry h).Z_normal _)).relIndex (U Rg z) ≤ 2)
    (hat : Adjacent Rg (alpha Rg) t) (hct : Adjacent Rg c t)
    (hbad : Z Rg c ≤ Q Rg (p.walk.getVert (p.walk.length-2)))
    (hne : ⁅Z Rg z ⊓ Q Rg (alpha Rg),Z Rg c⁆ ≠ ⊥)
    (k : FreeAmalgam Rg)
    (hkm : k ∈ Ltilde Rg (p.walk.getVert (p.walk.length-2)))
    (hkt : act Rg k (p.walk.getVert (p.walk.length-1)) = p.walk.getVert (p.walk.length-3)) :
    ∃ q : CriticalPath Rg (sourceGeometry h) c (act Rg k z),
      q.walk.getVert 1 = t ∧
      (∀ i ≤ p.walk.length-3, q.walk.getVert (i+2) = p.walk.getVert i) ∧
      Nat.card (⁅Z Rg z ⊓ Q Rg (alpha Rg),Z Rg c⁆ : Subgroup (FreeAmalgam Rg)) = 2 ∧
      ⁅Z Rg z ⊓ Q Rg (alpha Rg),Z Rg c⁆ = ⁅U Rg z,Z Rg (act Rg k⁻¹ c)⁆ ∧
      ⁅Z Rg z ⊓ Q Rg (alpha Rg),Z Rg c⁆ ≤
        centralizer (stabilizer Rg (p.walk.getVert (p.walk.length-2)) : Set (FreeAmalgam Rg)) ∧
      ¬ ⁅Z Rg z ⊓ Q Rg (alpha Rg),Z Rg c⁆ ≤
        centralizer (stabilizer Rg z : Set (FreeAmalgam Rg)) := by
  have hb := distance_gt_two h e hz hk
  have hcentralCore := plane_predecessor_slice_commutator_central h e hz hk u hR p hpre
  have htransport :
      ⁅Z Rg z ⊓ Q Rg (alpha Rg),Z Rg (act Rg k⁻¹ c)⁆ =
        ⁅Z Rg z ⊓ Q Rg (alpha Rg),Z Rg c⁆ := by
    rw [Z_act,inv_inv]
    exact plane_predecessor_slice_residual_transport h e hz hk u hR p hpre _ hbad k hkm
  have hescape : ¬ Z Rg c ≤ Q Rg (act Rg k z) := by
    intro hh
    have hm : Z Rg (act Rg k⁻¹ c) ≤ Q Rg z := by
      calc
        _ = (Z Rg c).map (MulAut.conj k).toMonoidHom := by rw [Z_act,inv_inv]
        _ ≤ (Q Rg (act Rg k z)).map (MulAut.conj k).toMonoidHom := map_mono hh
        _ = Q Rg (act Rg k⁻¹ (act Rg k z)) := by
          simpa only [inv_inv] using (Q_act Rg k⁻¹ (act Rg k z)).symm
        _ = Q Rg z := by rw [←act_mul,mul_inv_cancel,act_one]
    apply hne
    rw [←htransport]
    exact le_bot_iff.mp ((commutator_mono inf_le_left hm).trans_eq
      (Z_centralizes_Q Rg z p.end_color))
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb
  have hcfalse : color Rg c = false := by
    have h1 := adjacent_color_ne Rg hat
    have h2 := adjacent_color_ne Rg hct
    change false ≠ color Rg t at h1
    cases hc : color Rg c <;> cases ht : color Rg t <;> simp_all
  have hlast : Adjacent Rg (p.walk.getVert (p.walk.length-1)) z := by
    have hh := p.walk.adj_getVert_succ (i := p.walk.length-1) (by omega)
    rw [show p.walk.length-1+1=p.walk.length by omega,p.walk.getVert_length] at hh
    exact (cosetGraph_adj Rg _ _).mp hh
  have hend : (cosetGraph Rg).Adj (p.walk.getVert (p.walk.length-3)) (act Rg k z) := by
    rw [←hkt]
    exact (cosetGraph_adj Rg _ _).mpr
      ((adjacent_act_iff Rg k _ _).mpr hlast)
  let w₀ : (cosetGraph Rg).Walk c (alpha Rg) :=
    .cons ((cosetGraph_adj Rg _ _).mpr hct)
      (.cons ((cosetGraph_adj Rg _ _).mpr (adjacent_symm Rg hat)) .nil)
  let w₁ := (p.walk.take (p.walk.length-3)).concat hend
  let w := w₀.append w₁
  have hw₀ : w₀.length = 2 := rfl
  have hw : w.length = p.walk.length := by
    simp only [w,w₁,SimpleGraph.Walk.length_append,hw₀,SimpleGraph.Walk.length_concat,
      SimpleGraph.Walk.take_length,inf_eq_left.mpr (Nat.sub_le _ _)]
    omega
  have hmin := criticalDistance_le Rg c ((sourceGeometry h).exists_critical c hcfalse) hescape
  rw [(sourceGeometry h).distance_constant c hcfalse] at hmin
  have hdist : (cosetGraph Rg).dist c (act Rg k z) = sourceDistance h := by
    have hh := SimpleGraph.dist_le w
    rw [hw,p.length_eq_b] at hh
    exact le_antisymm hh hmin
  let q : CriticalPath Rg (sourceGeometry h) c (act Rg k z) :=
    ⟨hcfalse,w,hw.trans (p.length_eq_b.trans hdist.symm),by
      refine ⟨?_,hescape⟩
      rw [(sourceGeometry h).distance_constant c hcfalse]
      exact hdist⟩
  have hback : act Rg k⁻¹ (act Rg k z) = z := by
    rw [←act_mul,mul_inv_cancel,act_one]
  let qr : CriticalPath Rg (sourceGeometry h) (act Rg k z) c :=
    ⟨q.end_color,q.walk.reverse,
      by rw [SimpleGraph.Walk.length_reverse,q.shortest,SimpleGraph.dist_comm],
      critical_reverse Rg (sourceGeometry h) (sourceEdgeCentralizer h e)
      c q.start_color (by
        rw [(sourceGeometry h).distance_constant c q.start_color]
        exact sourceDistance_pos h) (act Rg k z) q.end_color q.critical⟩
  have hrex : Nonempty (CriticalPath Rg (sourceGeometry h) z (act Rg k⁻¹ c)) := by
    rw [←hback]
    exact ⟨qr.act k⁻¹⟩
  obtain ⟨r⟩ := hrex
  have hq2 : q.walk.getVert 2 = alpha Rg := by
    change (w₀.append w₁).getVert 2 = alpha Rg
    rw [SimpleGraph.Walk.getVert_append,hw₀,if_neg (by decide),Nat.sub_self,
      SimpleGraph.Walk.getVert_zero]
  have hqrpre : qr.walk.getVert (qr.walk.length-2) = alpha Rg := by
    change q.walk.reverse.getVert (q.walk.reverse.length-2) = alpha Rg
    rw [SimpleGraph.Walk.length_reverse,SimpleGraph.Walk.getVert_reverse,
      show q.walk.length-(q.walk.length-2)=2 by
        have hh : q.walk.length = sourceDistance h := q.length_eq_b
        omega,hq2]
  have hqrsmall := critical_predecessor_small_slice h e hz hk hb qr
    (by simpa only [hqrpre] using hforward)
  have hrs : (Q Rg (act Rg k⁻¹ c)).relIndex (Z Rg z) < 4 := by
    rw [←hback,Q_act,Z_act,relIndex_map_map_of_injective _ _ (MulAut.conj _).injective,
      hqrsmall.2.2]
    decide
  let H := ⁅Z Rg z ⊓ Q Rg (alpha Rg),Z Rg c⁆
  let D₀ := ⁅U Rg z,Z Rg (act Rg k⁻¹ c)⁆
  have hDcard : Nat.card D₀ = 2 := by
    dsimp only [D₀]
    rw [small_critical_moving_commutator_eq h e hz hk r hrs]
    exact small_critical_commutator_card h e hz hk r hrs
  let : Finite D₀ := Nat.finite_of_card_ne_zero (by rw [hDcard]; decide)
  have hkQ : (Q Rg (p.walk.getVert (p.walk.length-2))).map
      (MulAut.conj k).toMonoidHom = Q Rg (p.walk.getVert (p.walk.length-2)) :=
    mem_normalizer_iff_map_conj_eq.mp ((Q_normalized Rg _)
      (Ltilde_le_stabilizer _ hkm))
  have hDk : Z Rg (act Rg k⁻¹ c) ≤ Q Rg (p.walk.getVert (p.walk.length-2)) := by
    rw [Z_act,inv_inv]
    exact (map_mono hbad).trans_eq hkQ
  have hle : H ≤ D₀ := by
    dsimp only [H,D₀]
    rw [←htransport,(critical_kernel_predecessor_moving h e hz hb p).2.2 _ hDk]
    exact commutator_mono inf_le_left le_rfl
  let : Finite H := Finite.of_injective (inclusion hle) (inclusion_injective _)
  have hcard : Nat.card H = 2 := by
    have hlo := (one_lt_card_iff_ne_bot _).mpr hne
    have hhi := card_le_of_le hle
    rw [hDcard] at hhi
    change 1 < Nat.card H at hlo
    omega
  have heq : H = D₀ := eq_of_le_of_card_ge hle (by rw [hcard,hDcard])
  have hcentral : H ≤ centralizer (stabilizer Rg (p.walk.getVert (p.walk.length-2)) :
      Set (FreeAmalgam Rg)) :=
    (commutator_mono le_rfl hbad).trans hcentralCore.2.2
  have hnon : ¬ H ≤ centralizer (stabilizer Rg z : Set (FreeAmalgam Rg)) := by
    rw [heq]
    exact critical_moving_commutator_not_central h e hz hk r
  refine ⟨q,?_,?_,hcard,heq,hcentral,hnon⟩
  · change (w₀.append w₁).getVert 1 = t
    simp only [SimpleGraph.Walk.getVert_append,hw₀,show 1<2 from by decide,ite_true,
      w₀,SimpleGraph.Walk.getVert_cons_succ,SimpleGraph.Walk.getVert_zero]
  · intro i hi
    change (w₀.append w₁).getVert (i+2) = p.walk.getVert i
    rw [SimpleGraph.Walk.getVert_append,hw₀,if_neg (by omega),Nat.add_sub_cancel]
    change ((p.walk.take (p.walk.length-3)).concat hend).getVert i = p.walk.getVert i
    rw [SimpleGraph.Walk.concat_eq_append,SimpleGraph.Walk.getVert_append']
    rw [if_pos (by simpa only [SimpleGraph.Walk.take_length,
      inf_eq_left.mpr (Nat.sub_le _ _)] using hi),SimpleGraph.Walk.take_getVert,inf_eq_right.mpr hi]


include h e hz hk in
/-- Two literal slice bounds control a seed trapped in the predecessor core.
The residual-shifted critical path obtains its small image from the original
forward slice, so no global small-slice or trapped-radius premise is needed. -/
theorem plane_trapped_seed_endpoint_control
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    {z c t : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z)
    (hat : Adjacent Rg (alpha Rg) t) (hct : Adjacent Rg c t)
    (hforward : (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex (U Rg c) ≤ 2)
    (hpre : (B Rg (p.walk.getVert (p.walk.length-2))
      ((sourceGeometry h).Z_normal _)).relIndex (U Rg z) ≤ 2)
    (hbad : Z Rg c ≤ Q Rg (p.walk.getVert (p.walk.length-2))) :
    ⁅Z Rg c,Z Rg z⁆ ≤ Z Rg (alpha Rg) := by
  by_contra hescape
  have hb := distance_gt_two h e hz hk
  have hsmall : (Q Rg z).relIndex (Z Rg (alpha Rg)) < 4 := by
    rw [(critical_predecessor_small_slice h e hz hk hb p hpre).2.2]
    decide
  have hne : ⁅Z Rg z ⊓ Q Rg (alpha Rg),Z Rg c⁆ ≠ ⊥ := by
    intro he
    rw [commutator_comm] at he
    exact hescape (small_critical_predecessor_commutator h e hz hk hb p hsmall
      (Z Rg c) hbad (commutator_eq_bot_iff_le_centralizer.mp he))
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb
  have hcol : color Rg (p.walk.getVert (p.walk.length-2)) = false := by
    apply (p.vertex_color (Nat.sub_le _ _)).mpr
    have he := sourceDistance_even h
    rw [Nat.even_iff] at he ⊢
    have hh : p.walk.length = sourceDistance h := p.length_eq_b
    omega
  have hlast : Adjacent Rg z (p.walk.getVert (p.walk.length-1)) := by
    have hh := p.walk.adj_getVert_succ (i := p.walk.length-1) (by omega)
    rw [show p.walk.length-1+1=p.walk.length by omega,p.walk.getVert_length] at hh
    exact adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp hh)
  have hct' : Adjacent Rg (p.walk.getVert (p.walk.length-2))
      (p.walk.getVert (p.walk.length-1)) := by
    have hh := p.walk.adj_getVert_succ (i := p.walk.length-2) (by omega)
    rw [show p.walk.length-2+1=p.walk.length-1 by omega] at hh
    exact (cosetGraph_adj Rg _ _).mp hh
  have hcv : Adjacent Rg (p.walk.getVert (p.walk.length-2))
      (p.walk.getVert (p.walk.length-3)) := by
    have hh := p.walk.adj_getVert_succ (i := p.walk.length-3) (by omega)
    rw [show p.walk.length-3+1=p.walk.length-2 by omega] at hh
    exact adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp hh)
  obtain ⟨k,hkm,hkt⟩ := residual_neighbor_transporter (h := h) hcol hct' hcv
  obtain ⟨q,hq1,hqverts,hcard,hmove,hcentral,hnon⟩ :=
    plane_two_slices_residual_path h e hz hk u hR p hforward hpre hat hct hbad hne k hkm hkt
  let := h.relative_normal
  obtain ⟨hJcore,htrans,hfull,hfixed,hfixedJ⟩ :=
    plane_residual_fixed_displacements h e hz hk u hR p hpre hbad k hkm hmove
  have hca := CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction.neighbor_distance_le_two hat hct
  have hcontrol := plane_critical_kernel_control_escape h e hz hk u hR p hca hbad hescape
  obtain ⟨i,hi,hir,hiR,hiQ,hiU,hA,hP,hJ,hAr,hPr,hJr,hApi,hPpi,hJpi,hFi,hfix⟩ :=
    plane_predecessor_cover_chart h e hz hk u hR p (Z Rg c) hbad k hkm
  have hZ : (Z Rg c).map (MulAut.conj k).toMonoidHom = Z Rg (act Rg k⁻¹ c) := by
    rw [Z_act,inv_inv]
  rw [hZ] at hJ hJr hJpi
  obtain ⟨⟨τ,hτ,hτswap,hτeq⟩,hcrit⟩ :=
    plane_small_critical_chart_actor h e hz hk p hsmall i hi hiQ hiU hA hAr
  have hobs := plane_cover_commutator_obstruction h e hz hk k i hi hiU hA hP hJ
    hne hfixed hfixedJ hmove.symm hcontrol
  apply not_planeCoverObstruction h e hz hk u
  change SixCover.IsNaturalOrCore (coverAction h e hz hk) (MonoidHom.id S) ∧ _
  refine ⟨moved_subgroup_cover_model h e hz hk,τ,
    ((Z Rg c).comap i).map π,((Z Rg (act Rg k⁻¹ c)).comap i).map π,
    hApi hτ,hτswap,hPpi,hJpi,?_⟩
  simpa only [hτeq] using hobs

include h e hz hk in
/-- At distance four the two end slices force the selected span out of the
midpoint core. Its orbit generators satisfy the localized endpoint estimate;
normal generation would otherwise put the entire span in the Baumann slice. -/
private theorem plane_four_selected_span_not_le_midpoint_of_slices
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    (hb4 : sourceDistance h = 4)
    {z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z)
    (hforward : (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (p.walk.getVert 2)) ≤ 2)
    (hopposite : (B Rg (p.walk.getVert 2) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg z) ≤ 2) :
    ¬ localZSpan Rg (p.walk.getVert 2) (alpha Rg) ≤ Q Rg (p.walk.getVert 2) := by
  intro hPcore
  have hb := distance_gt_two h e hz hk
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb4
  let c := p.walk.getVert 2
  let t := p.walk.getVert 1
  let P := localZSpan Rg c (alpha Rg)
  have hPV : P ≤ V Rg (alpha Rg) := localZSpan_le_V Rg (by
    rw [SimpleGraph.dist_comm,p.dist_start (by omega)])
  have hat : Adjacent Rg (alpha Rg) t := by
    apply (cosetGraph_adj Rg _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) (by omega)
  have hct : Adjacent Rg c t := adjacent_symm Rg
    ((cosetGraph_adj Rg _ _).mp (p.walk.adj_getVert_succ (i := 1) (by omega)))
  have hpre : (B Rg (p.walk.getVert (p.walk.length-2))
      ((sourceGeometry h).Z_normal _)).relIndex (U Rg z) ≤ 2 := by
    simpa only [hl,Nat.reduceSub] using hopposite
  have hconj (g : stabilizer Rg (alpha Rg)) : Z Rg (act Rg g c) ≤ P := by
    rw [Z_act]
    exact (map_mono (Z_le_localZSpan Rg c (alpha Rg))).trans_eq
      (mem_normalizer_iff_map_conj_eq.mp (localZSpan_normalized Rg c (alpha Rg)
        ((stabilizer Rg (alpha Rg)).inv_mem g.property)))
  have hcomm : ⁅P,Z Rg z⁆ ≤ Z Rg (alpha Rg) := by
    dsimp only [P]
    rw [localZSpan_eq_conjugates]
    apply commutator_iSup_le_of_relative_normal (stabilizer Rg (alpha Rg))
      (Z Rg z) (Z Rg (alpha Rg)) _ (Z_normalized Rg _)
    · intro g
      rw [←Z_act]
      exact (hconj g).trans (hPV.trans ((sourceGeometry h).V_local _ rfl hb))
    · intro g
      rw [←Z_act]
      have hatg : Adjacent Rg (alpha Rg) (act Rg g t) := by
        simpa only [show act Rg g (alpha Rg) = alpha Rg from g.property] using
          (adjacent_act_iff Rg (g : FreeAmalgam Rg) _ _).mpr hat
      have hctg := (adjacent_act_iff Rg (g : FreeAmalgam Rg) c t).mpr hct
      have hBm : (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).map
          (MulAut.conj (g : FreeAmalgam Rg)⁻¹).toMonoidHom =
          B Rg (alpha Rg) ((sourceGeometry h).Z_normal _) :=
        mem_normalizer_iff_map_conj_eq.mp (Escape.Propagation.Rigidity.B_normalized
          hb (alpha Rg) rfl ((stabilizer Rg (alpha Rg)).inv_mem g.property))
      have hs : (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
          (U Rg (act Rg g c)) ≤ 2 := by
        rw [U_act,←hBm,relIndex_map_map_of_injective _ _ (MulAut.conj _).injective]
        exact hforward
      apply plane_trapped_seed_endpoint_control h e hz hk u hR p hatg hctg hs hpre
      simpa only [hl,Nat.reduceSub] using (hconj g).trans hPcore
  have hPB := normalized_radius_le_slice_of_critical_commutator h e hz hb p P hPV
    (localZSpan_normalized Rg _ _) hcomm
  exact (plane_critical_paths h e hz hk u hR p).2.2.2
    ((DistanceEight.U_le_Z Rg c).trans ((Z_le_localZSpan Rg _ _).trans hPB))

include h e hz hk in
/-- The two end slices themselves force nonabelianness of the original
selected span at distance four; no midpoint conjugator is assumed. -/
theorem plane_four_selected_span_nonabelian_of_slices
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    (hb4 : sourceDistance h = 4)
    {a' : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a')
    (hforward : (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (p.walk.getVert 2)) ≤ 2)
    (hopposite : (B Rg (p.walk.getVert 2) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg a') ≤ 2) :
    ⁅localZSpan Rg (p.walk.getVert 2) (alpha Rg),
      localZSpan Rg (p.walk.getVert 2) (alpha Rg)⁆ ≠ ⊥ := by
  intro he
  have hb := distance_gt_two h e hz hk
  let c := p.walk.getVert 2
  let t := p.walk.getVert 1
  let P := localZSpan Rg c (alpha Rg)
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb
  have hcol : color Rg c = false := (p.vertex_color (by omega)).mpr (by decide)
  have hat : Adjacent Rg (alpha Rg) t := by
    apply (cosetGraph_adj Rg _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) (by omega)
  have hct : Adjacent Rg c t := adjacent_symm Rg
    ((cosetGraph_adj Rg _ _).mp (p.walk.adj_getVert_succ (i := 1) (by omega)))
  have ht : color Rg t = true := by
    have hh := adjacent_color_ne Rg hat
    change false ≠ color Rg t at hh
    cases hh' : color Rg t <;> simp_all
  have hPQ := (selected_span_le_forward_kernel (h := h) hb p).trans inf_le_left
  have hPG : P ≤ stabilizer Rg c :=
    (hPQ.trans (Q_le_adjacent_h Rg ht hat)).trans
      (fun _ hx => hx.2 _ (adjacent_symm Rg hct))
  have hPc : P ≤ Q Rg c := two_subgroup_seed_centralizer_le_core h e hz hcol P
    ((Q_isPGroup Rg h.relative_radical.isPGroup h.relative_radical.twoCore_le
      (alpha Rg) rfl).to_le hPQ)
    (le_inf hPG ((commutator_eq_bot_iff_le_centralizer.mp he).trans
      (centralizer_le (Z_le_localZSpan Rg c (alpha Rg)))))
  exact plane_four_selected_span_not_le_midpoint_of_slices h e hz hk u hR hb4 p
    hforward hopposite hPc

include h e hz hk in
/-- On the same original span the two end slices supply index two, the
nontrivial derived line, its transfer to the common core, and an actual
midpoint-conjugate critical pair. The terminal theorem then makes the
reciprocal slice strict. -/
theorem plane_four_selected_configuration_of_slices
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    (hb4 : sourceDistance h = 4)
    {z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z)
    (hforward : (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (p.walk.getVert 2)) ≤ 2)
    (hopposite : (B Rg (p.walk.getVert 2) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg z) ≤ 2) :
    let P := localZSpan Rg (p.walk.getVert 2) (alpha Rg)
    let Y := P ⊓ Q Rg (p.walk.getVert 2)
    Y.relIndex P = 2 ∧ Nat.card (⁅P,P⁆ : Subgroup (FreeAmalgam Rg)) = 2 ∧
      ⁅Y,Y⁆ = ⁅P,P⁆ ∧
      2 < (B Rg (p.walk.getVert 2) ((sourceGeometry h).Z_normal _)).relIndex
        (U Rg (alpha Rg)) ∧
      ∃ x ∈ stabilizer Rg (alpha Rg),
        ∃ q : CriticalPath Rg (sourceGeometry h) (p.walk.getVert 2)
          (act Rg x (p.walk.getVert 2)),
          q.walk.getVert 1 = p.walk.getVert 1 ∧
          q.walk.getVert 2 = alpha Rg ∧
          q.walk.getVert 3 = act Rg x (p.walk.getVert 1) := by
  have hb := distance_gt_two h e hz hk
  have hn := plane_four_selected_span_nonabelian_of_slices h e hz hk u hR hb4 p
    hforward hopposite
  have hnot := plane_four_selected_span_not_le_midpoint_of_slices h e hz hk u hR hb4 p
    hforward hopposite
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb4
  have hsmall : (Q Rg z).relIndex (Z Rg (alpha Rg)) < 4 := by
    have hh := critical_predecessor_small_slice h e hz hk hb p
      (by simpa only [hl,Nat.reduceSub] using hopposite)
    rw [hh.2.2]
    decide
  let P := localZSpan Rg (p.walk.getVert 2) (alpha Rg)
  let Y := P ⊓ Q Rg (p.walk.getVert 2)
  have hPQ := (selected_span_le_forward_kernel (h := h) hb p).trans inf_le_left
  let := finite_stabilizer Rg (alpha Rg)
  let : Finite P := Finite.of_injective
    (inclusion (hPQ.trans (show Q Rg (alpha Rg) ≤ stabilizer Rg (alpha Rg) from fun _ hx => hx.1)))
    (inclusion_injective _)
  have hi : Y.relIndex P = 2 := by
    dsimp only [Y]
    rw [inf_relIndex_left]
    have hlo : 0 < (Q Rg (p.walk.getVert 2)).relIndex P := Nat.pos_of_ne_zero index_ne_zero_of_finite
    have hne : (Q Rg (p.walk.getVert 2)).relIndex P ≠ 1 := fun hh => hnot (relIndex_eq_one.mp hh)
    have hup := (selected_span_index_of_forward_slice h e hz hk hb p hforward).2
    change (Q Rg (p.walk.getVert 2)).relIndex P ≤ 2 at hup
    omega
  have hd := small_selected_span_derived h e hz hk hb p hsmall hforward hn
  have htransfer := selected_span_derived_transfer h e hz hk hb p hd.2.1 Y inf_le_left hi.le
  have hs := (plane_selected_reciprocal_slice_alternative h e hz hk u hR p hn).resolve_left
    (Nat.not_lt_of_ge hforward)
  exact ⟨hi,hd.2.1,htransfer,hs,(selected_span_conjugate_critical_path h hb p hn).2⟩

omit hk in
include h e hz in
/-- Whole-core application of the localized endpoint argument. The two end
slices now construct the selected span and conjugate critical pair, and the
terminal exclusion forces its reciprocal slice to be large. -/
theorem coreExhaustion_or_cubic_plane_selected_slices :
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
        (sourceDistance h = 4 → ∀ z (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z),
          (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
            (U Rg (p.walk.getVert 2)) ≤ 2 →
          (B Rg (p.walk.getVert 2) ((sourceGeometry h).Z_normal _)).relIndex (U Rg z) ≤ 2 →
          let P := localZSpan Rg (p.walk.getVert 2) (alpha Rg)
          let Y := P ⊓ Q Rg (p.walk.getVert 2)
          Y.relIndex P = 2 ∧ Nat.card (⁅P,P⁆ : Subgroup (FreeAmalgam Rg)) = 2 ∧
            ⁅Y,Y⁆ = ⁅P,P⁆ ∧
            2 < (B Rg (p.walk.getVert 2) ((sourceGeometry h).Z_normal _)).relIndex
              (U Rg (alpha Rg)) ∧
            ∃ x ∈ stabilizer Rg (alpha Rg),
              ∃ q : CriticalPath Rg (sourceGeometry h) (p.walk.getVert 2)
                (act Rg x (p.walk.getVert 2)),
                q.walk.getVert 1 = p.walk.getVert 1 ∧
                q.walk.getVert 2 = alpha Rg ∧
                q.walk.getVert 3 = act Rg x (p.walk.getVert 1))) := by
  rcases coreExhaustion_or_cubic_plane_terminal_slices h e hz with
    hex | ⟨hk,hs,hb,hcovers,u,hborel | ⟨hplane,_⟩⟩
  · exact Or.inl hex
  · exact Or.inr ⟨hk,hs,hb,hcovers,u,Or.inl hborel⟩
  · exact Or.inr ⟨hk,hs,hb,hcovers,u,Or.inr ⟨hplane,
      fun hb4 z p hf ho => plane_four_selected_configuration_of_slices h e hz hk u hplane hb4 p hf ho⟩⟩

omit hk in
include h e hz in
/-- Literal C.1.32 application retaining the full cubic kernel, both covers,
the Borel branch and the exact remaining two end-slice premises. -/
theorem rankTwo_or_cubic_plane_selected_slices :
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
        (sourceDistance h = 4 → ∀ z (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z),
          (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
            (U Rg (p.walk.getVert 2)) ≤ 2 →
          (B Rg (p.walk.getVert 2) ((sourceGeometry h).Z_normal _)).relIndex (U Rg z) ≤ 2 →
          let P := localZSpan Rg (p.walk.getVert 2) (alpha Rg)
          let Y := P ⊓ Q Rg (p.walk.getVert 2)
          Y.relIndex P = 2 ∧ Nat.card (⁅P,P⁆ : Subgroup (FreeAmalgam Rg)) = 2 ∧
            ⁅Y,Y⁆ = ⁅P,P⁆ ∧
            2 < (B Rg (p.walk.getVert 2) ((sourceGeometry h).Z_normal _)).relIndex
              (U Rg (alpha Rg)) ∧
            ∃ x ∈ stabilizer Rg (alpha Rg),
              ∃ q : CriticalPath Rg (sourceGeometry h) (p.walk.getVert 2)
                (act Rg x (p.walk.getVert 2)),
                q.walk.getVert 1 = p.walk.getVert 1 ∧
                q.walk.getVert 2 = alpha Rg ∧
                q.walk.getVert 3 = act Rg x (p.walk.getVert 1))) :=
  (coreExhaustion_or_cubic_plane_selected_slices h e hz).imp
    (rankTwo_of_exhaustion h e hz) id

end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
