module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicChiefComplete
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.DistanceFourLargeFixed
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.DistanceFourAdjustedSeed
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.DistanceFourSmallExclusion

/-!
# The full selected span in the original large Borel branch

A large critical commutator cannot be fixed by the entire first edge:
the normal-Borel displacement theorem would put that edge in its proper
index-two mover. Equal movers in the adjusted backward selection would
fix the commutator under the whole midpoint stabilizer, contradicting
this observation. Thus the actual selected movers are distinct.

The preceding large-image comparison now gives residual-fixed core
movement for the entire selected span, without a mover-comparison premise.
Transport by the same residual representative identifies its forward
span. This movement lies in midpoint omega, has order dividing eight,
and is moved by the full stabilizer. A small critical pair anywhere on
the original graph would upgrade residual fixedness to full fixedness,
so every critical image is large. The unique noncentral radius factor
then lies in the selected span modulo the full seed. Since that seed
centralizes the original two-core, the entire moving radius also has
residual-fixed core movement.

Both full moving covers, the adjusted actor, full central attachment,
strict slice, literal transporters and the odd cubic kernel are retained.
This is selected-span control: the whole-radius/core fixedness and the
remaining MS93 (5.12)(2) contradiction are still needed for exhaustion.
The private imports implement the same theorem family across modules.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (5.5)(c) and (5.12)(2), printed pp.916,925--926;
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
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "Rg" => edge L R
local notation "M" => (L ⊔ R : Subgroup G)
local notation "W" => (⁅centralOmega L R,L.subgroupOf M⁆ : Subgroup M)
local notation "π" => CubicAction.projection h e hz hk
local instance : IsElementaryAbelian 2 W := IsElementaryAbelian.of_le (commutator_le_left _ _)

include h e hz hk in
/-- The full first edge moves every large critical commutator. -/
theorem borel_four_large_critical_not_edge_fixed
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {c w : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) c w)
    (hp : 4 ≤ (Q Rg w).relIndex (Z Rg c)) :
    ¬ ⁅Z Rg c,Z Rg w⁆ ≤ centralizer
      (Q Rg (p.walk.getVert 1) : Set (FreeAmalgam Rg)) := by
  let a := p.walk.getVert 2
  let t := p.walk.getVert 1
  have hb := borel_distance_eq_four h e hz hk u hR
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hct : Adjacent Rg c t := by
    apply (cosetGraph_adj Rg _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using
      p.walk.adj_getVert_succ (i := 0) (by omega)
  have hat : Adjacent Rg a t := adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp
    (p.walk.adj_getVert_succ (i := 1) (by omega)))
  have ht : color Rg t = true := by
    have hh := adjacent_color_ne Rg hct
    rw [p.start_color] at hh
    exact Bool.eq_true_of_not_eq_false (Ne.symm hh)
  have hZwQa : Z Rg w ≤ Q Rg a := by
    apply Z_le_Q_of_dist_lt Rg w ((sourceGeometry h).exists_critical w p.end_color)
    rw [(sourceGeometry h).distance_constant _ p.end_color,SimpleGraph.dist_comm,p.dist_end,hl]
    exact distance_gt_two h e hz hk
  intro hf
  have hj := borel_edge_normal_large_movement h e hz hk u hR p.start_color hct
    (Z Rg w) (Q Rg t) (hZwQa.trans (Q_le_adjacent_h Rg ht hat)) le_rfl
    (Q Rg t).le_normalizer
    (by have hh := reverse_critical_image_four_le h e hz hk (sourceDistance_pos h) p hp; omega)
    (le_centralizer_iff.mp ((commutator_mono (DistanceEight.U_le_Z Rg c) le_rfl).trans hf))
  obtain ⟨J,_,hJ,_,_,hi,_⟩ := borel_edge_maximal_offenders h e hz hk u hR p.start_color hct
  have ho : J.relIndex (Q Rg t) = 1 := relIndex_eq_one.mpr (hj.trans hJ.le)
  omega

include h e hz hk in
/-- A generating actor fixing the large critical commutator forces distinct
incident movers on the same path. -/
theorem borel_four_large_selected_movers_distinct
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {c w : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) c w)
    (hp : 4 ≤ (Q Rg w).relIndex (Z Rg c))
    (A : Subgroup (FreeAmalgam Rg))
    (hgen : edgeOffenderJoin (p.walk.getVert 2) (p.walk.getVert 1) ⊔ A =
      stabilizer Rg (p.walk.getVert 2))
    (hfix : ⁅Z Rg c,Z Rg w⁆ ≤ centralizer (A : Set (FreeAmalgam Rg))) :
    edgeOffenderJoin c (p.walk.getVert 1) ≠
      edgeOffenderJoin (p.walk.getVert 2) (p.walk.getVert 1) := by
  let a := p.walk.getVert 2
  let t := p.walk.getVert 1
  let D := ⁅Z Rg c,Z Rg w⁆
  have hb := borel_distance_eq_four h e hz hk u hR
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hct : Adjacent Rg c t := by
    apply (cosetGraph_adj Rg _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using
      p.walk.adj_getVert_succ (i := 0) (by omega)
  have hat : Adjacent Rg a t := adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp
    (p.walk.adj_getVert_succ (i := 1) (by omega)))
  have hZwQa : Z Rg w ≤ Q Rg a := by
    apply Z_le_Q_of_dist_lt Rg w ((sourceGeometry h).exists_critical w p.end_color)
    rw [(sourceGeometry h).distance_constant _ p.end_color,SimpleGraph.dist_comm,p.dist_end,hl]
    exact distance_gt_two h e hz hk
  intro he
  obtain ⟨J,_,hJ,_,_,_,_,_,hquad⟩ :=
    borel_edge_maximal_offenders h e hz hk u hR p.start_color hct
  have hZwJ : Z Rg w ≤ J := hZwQa.trans
    ((borel_four_large_midpoint_core_le_mover h e hz hk u hR p hp).trans hJ.le)
  have hDJ : D ≤ centralizer (J : Set (FreeAmalgam Rg)) := by
    apply commutator_eq_bot_iff_le_centralizer.mp
    apply le_bot_iff.mp
    change ⁅⁅Z Rg c,Z Rg w⁆,J⁆ ≤ ⊥
    rw [critical_whole_commutator_eq_moving h e hz p (distance_gt_two h e hz hk)]
    exact (commutator_mono
      (commutator_mono le_rfl ((DistanceEight.U_le_Z Rg w).trans hZwJ)) le_rfl).trans_eq hquad
  have hDC : D ≤ centralizer (stabilizer Rg a : Set (FreeAmalgam Rg)) := by
    apply le_centralizer_iff.mp
    rw [←hgen]
    exact sup_le (le_centralizer_iff.mp (hDJ.trans (centralizer_le (he ▸ hJ.le))))
      (le_centralizer_iff.mp hfix)
  exact borel_four_large_critical_not_edge_fixed h e hz hk u hR p hp
    (hDC.trans (centralizer_le (show Q Rg t ≤ stabilizer Rg a from
      fun _ hx => hx.2 _ (adjacent_symm Rg hat))))

include h e hz hk in
/-- The actual adjusted backward selection has distinct movers and invariant
whole-span movement. Every preceding attachment and selection clause remains. -/
theorem borel_four_large_backward_span
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z)
    (hp : 4 ≤ (Q Rg z).relIndex (Z Rg (alpha Rg))) :
    ∃ A : Subgroup (FreeAmalgam Rg), A ≤ Z Rg z ∧ Z Rg (p.walk.getVert 3) ≤ A ∧
      A.relIndex (Z Rg z) ≤ 2 ∧
      ⁅Z Rg (alpha Rg),A⁆ = ⁅Z Rg (alpha Rg),Z Rg z⁆ ∧
      ∃ d t, ∃ x ∈ Ltilde Rg (alpha Rg),
        act Rg x (p.walk.getVert 2) = d ∧ act Rg x (p.walk.getVert 1) = t ∧
        Adjacent Rg (alpha Rg) t ∧ Adjacent Rg d t ∧
        edgeOffenderJoin (alpha Rg) t ⊔ A = stabilizer Rg (alpha Rg) ∧
        (Z Rg (p.walk.getVert 1) ⊓ centralizer
          (edgeOffenderJoin (alpha Rg) t : Set (FreeAmalgam Rg)) ≤
          centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg))) ∧
        Q Rg t ⊔ A = stabilizer Rg (alpha Rg) ∧
        Q Rg t ⊔ Z Rg z = stabilizer Rg (alpha Rg) ∧
        ∃ q : CriticalPath Rg (sourceGeometry h) d (p.walk.getVert 2),
          q.walk.getVert 1 = t ∧
          (∀ i ≤ 2, q.walk.getVert (i+2) = p.walk.getVert i) ∧
          ⁅Z Rg d ⊓ Q Rg (p.walk.getVert 2),A⁆ ≤ Z Rg (alpha Rg) ∧
          A ≤ normalizer
            (((Z Rg d ⊓ Q Rg (p.walk.getVert 2)) ⊔ Z Rg (alpha Rg) :
              Subgroup (FreeAmalgam Rg)) : Set _) ∧
          2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex (U Rg d) ∧
          4 ≤ (Q Rg (p.walk.getVert 2)).relIndex (Z Rg d) ∧
          Q Rg d ≤ edgeOffenderJoin (alpha Rg) t ∧
          ⁅Z Rg d,Z Rg (p.walk.getVert 2)⁆ ≤ fixedCore Rg (alpha Rg) ∧
          edgeOffenderJoin d t ≠ edgeOffenderJoin (alpha Rg) t ∧
          ⁅localZSpan Rg d (alpha Rg),Q Rg (alpha Rg)⁆ =
            ⁅Z Rg d,Z Rg (p.walk.getVert 2)⁆ ∧
          stabilizer Rg (alpha Rg) ≤ normalizer
            ((⁅Z Rg d,Z Rg (p.walk.getVert 2)⁆ : Subgroup (FreeAmalgam Rg)) : Set _) := by
  obtain ⟨A,hAZ,hattach,hi,hcomm,d,t,x,hx,hxd,hxt,hat,hdt,hJgen,hfix,hgen,hgenZ,
    q,hqt,hover,hbound,hnorm,hstrict,hlarge,hcore,hDF,hspan⟩ :=
    borel_four_large_backward_fixed h e hz hk u hR p hp
  have hqa : q.walk.getVert 2 = alpha Rg := by
    simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using hover 0 (by decide)
  have hne := borel_four_large_selected_movers_distinct h e hz hk u hR q hlarge A
    (by rwa [hqa,hqt])
    ((four_midpoint_line_centralizes_endpoint h e hz hk u hR q p rfl).trans (centralizer_le hAZ))
  rw [hqa,hqt] at hne
  exact ⟨A,hAZ,hattach,hi,hcomm,d,t,x,hx,hxd,hxt,hat,hdt,hJgen,hfix,hgen,hgenZ,
    q,hqt,hover,hbound,hnorm,hstrict,hlarge,hcore,hDF,hne,hspan hne⟩

include h e hz hk in
/-- The full forward selected span has small residual-fixed core movement,
which the full midpoint stabilizer does not fix. No mover-comparison premise
remains; the actual backward selection supplies it. -/
theorem borel_four_large_span_core_fixed
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z)
    (hp : 4 ≤ (Q Rg z).relIndex (Z Rg (alpha Rg))) :
    let H := ⁅localZSpan Rg (p.walk.getVert 2) (alpha Rg),Q Rg (alpha Rg)⁆
    H ≤ fixedCore Rg (alpha Rg) ∧ H ≤ X Rg (alpha Rg) ∧ Nat.card H ∣ 8 ∧
      ¬ H ≤ centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg)) := by
  obtain ⟨A,hAZ,hattach,hi,hcomm,d,t,x,hx,hxd,hxt,hat,hdt,hJgen,hfix,hgen,hgenZ,
    q,hqt,hover,hbound,hnorm,hstrict,hlarge,hcore,hDF,hne,hspan,hDN⟩ :=
    borel_four_large_backward_span h e hz hk u hR p hp
  let P := localZSpan Rg (p.walk.getVert 2) (alpha Rg)
  let D := ⁅Z Rg d,Z Rg (p.walk.getVert 2)⁆
  have hxG := Ltilde_le_stabilizer _ hx
  have hseed : Z Rg (p.walk.getVert 2) ≤ localZSpan Rg d (alpha Rg) := by
    have he : act Rg x⁻¹ d = p.walk.getVert 2 := by
      rw [←hxd,←act_mul,mul_inv_cancel,act_one]
    rw [←he,Z_act,inv_inv]
    exact (map_mono (Z_le_localZSpan Rg d (alpha Rg))).trans_eq
      (mem_normalizer_iff_map_conj_eq.mp (localZSpan_normalized Rg d (alpha Rg) hxG))
  have hP : P ≤ localZSpan Rg d (alpha Rg) := by
    change localZSpan Rg (p.walk.getVert 2) (alpha Rg) ≤ _
    conv_lhs => rw [localZSpan_eq_conjugates]
    apply iSup_le
    intro g
    exact (map_mono hseed).trans_eq (mem_normalizer_iff_map_conj_eq.mp
      (localZSpan_normalized Rg d (alpha Rg) ((stabilizer Rg (alpha Rg)).inv_mem g.property)))
  have hdP : Z Rg d ≤ P := by
    rw [←hxd,Z_act]
    exact (map_mono (Z_le_localZSpan Rg (p.walk.getVert 2) (alpha Rg))).trans_eq
      (mem_normalizer_iff_map_conj_eq.mp
        (localZSpan_normalized Rg _ _ ((stabilizer Rg (alpha Rg)).inv_mem hxG)))
  have hqa : q.walk.getVert 2 = alpha Rg := by
    simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using hover 0 (by decide)
  have hmove := borel_four_large_midpoint_movement h e hz hk u hR q hlarge
  rw [hqa,hqt] at hmove
  have hDQ : Z Rg (p.walk.getVert 2) ≤ Q Rg (alpha Rg) := by
    apply Z_le_Q_of_dist_lt Rg _ ((sourceGeometry h).exists_critical _ q.end_color)
    rw [SimpleGraph.dist_comm,p.dist_start (by
      have hl : p.walk.length = 4 := p.length_eq_b.trans (borel_distance_eq_four h e hz hk u hR)
      omega),(sourceGeometry h).distance_constant _ q.end_color]
    exact distance_gt_two h e hz hk
  have hH : ⁅P,Q Rg (alpha Rg)⁆ = D :=
    le_antisymm ((commutator_mono hP le_rfl).trans hspan.le)
      (commutator_mono hdP hDQ)
  change ⁅P,Q Rg (alpha Rg)⁆ ≤ _ ∧ _
  rw [hH]
  refine ⟨hDF,hmove.2.2.2.2.trans hmove.2.1,?_,?_⟩
  · have he := borel_four_large_distinct_movement_eq h e hz hk u hR q hlarge
      (by rwa [hqa,hqt]) (by rwa [hqa,hqt])
    rw [hqa] at he
    change Nat.card (⁅Z Rg d,Z Rg (p.walk.getVert 2)⁆ : Subgroup (FreeAmalgam Rg)) ∣ 8
    rw [←he]
    exact hmove.2.2.1
  · intro hc
    apply borel_four_large_critical_not_edge_fixed h e hz hk u hR q hlarge
    rw [hqt]
    exact hc.trans (centralizer_le (show Q Rg t ≤ stabilizer Rg (alpha Rg) from
      fun _ hx => hx.2 _ (adjacent_symm Rg hat)))

include h e hz hk in
/-- Every original critical image is large: a small pair would make the
residual-fixed movement of the large selected span fixed by the whole
stabilizer, contrary to the full-edge displacement calculation. -/
theorem borel_four_critical_images_large
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {c w : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) c w) :
    4 ≤ (Q Rg w).relIndex (Z Rg c) := by
  by_contra! hp
  obtain ⟨z,q,hq⟩ := borel_four_exists_large_critical h e hz hk u hR
  obtain ⟨hf,hX,_,hn⟩ := borel_four_large_span_core_fixed h e hz hk u hR q hq
  exact hn ((le_inf hX (hf.trans inf_le_right)).trans
    (small_pair_omega_residual_fixed_at h e hz hk p hp rfl))

include h e hz hk in
/-- The unique noncentral factor of the original radius is carried by the
selected span modulo the full starting seed. The strict slice excludes
the fixed alternative in MS93 (5.2)(i). -/
theorem borel_four_moving_radius_le_span_seed
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z) :
    Vcirc Rg (alpha Rg) ≤ localZSpan Rg (p.walk.getVert 2) (alpha Rg) ⊔ Z Rg (alpha Rg) := by
  let P := localZSpan Rg (p.walk.getVert 2) (alpha Rg)
  let Y := P.comap (embedM Rg)
  have hb := distance_gt_two h e hz hk
  have hp := borel_four_critical_images_large h e hz hk u hR p
  have hlen : 2 ≤ p.walk.length := by
    have hh := p.length_eq_b
    change p.walk.length = sourceDistance h at hh
    omega
  have hPV : P ≤ V Rg (alpha Rg) := localZSpan_le_V Rg (by
    rw [SimpleGraph.dist_comm,p.dist_start hlen])
  have hPG : P ≤ stabilizer Rg (alpha Rg) :=
    hPV.trans ((sourceGeometry h).V_local _ rfl hb)
  have hPN := localZSpan_normalized Rg (p.walk.getVert 2) (alpha Rg)
  have hYm : Y.map (embedM Rg) = P :=
    map_comap_eq_self (hPG.trans_eq (stabilizer_m_base Rg))
  let : Y.Normal := ⟨by
    intro y hy g
    change embedM Rg (g*y*g⁻¹) ∈ P
    rw [map_mul,map_mul,map_inv]
    have hg : embedM Rg g ∈ stabilizer Rg (alpha Rg) := by
      rw [show alpha Rg = mVertex Rg 1 from rfl,stabilizer_m_base]
      exact ⟨g,rfl⟩
    exact (mem_normalizer_iff.mp (hPN hg) (embedM Rg y)).mp hy⟩
  have hYV : Y ≤ radiusPreimage L R := comap_mono hPV
  have hLm : (L.subgroupOf M).map (embedM Rg) = Ltilde Rg (alpha Rg) := by
    rw [Ltilde_alpha,h.relative_residual]
  have hZm : (radiusSeed L R).map (embedM Rg) = Z Rg (alpha Rg) :=
    map_comap_eq_self ((Z_le_stabilizer Rg _).trans_eq (stabilizer_m_base Rg))
  rcases critical_radius_normal_subgroup_dichotomy h e hz hk hb p hp Y hYV with hf | hm
  · have hf' := map_mono (f := embedM Rg) hf
    rw [map_commutator,hYm,hLm,hZm] at hf'
    have hPB : P ≤ B Rg (alpha Rg) ((sourceGeometry h).Z_normal _) := by
      intro v hv
      apply (mem_B_iff Rg (alpha Rg) _ ((sourceGeometry h).V_local _ rfl hb) v).mpr
      refine ⟨hPV hv,?_⟩
      intro l hl
      rw [commutator_comm] at hf'
      exact hf' (commutator_mem_commutator hl hv)
    have hUB := (DistanceEight.U_le_Z Rg (p.walk.getVert 2)).trans
      ((Z_le_localZSpan Rg _ _).trans hPB)
    have hi := large_remaining_four_forward_slice_strict_at h e hz hk
      (borel_distance_eq_four h e hz hk u hR) u (Or.inr hR) p hp
    rw [relIndex_eq_one.mpr hUB] at hi
    omega
  · have hm' := map_mono (f := embedM Rg) hm
    rw [map_commutator,radius_comap_map (h := h) hb,hLm,Subgroup.map_sup,hYm,hZm] at hm'
    exact hm'

include h e hz hk in
/-- The whole moving radius now has residual-fixed core movement. The full
seed in the preceding covering equality centralizes the two-core, so it
adds no movement. -/
theorem borel_four_moving_radius_core_fixed
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z) :
    ⁅Vcirc Rg (alpha Rg),Q Rg (alpha Rg)⁆ ≤ fixedCore Rg (alpha Rg) := by
  have hm := borel_four_moving_radius_le_span_seed h e hz hk u hR p
  have hp := borel_four_critical_images_large h e hz hk u hR p
  have hfixed := (borel_four_large_span_core_fixed h e hz hk u hR p hp).1
  have hlen : 2 ≤ p.walk.length := by
    have hh := p.length_eq_b
    have hb := distance_gt_two h e hz hk
    change p.walk.length = sourceDistance h at hh
    omega
  have hPG := (localZSpan_le_V Rg (by rw [SimpleGraph.dist_comm,p.dist_start hlen])).trans
    ((sourceGeometry h).V_local _ rfl (distance_gt_two h e hz hk))
  apply (commutator_mono hm le_rfl).trans
  exact commutator_sup_le_of_relative_normal (stabilizer Rg (alpha Rg)) _ _ _ _
    (fixedCore_normalized Rg (alpha Rg)) hPG (Z_le_stabilizer Rg _) hfixed
    ((Z_centralizes_Q Rg (alpha Rg) rfl).le.trans bot_le)

end AlternatingSixReconstruction.Exceptional.OriginalSylow
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
