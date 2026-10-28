module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneRadiusCoreFixed
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicTerminal
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicForwardKernel

/-!
# Reciprocal moving spans on the original cubic plane

The chief-factor dichotomy and forward escape place the moving radius in
the selected span joined with the starting seed. The actual large backward
path gives the same containment at the original midpoint. All groups and
paths remain in the original cubic graph, retaining the full kernel E/Q.

Source: Meierfrankenfeld--Stellmacher (1993), (5.12)(2), pp.925--926.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open Theory.SpecificGroups.SymmetricSix Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
open scoped IsMulCommutative commutatorElement Pointwise
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "M" => (L ⊔ R : Subgroup G)
local notation "Rg" => edge L R
local notation "π" => CubicAction.projection h e hz hk

include h e hz hk in
/-- A large distance-four path makes its selected span carry the entire
moving radius modulo the original starting seed. -/
theorem plane_four_large_moving_radius_le_selected_span
    (hb : sourceDistance h = 4)
    {z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z)
    (hlarge : 4 ≤ (Q Rg z).relIndex (Z Rg (alpha Rg))) :
    Vcirc Rg (alpha Rg) ≤
      localZSpan Rg (p.walk.getVert 2) (alpha Rg) ⊔ Z Rg (alpha Rg) := by
  let P := localZSpan Rg (p.walk.getVert 2) (alpha Rg)
  let Y := P.comap (embedM Rg)
  have hb2 : 2 < sourceDistance h := by omega
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hPV : P ≤ V Rg (alpha Rg) := localZSpan_le_V Rg (by
    rw [SimpleGraph.dist_comm,p.dist_start (by omega)])
  have hPG : P ≤ stabilizer Rg (alpha Rg) :=
    hPV.trans ((sourceGeometry h).V_local _ rfl hb2)
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
  have hLm : (L.subgroupOf M).map (embedM Rg) = Ltilde Rg (alpha Rg) := by
    rw [Ltilde_alpha,h.relative_residual]
  have hZm : (radiusSeed L R).map (embedM Rg) = Z Rg (alpha Rg) :=
    map_comap_eq_self ((Z_le_stabilizer Rg _).trans_eq (stabilizer_m_base Rg))
  rcases critical_radius_normal_subgroup_dichotomy h e hz hk hb2 p hlarge Y
      (comap_mono hPV) with hf | hm
  · have hf' := map_mono (f := embedM Rg) hf
    rw [map_commutator,hYm,hLm,hZm] at hf'
    have hPB : P ≤ B Rg (alpha Rg) ((sourceGeometry h).Z_normal _) := by
      intro v hv
      apply (mem_B_iff Rg (alpha Rg) _ ((sourceGeometry h).V_local _ rfl hb2) v).mpr
      refine ⟨hPV hv,?_⟩
      intro l hl
      rw [commutator_comm] at hf'
      exact hf' (commutator_mem_commutator hl hv)
    exact (large_critical_four_forward_eligible h e hz hk hb p hlarge
      ((DistanceEight.U_le_Z Rg _).trans ((Z_le_localZSpan Rg _ _).trans hPB))).elim
  · have hm' := map_mono (f := embedM Rg) hm
    rw [map_commutator,radius_comap_map (h := h) hb2,hLm,Subgroup.map_sup,hYm,hZm] at hm'
    exact hm'

include h e hz hk in
/-- The selected-span containment transports to every original component vertex. -/
theorem plane_four_large_moving_radius_le_selected_span_at
    (hb : sourceDistance h = 4)
    {a z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (hlarge : 4 ≤ (Q Rg z).relIndex (Z Rg a)) :
    Vcirc Rg a ≤ localZSpan Rg (p.walk.getVert 2) a ⊔ Z Rg a := by
  obtain ⟨g,hg⟩ := exists_mVertex_of_color Rg p.start_color
  have hbase : act Rg g⁻¹ a = alpha Rg := by
    rw [hg,act_mVertex,mul_inv_cancel]
    rfl
  have base := plane_four_large_moving_radius_le_selected_span h e hz hk hb
    (z := act Rg g⁻¹ z)
  rw [←hbase] at base
  have hlarge₀ : 4 ≤ (Q Rg (act Rg g⁻¹ z)).relIndex (Z Rg (act Rg g⁻¹ a)) := by
    rw [Q_act,Z_act,relIndex_map_map_of_injective _ _ (MulAut.conj _).injective]
    exact hlarge
  have hm := base (p.act g⁻¹) hlarge₀
  simp only [CriticalPath.act,actWalk_getVert] at hm
  rw [Vcirc_act,LocalCommutator.CriticalCase.localZSpan_act,Z_act,←Subgroup.map_sup] at hm
  exact (map_le_map_iff_of_injective (MulAut.conj _).injective).mp hm

include h e hz hk in
/-- Both actual reciprocal spans cover their moving radii modulo their seeds.
The midpoint uses the reversal of the same large generating backward path. -/
theorem plane_four_large_reciprocal_moving_radius_span_cover
    (hb : sourceDistance h = 4) (u : S)
    (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    {z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z)
    (hlarge : 4 ≤ (Q Rg z).relIndex (Z Rg (alpha Rg))) :
    Vcirc Rg (alpha Rg) ≤
      localZSpan Rg (p.walk.getVert 2) (alpha Rg) ⊔ Z Rg (alpha Rg) ∧
    Vcirc Rg (p.walk.getVert 2) ≤
      localZSpan Rg (alpha Rg) (p.walk.getVert 2) ⊔ Z Rg (p.walk.getVert 2) := by
  refine ⟨plane_four_large_moving_radius_le_selected_span h e hz hk hb p hlarge,?_⟩
  obtain ⟨q,hback,_⟩ := plane_four_large_backward_configuration h e hz hk hb u hR p hlarge
  let qr : CriticalPath Rg (sourceGeometry h)
      (p.walk.getVert (p.walk.length-2)) q.start :=
    ⟨q.path.end_color,q.path.walk.reverse,
      by rw [SimpleGraph.Walk.length_reverse,q.path.shortest,SimpleGraph.dist_comm],
      critical_reverse Rg (sourceGeometry h) (sourceEdgeCentralizer h e)
        _ q.path.start_color (by
          rw [(sourceGeometry h).distance_constant _ q.path.start_color]
          exact sourceDistance_pos h) _ q.path.end_color q.path.critical⟩
  have hm := plane_four_large_moving_radius_le_selected_span_at h e hz hk hb qr
    (reverse_critical_image_four_le h e hz hk (sourceDistance_pos h) q.path hback)
  have hq2 : q.path.walk.getVert 2 = alpha Rg := by
    simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using
      q.overlap 0 (Nat.zero_le _)
  have hql : q.path.walk.length = 4 := q.path.length_eq_b.trans hb
  have hmiddle : qr.walk.getVert 2 = alpha Rg := by
    change q.path.walk.reverse.getVert 2 = _
    rw [SimpleGraph.Walk.getVert_reverse,hql]
    exact hq2
  rw [hmiddle] at hm
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  simpa only [hl,Nat.reduceSub] using hm

include h e hz hk in
private theorem cover_small_commutator_image (A : Subgroup M)
    (hcard : Nat.card (⁅initialMoved L R,A⁆ : Subgroup M) ≤ 2) :
    Nat.card (A.map π) ≤ 2 := by
  let W := initialMoved L R
  let := h.relative_normal
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.of_le (commutator_le_left _ _)
  let : IsElementaryAbelian 2 (⁅W,A⁆ : Subgroup M) :=
    IsElementaryAbelian.of_le (commutator_le_left _ _)
  let D₀ := subspaceCommutator (coverAction h e hz hk) ⊤ (A.map π)
  have hDcard : Nat.card D₀ ≤ 2 := by
    have he := Nat.card_congr (NormalElementaryQuotient.movedEquiv W π
      (CubicEven.projection_surjective h e hz hk)
      (CubicAction.moved_projection_kernel h e hz hk) A).toEquiv
    change Nat.card (⁅W,A⁆ : Subgroup M) = Nat.card D₀ at he
    rwa [←he]
  have hDdim : Module.finrank (ZMod 2) D₀ ≤ 1 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod] at hDcard
    exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hDcard
  have hm : D₀.map (coverMap h e hz hk) =
      subspaceCommutator (naturalRepresentation (Fin 6)) ⊤ (A.map π) := by
    have hh := subspaceCommutator_map_embedding (naturalRepresentation (Fin 6))
      (coverAction h e hz hk) (MonoidHom.id (Equiv.Perm (Fin 6))) (coverMap h e hz hk)
      (fun g v => (coverMap_equivariant h e hz hk g v).symm) (A.map π) ⊤
    rw [Submodule.map_top,LinearMap.range_eq_top.mpr (coverMap_surjective h e hz hk),
      Subgroup.map_id] at hh
    exact hh.symm
  have hnat : fixedCodim (naturalRepresentation (Fin 6)) (A.map π) ≤ 1 := by
    rw [←Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalPairing.moved_finrank_eq_fixedCodim,←hm]
    exact (Submodule.finrank_map_le (coverMap h e hz hk) D₀).trans hDdim
  by_cases he : A.map π = ⊥
  · rw [he,card_bot]; decide
  · obtain ⟨t,_,ht,he⟩ :=
      Theory.SpecificGroups.SymmetricSix.BinaryFlags.PointCoreTranspositionFixed.small_image_eq_zpowers
        (A.map π) he hnat
    rw [he,Nat.card_zpowers,ht.orderOf]

include h e hz hk in
/-- A critical commutator of order at most two forces both original
critical images to have order two, including the central cubic kernel. -/
theorem critical_indices_two_of_commutator_card
    {a z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (hcard : Nat.card (⁅Z Rg a,Z Rg z⁆ : Subgroup (FreeAmalgam Rg)) ≤ 2) :
    (Q Rg z).relIndex (Z Rg a) = 2 ∧ (Q Rg a).relIndex (Z Rg z) = 2 := by
  obtain ⟨i,hi,hir,hiQ,_hiE,hiU,_hiC⟩ := graph_cover h e hz hk z p.end_color
  have hA : Z Rg a ≤ i.range := by
    rw [hir]
    exact Z_le_stabilizer_of_dist_le a _ p.critical.1.le
  let A := (Z Rg a).comap i
  have hmA : A.map i = Z Rg a := map_comap_eq_self hA
  let := finite_Z Rg a
  let : Finite (⁅Z Rg a,Z Rg z⁆ : Subgroup (FreeAmalgam Rg)) :=
    Finite.of_injective (inclusion (le_normalizer_iff_commutator_le_left.mp
      ((critical_Z_le_stabilizer Rg (sourceGeometry h) a p.start_color
        (by rw [(sourceGeometry h).distance_constant _ p.start_color];
            exact sourceDistance_pos h) p.critical).trans (Z_normalized Rg a))))
      (inclusion_injective _)
  have hcomm : ⁅U Rg z,Z Rg a⁆ ≤ ⁅Z Rg a,Z Rg z⁆ := by
    rw [commutator_comm (Z Rg a)]
    exact commutator_mono (DistanceEight.U_le_Z Rg z) le_rfl
  have hsmall : Nat.card (⁅initialMoved L R,A⁆ : Subgroup M) ≤ 2 := by
    rw [←card_map_of_injective hi,map_commutator,hiU,hmA]
    exact (card_le_of_le hcomm).trans hcard
  have hidx := cover_small_commutator_image h e hz hk A hsmall
  let := (sourceGeometry h).Z_elementary (sourceDistance_pos h) a p.start_color
  rw [CubicAction.permutation_image_card_of_two h e hz hk A
    ((IsElementaryAbelian.isPGroup 2 (Z Rg a)).comap_of_injective i hi),
    ←relIndex_map_map_of_injective _ _ hi,hiQ,hmA] at hidx
  exact small_critical_indices h e hz hk p (by omega)

include h e hz hk in
/-- The actual large backward pair lies in the original selected span,
whose derived subgroup therefore has order greater than two. -/
theorem plane_four_large_selected_derived_gt_two
    (hb : sourceDistance h = 4) (u : S)
    (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    {z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z)
    (hlarge : 4 ≤ (Q Rg z).relIndex (Z Rg (alpha Rg))) :
    2 < Nat.card (⁅localZSpan Rg (p.walk.getVert 2) (alpha Rg),
      localZSpan Rg (p.walk.getVert 2) (alpha Rg)⁆ : Subgroup (FreeAmalgam Rg)) := by
  obtain ⟨q,hback,_⟩ := plane_four_large_backward_configuration h e hz hk hb u hR p hlarge
  let P := localZSpan Rg (p.walk.getVert 2) (alpha Rg)
  have hb2 : 2 < sourceDistance h := by omega
  have hZc : Z Rg q.start ≤ P := by
    rw [←q.start_eq,Z_act]
    exact (map_mono (Z_le_localZSpan Rg _ _)).trans_eq
      (mem_normalizer_iff_map_conj_eq.mp
        (localZSpan_normalized Rg _ _ ((stabilizer Rg (alpha Rg)).inv_mem q.transporter_mem)))
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hPG : P ≤ stabilizer Rg (alpha Rg) :=
    (localZSpan_le_V Rg (by rw [SimpleGraph.dist_comm,p.dist_start (by omega)])).trans
      ((sourceGeometry h).V_local _ rfl hb2)
  let := finite_stabilizer Rg (alpha Rg)
  let : Finite P := Finite.of_injective (inclusion hPG) (inclusion_injective _)
  let : Finite (⁅P,P⁆ : Subgroup (FreeAmalgam Rg)) :=
    Finite.of_injective (inclusion (Subgroup.commutator_le_self P)) (inclusion_injective _)
  by_contra! hsmall
  have hcsmall : Nat.card (⁅Z Rg q.start,Z Rg (p.walk.getVert (p.walk.length-2))⁆ :
      Subgroup (FreeAmalgam Rg)) ≤ 2 :=
    (card_le_of_le (commutator_mono hZc (by
      simpa only [hl,Nat.reduceSub] using Z_le_localZSpan Rg (p.walk.getVert 2) (alpha Rg)))).trans hsmall
  have htwo := (critical_indices_two_of_commutator_card h e hz hk q.path hcsmall).1
  omega

include h e hz hk in
/-- Residual fixedness moves the selected derived subgroup into the
derived moving radius, retaining its strict order bound. -/
theorem plane_four_large_moving_derived_gt_two
    (hb : sourceDistance h = 4) (u : S)
    (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    {z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z)
    (hlarge : 4 ≤ (Q Rg z).relIndex (Z Rg (alpha Rg))) :
    2 < Nat.card (⁅Vcirc Rg (alpha Rg),Vcirc Rg (alpha Rg)⁆ :
      Subgroup (FreeAmalgam Rg)) := by
  have hb2 : 2 < sourceDistance h := by omega
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hPV : localZSpan Rg (p.walk.getVert 2) (alpha Rg) ≤ V Rg (alpha Rg) :=
    localZSpan_le_V Rg (by rw [SimpleGraph.dist_comm,p.dist_start (by omega)])
  have hPQ := hPV.trans (V_le_Q Rg (geometry := sourceGeometry h) rfl hb2)
  have hfixed := plane_four_large_radius_core_fixed h e hz hk hb u hR p hlarge
  have hPP := ((commutator_mono hPV hPQ).trans hfixed).trans inf_le_right
  have he := selected_span_derived_eq_moved h hb2 p hPP
  have hP₀V : forwardMovedSpan Rg (p.walk.getVert 2) ≤ Vcirc Rg (alpha Rg) :=
    commutator_mono hPV le_rfl
  have hmV : Vcirc Rg (alpha Rg) ≤ V Rg (alpha Rg) :=
    le_normalizer_iff_commutator_le_left.mp ((Ltilde_le_stabilizer _).trans (V_normalized _))
  let := finite_stabilizer Rg (alpha Rg)
  let : Finite (Vcirc Rg (alpha Rg)) := Finite.of_injective
    (inclusion (hmV.trans ((sourceGeometry h).V_local _ rfl hb2))) (inclusion_injective _)
  let : Finite (⁅Vcirc Rg (alpha Rg),Vcirc Rg (alpha Rg)⁆ : Subgroup (FreeAmalgam Rg)) :=
    Finite.of_injective (inclusion (Subgroup.commutator_le_self _)) (inclusion_injective _)
  have hbig := plane_four_large_selected_derived_gt_two h e hz hk hb u hR p hlarge
  rw [he] at hbig
  exact hbig.trans_le (card_le_of_le (commutator_mono hP₀V hP₀V))

include h e hz hk in
/-- The strict derived moving-radius bound at any original component vertex. -/
theorem plane_four_large_moving_derived_gt_two_at
    (hb : sourceDistance h = 4) (u : S)
    (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    {a z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (hlarge : 4 ≤ (Q Rg z).relIndex (Z Rg a)) :
    2 < Nat.card (⁅Vcirc Rg a,Vcirc Rg a⁆ : Subgroup (FreeAmalgam Rg)) := by
  obtain ⟨g,hg⟩ := exists_mVertex_of_color Rg p.start_color
  have hbase : act Rg g⁻¹ a = alpha Rg := by
    rw [hg,act_mVertex,mul_inv_cancel]
    rfl
  have base := plane_four_large_moving_derived_gt_two h e hz hk hb u hR
    (z := act Rg g⁻¹ z)
  rw [←hbase] at base
  have hlarge₀ : 4 ≤ (Q Rg (act Rg g⁻¹ z)).relIndex (Z Rg (act Rg g⁻¹ a)) := by
    rw [Q_act,Z_act,relIndex_map_map_of_injective _ _ (MulAut.conj _).injective]
    exact hlarge
  have hm := base (p.act g⁻¹) hlarge₀
  rw [Vcirc_act,←map_commutator,card_map_of_injective (MulAut.conj _).injective] at hm
  exact hm

include h e hz hk in
/-- Both actual reciprocal moving radii have derived subgroup of order
greater than two, using the same large generating backward path. -/
theorem plane_four_large_reciprocal_moving_derived_gt_two
    (hb : sourceDistance h = 4) (u : S)
    (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    {z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z)
    (hlarge : 4 ≤ (Q Rg z).relIndex (Z Rg (alpha Rg))) :
    2 < Nat.card (⁅Vcirc Rg (alpha Rg),Vcirc Rg (alpha Rg)⁆ : Subgroup (FreeAmalgam Rg)) ∧
    2 < Nat.card (⁅Vcirc Rg (p.walk.getVert 2),Vcirc Rg (p.walk.getVert 2)⁆ :
      Subgroup (FreeAmalgam Rg)) := by
  refine ⟨plane_four_large_moving_derived_gt_two h e hz hk hb u hR p hlarge,?_⟩
  obtain ⟨q,hback,_⟩ := plane_four_large_backward_configuration h e hz hk hb u hR p hlarge
  let qr : CriticalPath Rg (sourceGeometry h)
      (p.walk.getVert (p.walk.length-2)) q.start :=
    ⟨q.path.end_color,q.path.walk.reverse,
      by rw [SimpleGraph.Walk.length_reverse,q.path.shortest,SimpleGraph.dist_comm],
      critical_reverse Rg (sourceGeometry h) (sourceEdgeCentralizer h e)
        _ q.path.start_color (by
          rw [(sourceGeometry h).distance_constant _ q.path.start_color]
          exact sourceDistance_pos h) _ q.path.end_color q.path.critical⟩
  have hm := plane_four_large_moving_derived_gt_two_at h e hz hk hb u hR qr
    (reverse_critical_image_four_le h e hz hk (sourceDistance_pos h) q.path hback)
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  simpa only [hl,Nat.reduceSub] using hm

end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
