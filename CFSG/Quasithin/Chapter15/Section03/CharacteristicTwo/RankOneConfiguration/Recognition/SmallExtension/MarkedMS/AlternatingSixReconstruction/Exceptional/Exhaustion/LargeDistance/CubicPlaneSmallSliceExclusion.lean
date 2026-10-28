module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneSliceShift
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneSpanStabilization

/-!
# Strict small forward slices on the original cubic plane graph

The actual forward shift and its full stabilizer invariant orbit span
force the original forward slice to have index greater than two above
distance four. A hypothetical small slice yields a nonzero order-two
commutator with its transported two-group kernel. That kernel escapes
the midpoint core and controls the full midpoint-normal seed span,
contradicting the established radius escape.

The result transports to every component vertex with the same critical
walk and second vertex. It keeps the original cubic projection kernel,
its odd quotient, and both full moving covers. No uniform critical-image
bound or global distance bound is assumed or asserted.

Source: Meierfrankenfeld--Stellmacher (1993), (5.9), printed pp.920--922.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement IsMulCommutative Pointwise
open Theory.SpecificGroups.SymmetricSix Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
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
/-- Every small-critical forward slice on the original plane graph is
strict above distance four. All shift and stabilization data are constructed. -/
theorem plane_small_forward_slice_strict
    (hb : 4 < sourceDistance h) (u : S)
    (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    {z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z)
    (hsmall : (Q Rg z).relIndex (Z Rg (alpha Rg)) < 4) :
    2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (p.walk.getVert 2)) := by
  by_contra! hslice
  have hb2 : 2 < sourceDistance h := by omega
  have hel := (plane_critical_paths h e hz hk u hR p).2.2.2
  obtain ⟨s⟩ := plane_exists_small_slice_shift h e hz hk hb2 u hR p hsmall hslice
  have hcollapse := s.plane_spanOrbit_stabilizes e hz hk hb u hR hsmall hslice
  have hcomm := s.span_commutator e hz hk hb2 hsmall hslice
  have hcard := (s.line_facts e hz hk hb2 hsmall hslice hel).1
  let c := p.walk.getVert 2
  let a := s.centerVertex
  have hc : color Rg c = false := s.path.start_color
  have hac : (cosetGraph Rg).dist a c = 2 := by
    dsimp only [a,c,SmallSliceShift.centerVertex]
    rw [←s.fixes_second,dist_act]
    exact p.dist_start (by
      have hl : p.walk.length = sourceDistance h := p.length_eq_b
      omega)
  have hZaY : Z Rg a ≤ s.span :=
    LocalCommutator.center_Z_le_span s.center_color (by
      rw [SimpleGraph.dist_comm]
      exact hac)
  have hYN : stabilizer Rg c ≤ normalizer (s.span : Set (FreeAmalgam Rg)) := by
    rw [←hcollapse.1]
    exact hcollapse.2
  have hTQa : s.kernel ≤ Q Rg a := by
    rw [s.kernel_eq hb2]
    exact inf_le_left
  have hTG : s.kernel ≤ stabilizer Rg c := hTQa.trans
    (Q_le_stabilizer_of_dist_le_two a c s.center_color hc hac.le)
  have hcommU : ⁅U Rg c,s.kernel⁆ = s.line := by
    have hUm : (U Rg c).map (MulAut.conj s.conjugator).toMonoidHom = U Rg c :=
      mem_normalizer_iff_map_conj_eq.mp (U_normalized c (Ltilde_le_stabilizer _ s.residual))
    dsimp only [SmallSliceShift.line,forwardSliceLine,SmallSliceShift.kernel]
    rw [map_commutator,hUm]
  have hHc : s.line ≤ Z Rg c := by
    rw [←hcommU]
    exact (le_normalizer_iff_commutator_le_left.mp (hTG.trans (U_normalized c))).trans
      (DistanceEight.U_le_Z Rg c)
  have hTne : ¬ s.kernel ≤ Q Rg c := by
    intro hle
    have he : ⁅U Rg c,s.kernel⁆ = ⊥ := le_bot_iff.mp
      ((commutator_mono (DistanceEight.U_le_Z Rg c) hle).trans_eq
        (Z_centralizes_Q Rg c hc))
    rw [hcommU] at he
    rw [he,card_bot] at hcard
    omega
  let F := conjugateSpanBy (Z Rg a) (stabilizer Rg c)
  have hFY : F ≤ s.span := conjugateSpanBy_le hZaY hYN
  have hFV : F ≤ V Rg c := conjugateSpanBy_le
    ((le_conjugateSpanBy _ _).trans (s.seedOrbit_radius_and_escape e hz hb2).1)
    (DistanceEight.V_normalized Rg c)
  have hFB := normalized_radius_le_slice_of_controlled_actor h e hz hb2 hc F s.kernel hFV
    (le_normalizer_conjugateSpanBy _ _) hTG
    ((Q_isPGroup Rg h.relative_radical.isPGroup h.relative_radical.twoCore_le a
      s.center_color).to_le hTQa) hTne
    (((commutator_mono hFY le_rfl).trans_eq hcomm).trans hHc)
  have hDF : s.seedOrbit ≤ F := conjugateSpanBy_mono le_rfl inf_le_left
  exact (s.seedOrbit_radius_and_escape e hz hb2).2 (hDF.trans hFB)

include h e hz hk in
/-- Vertex transport preserves the original strict forward slice and the
same small critical image at every component vertex. -/
theorem plane_small_forward_slice_strict_at
    (hb : 4 < sourceDistance h) (u : S)
    (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    {a z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (hsmall : (Q Rg z).relIndex (Z Rg a) < 4) :
    2 < (B Rg a ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (p.walk.getVert 2)) := by
  obtain ⟨g,hg⟩ := exists_mVertex_of_color Rg p.start_color
  have hbase : act Rg g⁻¹ a = alpha Rg := by
    rw [hg,act_mVertex,mul_inv_cancel]
    rfl
  have hpact : ∃ p₀ : CriticalPath Rg (sourceGeometry h)
      (act Rg g⁻¹ a) (act Rg g⁻¹ z),
      p₀.walk.getVert 2 = act Rg g⁻¹ (p.walk.getVert 2) :=
    ⟨p.act g⁻¹,by simp only [CriticalPath.act,actWalk_getVert]⟩
  rw [hbase] at hpact
  obtain ⟨p₀,hvert⟩ := hpact
  have hsmall₀ : (Q Rg (act Rg g⁻¹ z)).relIndex (Z Rg (alpha Rg)) < 4 := by
    rw [←hbase,Q_act,Z_act,relIndex_map_map_of_injective _ _ (MulAut.conj g⁻¹⁻¹).injective]
    exact hsmall
  have hB := Escape.PairingControl.FirstPairing.B_act
    (geometry := sourceGeometry h) (by change 2 < sourceDistance h; omega)
    g⁻¹ a p.start_color
  rw [hbase,inv_inv] at hB
  have hi := plane_small_forward_slice_strict h e hz hk hb u hR p₀ hsmall₀
  rw [hvert,U_act,inv_inv,hB,relIndex_map_map_of_injective _ _ (MulAut.conj g).injective] at hi
  exact hi

end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
