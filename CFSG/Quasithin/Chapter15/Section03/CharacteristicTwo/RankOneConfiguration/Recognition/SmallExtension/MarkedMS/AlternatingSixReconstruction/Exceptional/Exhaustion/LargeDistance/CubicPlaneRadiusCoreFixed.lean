module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicHattedSeedMidpoint
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicBackwardLarge
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicRadiusCoreTransfer
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicChiefComplete
public import Theory.GroupTheory.ConjugateSpanSylow

/-!
# Restricted seeds and the original cubic moving radius

The actual chief-factor dichotomy places the moving radius in the normal
span of a restricted seed escaping the Baumann slice. Its core commutator
is residual-fixed by the same large backward shift. The original cubic
normal-generation transfer then controls the whole radius, at both the
starting vertex and the actual midpoint of the original critical path.
No Sylow upgrade, global small-image hypothesis or radius-fixedness premise
is introduced.
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
private theorem restricted_span_captures_moving_radius
    (hb : 2 < sourceDistance h)
    {z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z)
    (hlarge : 4 ≤ (Q Rg z).relIndex (Z Rg (alpha Rg)))
    (E : Subgroup (FreeAmalgam Rg))
    (hEV : E ≤ V Rg (alpha Rg))
    (hEB : ¬ E ≤ B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)) :
    Vcirc Rg (alpha Rg) ≤
      conjugateSpanBy E (stabilizer Rg (alpha Rg)) ⊔ Z Rg (alpha Rg) := by
  let P := conjugateSpanBy E (stabilizer Rg (alpha Rg))
  let Y := P.comap (embedM Rg)
  have hPV : P ≤ V Rg (alpha Rg) := conjugateSpanBy_le hEV (V_normalized _)
  have hPG : P ≤ stabilizer Rg (alpha Rg) :=
    hPV.trans ((sourceGeometry h).V_local _ rfl hb)
  have hPN := le_normalizer_conjugateSpanBy E (stabilizer Rg (alpha Rg))
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
  rcases critical_radius_normal_subgroup_dichotomy h e hz hk hb p hlarge Y
      (comap_mono hPV) with hf | hm
  · have hf' := map_mono (f := embedM Rg) hf
    rw [map_commutator,hYm,hLm,hZm] at hf'
    have hPB : P ≤ B Rg (alpha Rg) ((sourceGeometry h).Z_normal _) := by
      intro v hv
      apply (mem_B_iff Rg (alpha Rg) _ ((sourceGeometry h).V_local _ rfl hb) v).mpr
      refine ⟨hPV hv,?_⟩
      intro l hl
      rw [commutator_comm] at hf'
      exact hf' (commutator_mem_commutator hl hv)
    exact (hEB ((le_conjugateSpanBy E _).trans hPB)).elim
  · have hm' := map_mono (f := embedM Rg) hm
    rw [map_commutator,radius_comap_map (h := h) hb,hLm,Subgroup.map_sup,hYm,hZm] at hm'
    exact hm'

include h e hz hk in
private theorem restricted_seed_moving_radius_core_fixed
    (hb : 2 < sourceDistance h)
    {z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z)
    (hlarge : 4 ≤ (Q Rg z).relIndex (Z Rg (alpha Rg)))
    (E : Subgroup (FreeAmalgam Rg))
    (hEV : E ≤ V Rg (alpha Rg))
    (hEB : ¬ E ≤ B Rg (alpha Rg) ((sourceGeometry h).Z_normal _))
    (hfixed : ⁅E,Q Rg (alpha Rg)⁆ ≤ fixedCore Rg (alpha Rg)) :
    ⁅Vcirc Rg (alpha Rg),Q Rg (alpha Rg)⁆ ≤ fixedCore Rg (alpha Rg) := by
  let a := alpha Rg
  let P := conjugateSpanBy E (stabilizer Rg a)
  let K := fixedCore Rg a
  have hEG : E ≤ stabilizer Rg a := hEV.trans ((sourceGeometry h).V_local _ rfl hb)
  have hKN : stabilizer Rg a ≤ normalizer (K : Set _) := fixedCore_normalized Rg a
  have hPK : ⁅P,Q Rg a⁆ ≤ K := by
    dsimp only [P]
    rw [conjugateSpanBy_eq_iSup_conj]
    apply commutator_iSup_le_of_relative_normal (stabilizer Rg a) _ _ _ hKN
    · intro g
      exact (map_mono hEG).trans_eq (mem_normalizer_iff_map_conj_eq.mp
        ((stabilizer Rg a).le_normalizer g.property))
    · intro g
      have hh := map_mono (f := (MulAut.conj (g : FreeAmalgam Rg)).toMonoidHom) hfixed
      have hQ : (Q Rg a).map (MulAut.conj (g : FreeAmalgam Rg)).toMonoidHom =
          Q Rg a := mem_normalizer_iff_map_conj_eq.mp (Q_normalized Rg a g.property)
      have hK : K.map (MulAut.conj (g : FreeAmalgam Rg)).toMonoidHom = K :=
        mem_normalizer_iff_map_conj_eq.mp (hKN g.property)
      change (⁅E,Q Rg a⁆).map _ ≤ K.map _ at hh
      rwa [map_commutator,hQ,hK] at hh
  have hm := restricted_span_captures_moving_radius h e hz hk hb p hlarge E hEV hEB
  apply (commutator_mono hm le_rfl).trans
  exact commutator_sup_le_of_relative_normal (stabilizer Rg a) _ _ _ K hKN
    (conjugateSpanBy_le_self hEG) (Z_le_stabilizer Rg _) hPK
    ((Z_centralizes_Q Rg a rfl).le.trans bot_le)

include h e hz hk in
/-- The large backward image and its strict slice produce a restricted
seed whose span controls the whole moving radius of the original plane. -/
theorem plane_four_large_moving_radius_core_fixed
    (hb : sourceDistance h = 4) (u : S)
    (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    {z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z)
    (hlarge : 4 ≤ (Q Rg z).relIndex (Z Rg (alpha Rg))) :
    ⁅Vcirc Rg (alpha Rg),Q Rg (alpha Rg)⁆ ≤ fixedCore Rg (alpha Rg) := by
  obtain ⟨q,hback,hstrict,hKQ,hKC⟩ :=
    plane_four_large_backward_configuration h e hz hk hb u hR p hlarge
  have hq2 : q.path.walk.getVert 2 = alpha Rg := by
    simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using
      q.overlap 0 (Nat.zero_le _)
  have hKfixed : ⁅Z Rg q.start,Z Rg (p.walk.getVert (p.walk.length-2))⁆ ≤
      fixedCore Rg (alpha Rg) :=
    le_inf hKQ (hKC.trans (centralizer_le (Ltilde_le_stabilizer _)))
  obtain ⟨E,_hFE,hEZ,hiE,hEQ⟩ :=
    plane_critical_hatted_seed_midpoint_control h e hz hk hb u hR q.path hback
  rw [hq2] at hEQ
  have hql : q.path.walk.length = 4 := q.path.length_eq_b.trans hb
  have hEV : E ≤ V Rg (alpha Rg) := hEZ.trans
    ((Z_le_localZSpan Rg q.start _).trans (localZSpan_le_V Rg (by
      have hd := q.path.dist_start (i := 2) (by omega)
      rw [hq2] at hd
      exact hd.le)))
  have hEB : ¬ E ≤ B Rg (alpha Rg) ((sourceGeometry h).Z_normal _) := by
    intro hbad
    let := finite_Z Rg q.start
    let : Finite (U Rg q.start) := Finite.of_injective
      (inclusion (DistanceEight.U_le_Z Rg _)) (inclusion_injective _)
    have hh := (relIndex_le_of_le_left (inf_le_left.trans hbad)
      (L := U Rg q.start) index_ne_zero_of_finite).trans hiE
    omega
  exact restricted_seed_moving_radius_core_fixed h e hz hk (by omega)
    p hlarge E hEV hEB (hEQ.le.trans hKfixed)

include h e hz hk in
/-- A large critical path fixes the entire original radius-core movement
under its local residual, retaining the full cubic kernel. -/
theorem plane_four_large_radius_core_fixed
    (hb : sourceDistance h = 4) (u : S)
    (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    {z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z)
    (hlarge : 4 ≤ (Q Rg z).relIndex (Z Rg (alpha Rg))) :
    ⁅V Rg (alpha Rg),Q Rg (alpha Rg)⁆ ≤ fixedCore Rg (alpha Rg) :=
  cubic_radius_core_fixed_of_moving_core_fixed h e hz (by omega)
    (plane_four_large_moving_radius_core_fixed h e hz hk hb u hR p hlarge)

include h e hz hk in
/-- The whole-radius bound transports to every original component vertex. -/
theorem plane_four_large_radius_core_fixed_at
    (hb : sourceDistance h = 4) (u : S)
    (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    {a z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (hlarge : 4 ≤ (Q Rg z).relIndex (Z Rg a)) :
    ⁅V Rg a,Q Rg a⁆ ≤ fixedCore Rg a := by
  obtain ⟨g,hg⟩ := exists_mVertex_of_color Rg p.start_color
  have hbase : act Rg g⁻¹ a = alpha Rg := by
    rw [hg,act_mVertex,mul_inv_cancel]
    rfl
  have base := plane_four_large_radius_core_fixed h e hz hk hb u hR
    (z := act Rg g⁻¹ z)
  rw [←hbase] at base
  have hlarge₀ : 4 ≤ (Q Rg (act Rg g⁻¹ z)).relIndex (Z Rg (act Rg g⁻¹ a)) := by
    rw [Q_act,Z_act,relIndex_map_map_of_injective _ _ (MulAut.conj _).injective]
    exact hlarge
  have hfixed := base (p.act g⁻¹) hlarge₀
  rw [V_act,Q_act,←map_commutator,fixedCore,Q_act,Ltilde_act,
    map_inf_centralizer_of_injective _ (MulAut.conj _).injective] at hfixed
  exact (map_le_map_iff_of_injective (MulAut.conj _).injective).mp hfixed

include h e hz hk in
/-- Both actual reciprocal radius-core movements are residual-fixed. The
midpoint bound uses the same large backward path with its orientation reversed. -/
theorem plane_four_large_reciprocal_radius_core_fixed
    (hb : sourceDistance h = 4) (u : S)
    (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    {z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z)
    (hlarge : 4 ≤ (Q Rg z).relIndex (Z Rg (alpha Rg))) :
    ⁅V Rg (alpha Rg),Q Rg (alpha Rg)⁆ ≤ fixedCore Rg (alpha Rg) ∧
    ⁅V Rg (p.walk.getVert 2),Q Rg (p.walk.getVert 2)⁆ ≤
      fixedCore Rg (p.walk.getVert 2) := by
  refine ⟨plane_four_large_radius_core_fixed h e hz hk hb u hR p hlarge,?_⟩
  obtain ⟨q,hback,_⟩ := plane_four_large_backward_configuration h e hz hk hb u hR p hlarge
  let qr : CriticalPath Rg (sourceGeometry h)
      (p.walk.getVert (p.walk.length-2)) q.start :=
    ⟨q.path.end_color,q.path.walk.reverse,
      by rw [SimpleGraph.Walk.length_reverse,q.path.shortest,SimpleGraph.dist_comm],
      critical_reverse Rg (sourceGeometry h) (sourceEdgeCentralizer h e)
        _ q.path.start_color (by
          rw [(sourceGeometry h).distance_constant _ q.path.start_color]
          exact sourceDistance_pos h) _ q.path.end_color q.path.critical⟩
  have hf := plane_four_large_radius_core_fixed_at h e hz hk hb u hR qr
    (reverse_critical_image_four_le h e hz hk (sourceDistance_pos h) q.path hback)
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  simpa only [hl,Nat.reduceSub] using hf

end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
