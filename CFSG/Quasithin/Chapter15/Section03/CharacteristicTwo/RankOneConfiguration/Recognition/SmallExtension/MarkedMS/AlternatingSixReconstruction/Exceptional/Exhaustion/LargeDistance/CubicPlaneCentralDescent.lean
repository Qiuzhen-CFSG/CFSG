module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneRadiusCoreFixed
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.DistanceFourEvenCover
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.FaithfulModels
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicTerminalActor
public import Theory.Representation.HexacodeAction.SmallInvolution.CentralKernel
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.NaturalStructure.Exclusion.MovingAbelian.Pairing

/-!
# The original plane central quotient and its retained cubic actor

The controlled even actor bounds movement on the literal moving central
quotient by three binary dimensions. Restriction to KQ retains the triple
cover and kills exactly Q. Whole-radius fixedness supplies the original
residual-invariant commutator forms.
Source: MS93 (3.8) and (5.12)(2), printed pp.878--879,925--926.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Theory.SpecificGroups.SymmetricSix Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.NaturalStructure.Exclusion
open scoped IsMulCommutative commutatorElement Pointwise
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
open AlternatingSixReconstruction.Exceptional.OriginalSylow
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "Rg" => edge L R
local notation "π" => CubicAction.projection h e hz hk

/-- Whole-radius fixedness also fixes its derived subgroup under the residual. -/
theorem plane_four_large_radius_derived_fixed
    (hb : sourceDistance h = 4) (u : S)
    (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    {z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z)
    (hlarge : 4 ≤ (Q Rg z).relIndex (Z Rg (alpha Rg))) :
    ⁅V Rg (alpha Rg),V Rg (alpha Rg)⁆ ≤ fixedCore Rg (alpha Rg) :=
  (commutator_mono le_rfl ((sourceGeometry h).V_le_Q (show 2 < sourceDistance h by omega) _ rfl)).trans
    (plane_four_large_radius_core_fixed h e hz hk hb u hR p hlarge)

/-- The controlled source actor acts inside the full even cover and moves at
most three dimensions on the actual moving central quotient. -/
theorem plane_four_large_even_cover_actor
    (hb : sourceDistance h = 4) (u : S)
    (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    {z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z)
    (hlarge : 4 ≤ (Q Rg z).relIndex (Z Rg (alpha Rg))) :
    letI := moving_central_quotient_elementary (sourceGeometry h) (sourceDistance_pos h)
      (alpha Rg) rfl (plane_four_large_radius_derived_fixed h e hz hk hb u hR p hlarge)
    ∃ A : Subgroup (evenCoverGroup L R),
      ∃ t : Atlas.Codes.HexEvenAutomorphisms, orderOf t = 2 ∧
        t ∈ A.map (evenCoverProjection h e hz) ∧
        fixedCodim ((Offenders.linearize (movingQuotientAction (alpha Rg))).comp
          (evenCoverEmbedding h)) A ≤ 3 := by
  let a := alpha Rg
  let H := evenCoverGroup L R
  let f := embedM Rg
  let j := evenCoverEmbedding h
  have hfixed := plane_four_large_radius_derived_fixed h e hz hk hb u hR p hlarge
  let := moving_central_quotient_elementary (sourceGeometry h) (sourceDistance_pos h) a rfl hfixed
  let := finite_moving (sourceGeometry h) (show 2 < sourceDistance h by omega) a rfl
  let ρ := Offenders.linearize (movingQuotientAction a)
  obtain ⟨W,hWU,hcomm,b,hbW,hb2,hbeven⟩ := critical_radius_even_actor h e hz hk p hlarge
  obtain ⟨g,hg,hgb⟩ := hbW
  have hgH : g ∈ H := by
    change g ∈ evenCoverGroup L R
    rw [evenCoverGroup_eq_even_preimage h e hz hk]
    change π g ∈ alternatingGroup (Fin 6)
    rwa [hgb]
  let x : H := ⟨g,hgH⟩
  let A := zpowers x
  have hg2 : g^2 = 1 := by
    apply embedM_injective Rg
    rw [map_pow,map_one]
    let := (sourceGeometry h).Z_elementary (sourceDistance_pos h) z p.end_color
    exact elemPow_eq_one_of_isElementaryAbelian (f g)
      ((hWU.trans (DistanceEight.U_le_Z Rg z)) hg)
  have hx2 : x^2 = 1 := Subtype.ext hg2
  let t := evenCoverProjection h e hz x
  have ht1 : t ≠ 1 := by
    intro he
    have hxQ : x ∈ (evenCoverProjection h e hz).ker := he
    rw [evenCoverProjection_kernel] at hxQ
    have hgQ : g ∈ pCore 2 (L ⊔ R : Subgroup G) := hxQ
    have hgE : g ∈ extensionKernel h := mem_sup_right hgQ
    have hb1 : b = 1 := by
      rw [←hgb]
      show g ∈ (π).ker
      rwa [CubicAction.projection_kernel h e hz hk]
    rw [hb1,orderOf_one] at hb2
    omega
  have ht : orderOf t = 2 := orderOf_eq_prime
    (by rw [←map_pow,hx2,map_one]) ht1
  have hsub : A.map j ≤ W.subgroupOf (stabilizer Rg a) := by
    rw [MonoidHom.map_zpowers]
    exact zpowers_le.mpr hg
  have hc := moving_fixedCodim_pow_le_radius_index_X (sourceGeometry h) (show 2 < sourceDistance h by omega) a rfl
    hfixed W (Q Rg (p.walk.getVert (p.walk.length-2)))
    (hcomm.trans ((sourceGeometry h).omega_bound a rfl (sourceDistance_pos h)))
  have hi := critical_radius_image_index_le_eight h e hz hk p
  have hcost : fixedCodim ρ (W.subgroupOf (stabilizer Rg a)) ≤ 3 := by
    exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp (hc.trans hi)
  have hm := Submodule.finrank_mono (fixedSpace_antitone ρ hsub)
  have he1 := fixedCodim_add_finrank ρ (A.map j)
  have he2 := fixedCodim_add_finrank ρ (W.subgroupOf (stabilizer Rg a))
  refine ⟨A,t,ht,mem_map_of_mem _ (mem_zpowers x),?_⟩
  change fixedCodim (ρ.comp j) A ≤ 3
  unfold fixedCodim
  rw [fixedSpace_comp_map]
  unfold fixedCodim at he1 he2 hcost
  omega

/-- The actual E-kernel acts trivially on the moving central quotient.
The proof excludes a surviving cubic character by the source commutator forms. -/
theorem plane_four_large_even_extension_kernel
    (hb : sourceDistance h = 4) (u : S)
    (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    {z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z)
    (hlarge : 4 ≤ (Q Rg z).relIndex (Z Rg (alpha Rg))) :
    letI := moving_central_quotient_elementary (sourceGeometry h) (sourceDistance_pos h)
      (alpha Rg) rfl (plane_four_large_radius_derived_fixed h e hz hk hb u hR p hlarge)
    (extensionKernel h).subgroupOf (evenCoverGroup L R) ≤
      (((Offenders.linearize (movingQuotientAction (alpha Rg))).comp
        (evenCoverEmbedding h))).ker := by
  let a := alpha Rg
  let H := evenCoverGroup L R
  let j := evenCoverEmbedding h
  have hb2 : 2 < sourceDistance h := by omega
  have hfixed := plane_four_large_radius_derived_fixed h e hz hk hb u hR p hlarge
  let := moving_central_quotient_elementary (sourceGeometry h) (sourceDistance_pos h) a rfl hfixed
  let := finite_moving (sourceGeometry h) hb2 a rfl
  let ρ := Offenders.linearize (movingQuotientAction a)
  let τ := ρ.comp j
  have hfullR : subspaceCommutator τ ⊤ (pResidual 2 H) = ⊤ := by
    rw [subspaceCommutator_comp_map,evenCoverEmbedding_residual_map h]
    exact movingQuotientAction_full_original h (sourceGeometry h) hb2 a rfl hfixed
  have hfixR : fixedSpace τ (pResidual 2 H) = ⊥ := by
    rw [fixedSpace_comp_map,evenCoverEmbedding_residual_map h]
    exact movingQuotient_fixedSpace_eq_bot_original h (sourceGeometry h) hb2 a rfl hfixed
  have hfull : subspaceCommutator τ ⊤ ⊤ = ⊤ := by
    apply top_unique
    apply hfullR.symm.trans_le
    apply Submodule.span_mono
    rintro _ ⟨g,_,v,hv,rfl⟩
    exact ⟨g,mem_top g,v,hv,rfl⟩
  have hfix : fixedSpace τ ⊤ = ⊥ :=
    le_bot_iff.mp ((fixedSpace_antitone τ le_top).trans_eq hfixR)
  obtain ⟨forms,_halt,hsep,hinv⟩ := exists_derived_fixed_forms (P := Vcirc Rg a)
  have hPV : Vcirc Rg a ≤ V Rg a :=
    le_normalizer_iff_commutator_le_left.mp ((Ltilde_le_stabilizer a).trans (V_normalized a))
  have hDX := (radius_bounds_at h e hz hk a rfl a a).2.1
  have hHC : Ltilde Rg a ⊔ Q Rg a ≤
      centralizer ((⁅V Rg a,V Rg a⁆ : Subgroup (FreeAmalgam Rg)) : Set _) :=
    sup_le (le_centralizer_iff.mp (hfixed.trans inf_le_right))
      ((Q_le_centralizer_X Rg a).trans (centralizer_le hDX))
  have hforms (g : H) (B : LinearMap.BilinForm (ZMod 2)
      (Additive ((Vcirc Rg a) ⧸ center (Vcirc Rg a)))) (hB : B ∈ forms) (v w) :
      B (τ g v) (τ g w) = B v w := by
    apply hinv (movingAction a (j g)) ?_ B hB v w
    intro d
    apply Subtype.ext
    rw [movingAction_apply]
    have hd : ((d : Vcirc Rg a) : FreeAmalgam Rg) ∈
        ⁅Vcirc Rg a,Vcirc Rg a⁆ := by
      rw [←map_subtype_commutator]
      exact mem_map_of_mem (Vcirc Rg a).subtype d.property
    have hg : (j g : FreeAmalgam Rg) ∈ Ltilde Rg a ⊔ Q Rg a := by
      change embedM Rg g.val ∈ _
      rw [←evenCoverGroup_map h]
      exact mem_map_of_mem _ g.property
    rw [←hHC hg _ (commutator_mono hPV hPV hd),mul_inv_cancel_right]
  obtain ⟨A,t,ht,htA,hcost⟩ := plane_four_large_even_cover_actor h e hz hk hb u hR p hlarge
  have hker := Hexacode.SmallInvolution.projected_center_le_ker_of_separating_forms
    (evenCoverProjection h e hz) (evenCoverProjection_surjective h e hz)
    (evenCoverProjection_kernel_isPGroup h e hz) τ hfull hfix A t ht htA hcost forms hsep hforms
  change (center Atlas.Codes.HexEvenAutomorphisms).comap
    (CubicTerminalActor.projection h e hz) ≤ τ.ker at hker
  rwa [CubicTerminalActor.projection_center_preimage h e hz] at hker

/-- Genuine cubic descent in group form: E moves the original moving radius
only inside its intrinsic center. -/
theorem plane_four_large_moving_extension_central
    (hb : sourceDistance h = 4) (u : S)
    (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    {z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z)
    (hlarge : 4 ≤ (Q Rg z).relIndex (Z Rg (alpha Rg))) :
    ⁅Vcirc Rg (alpha Rg),(extensionKernel h).map (embedM Rg)⁆ ≤
      Vcirc Rg (alpha Rg) ⊓ centralizer (Vcirc Rg (alpha Rg) : Set (FreeAmalgam Rg)) := by
  let a := alpha Rg
  let P := Vcirc Rg a
  let H := evenCoverGroup L R
  let j := evenCoverEmbedding h
  have hfixed := plane_four_large_radius_derived_fixed h e hz hk hb u hR p hlarge
  let := moving_central_quotient_elementary (sourceGeometry h) (sourceDistance_pos h) a rfl hfixed
  have hE : extensionKernel h ≤ H :=
    sup_le ((map_subtype_le _).trans le_sup_left) le_sup_right
  have hker := plane_four_large_even_extension_kernel h e hz hk hb u hR p hlarge
  rw [commutator_comm]
  apply commutator_le.mpr
  rintro x ⟨m,hm,rfl⟩ y hy
  let mH : H := ⟨m,hE hm⟩
  let yP : P := ⟨y,hy⟩
  let d : P := movingAction a (j mH) yP / yP
  have hdcenter : d ∈ center P := by
    have he := LinearMap.congr_fun (hker (show mH ∈ (extensionKernel h).subgroupOf H from hm))
      (Additive.ofMul (QuotientGroup.mk' (center P) yP))
    change Additive.ofMul (movingQuotientAction a (j mH)
      (QuotientGroup.mk' (center P) yP)) = Additive.ofMul (QuotientGroup.mk' (center P) yP) at he
    have hh := Additive.ofMul.injective he
    rw [movingQuotientAction_apply] at hh
    exact QuotientGroup.eq_iff_div_mem.mp hh
  have hd : (d : FreeAmalgam Rg) = ⁅embedM Rg m,y⁆ := by
    change (movingAction a (j mH) yP : FreeAmalgam Rg) / y = _
    rw [movingAction_apply,div_eq_mul_inv,commutatorElement_def]
    rfl
  rw [←hd]
  refine ⟨d.property,?_⟩
  intro v hv
  exact congrArg Subtype.val (mem_center_iff.mp hdcenter ⟨v,hv⟩)

include h hk in
omit [Finite G] in
private theorem chart_kernel_intrinsic {a : Vertex Rg}
    (c : CubicEven.Chart (L := L) (R := R) a) :
    c.kernel h = stabilizer Rg a ⊓ centralizer (X Rg a : Set (FreeAmalgam Rg)) := by
  rw [CubicEven.Chart.kernel,←hk]
  change (centralizer (centralOmega L R : Set (L ⊔ R : Subgroup G))).map c.embedding = _
  have hh := map_inf_centralizer_of_injective c.embedding c.injective
    (⊤ : Subgroup (L ⊔ R : Subgroup G)) (centralOmega L R)
  simpa only [top_inf_eq,←MonoidHom.range_eq_map,c.range_eq,c.map_X] using hh.symm

/-- Cubic descent transports to every actual original component vertex,
retaining its chart kernel E and the same large critical path. -/
theorem plane_four_large_moving_extension_central_at
    (hb : sourceDistance h = 4) (u : S)
    (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    {a z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (hlarge : 4 ≤ (Q Rg z).relIndex (Z Rg a))
    (c : CubicEven.Chart (L := L) (R := R) a) :
    ⁅Vcirc Rg a,c.kernel h⁆ ≤ centralizer (Vcirc Rg a : Set (FreeAmalgam Rg)) := by
  obtain ⟨g,hg⟩ := exists_mVertex_of_color Rg p.start_color
  have hbase : act Rg g⁻¹ a = alpha Rg := by
    rw [hg,act_mVertex,mul_inv_cancel]
    rfl
  have hlarge₀ : 4 ≤ (Q Rg (act Rg g⁻¹ z)).relIndex (Z Rg (act Rg g⁻¹ a)) := by
    rw [Q_act,Z_act,relIndex_map_map_of_injective _ _ (MulAut.conj _).injective]
    exact hlarge
  let c₀ : CubicEven.Chart (L := L) (R := R) (alpha Rg) := {
    embedding := embedM Rg
    injective := embedM_injective Rg
    range_eq := (stabilizer_m_base Rg).symm
    map_X := (graph_X h).symm }
  have base := plane_four_large_moving_extension_central h e hz hk hb u hR
    (z := act Rg g⁻¹ z)
  have hq := p.act g⁻¹
  rw [hbase] at hq hlarge₀
  have hf := base hq hlarge₀
  change ⁅Vcirc Rg (alpha Rg),c₀.kernel h⁆ ≤ _ at hf
  rw [chart_kernel_intrinsic h hk c₀,←hbase] at hf
  rw [Vcirc_act,stabilizer_act,X_act,
    map_inf_centralizer_of_injective _ (MulAut.conj _).injective,
    ←map_commutator,
    map_inf_centralizer_of_injective _ (MulAut.conj _).injective] at hf
  have hh := (map_le_map_iff_of_injective (MulAut.conj _).injective).mp hf
  rw [chart_kernel_intrinsic h hk c]
  exact hh.trans inf_le_right

end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
