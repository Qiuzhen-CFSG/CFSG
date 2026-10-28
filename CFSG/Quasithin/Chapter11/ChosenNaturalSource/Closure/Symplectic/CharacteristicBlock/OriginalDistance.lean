module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.CharacteristicBlock.DistanceClosure

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.EdgeRadius

/-!
# Critical distance forced by the original nonabelian closure

The point residual and R₁ fix the entire original V₁, including the central
attachment. Symplectic transitivity shows that its L-conjugates generate V.
Consequently V lies in the central-omega orbit of every characteristic
replacement radical: the replacement contains V by its core-containment
property, and its image lies in R₁.

At critical distance greater than two the holomorph edge-radius layer is
abelian and its pullback is characteristic in the replacement radical.
The actual G₁ normalizes that radical because it is characteristic in
O₂(G₁). This abelian characteristic layer therefore contains ⟨V^{G₁}⟩.
Under the source's nonabelian-closure assumption this is impossible, so
positive even critical distance is exactly two. The existing whole-core
theorem supplies shortness, and the genuine core-commutator equality gives
O₂(L)=V. The root-image and both terminal branches then prove abelianness.

This source-specific argument discharges the intermediate distance premise
of `abelian_of_preceding_and_distance_two`. It does not assert the general
nonbinary MS classification or its field-four restriction. The original
module, central attachment, quotient marking, and V₂-normalizer component
are unchanged. The final owner qt-d-1222-natural-closure retains discharge
of the explicit preceding flag, Cartan and source hypotheses through 11.5.6.

Source: Aschbacher--Smith 11.5.7, printed pp.782--784;
Meierfrankenfeld--Stellmacher (1993), (3.6), printed pp.870--872, and the
holomorph edge-radius argument in (4.6.8), printed pp.905--908.
-/

set_option backward.isDefEq.respectTransparency false
public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.CharacteristicBlock
open Subgroup Representation LocalGeometry Theory.SpecificGroups.SymplecticFour
open CFSG.Quasithin.Chapter12.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} (E : Geometry D) (m : MarkedFlag E)

include m in
/-- The L-orbit of the full point preimage generates the chosen V. -/
theorem seed_le_of_point_le (B : Subgroup G) (hB : L ≤ normalizer (B : Set G))
    (hp : E.V₁ ≤ B) : V ≤ B := by
  let c := Coordinates.sp4 m.action
  have hn : m.flag.space 0 ≠ ⊥ := by
    intro he
    have hd := m.flag.dimension 0
    rw [he, finrank_bot] at hd
    norm_num at hd
  have hex : ∃ w, w ∈ m.flag.space 0 ∧ w ≠ 0 := by
    by_contra hh
    apply hn
    apply le_bot_iff.mp
    intro w hw
    exact Classical.not_not.mp (fun hw0 => hh ⟨w,hw,hw0⟩)
  obtain ⟨w,hw,hw0⟩ := hex
  intro x hx
  let v : V := ⟨x,hx⟩
  by_cases hv : (c.projection v).toAdd = 0
  · apply hp
    rw [m.point_preimage]
    apply (c.mem_preimage _ v).mpr
    change (c.projection v).toAdd ∈ m.flag.space 0
    rw [hv]
    exact (m.flag.space 0).zero_mem
  obtain ⟨s,hs⟩ := TwoLocalCover.nonzero_vector_transitive hv hw0
  obtain ⟨l,hl⟩ := c.quotientMap_surjective s
  let v' := V.normalizerMonoidHom (inclusion D.normalizes l) v
  have hv' : (v' : G) ∈ E.V₁ := by
    rw [m.point_preimage]
    apply (c.mem_preimage _ v').mpr
    have he := c.projection_component_conjugation l v
    change (c.projection v').toAdd = c.modelAction (c.quotientMap l) (c.projection v).toAdd at he
    change (c.projection v').toAdd ∈ m.flag.space 0
    rw [he,hl]
    rwa [show (c.modelAction s) (c.projection v).toAdd = w from hs]
  have hh := le_normalizer_iff.mp hB (l : G)⁻¹ (L.inv_mem l.property) (v' : G) (hp hv')
  change (l : G)⁻¹ * ((l : G) * x * (l : G)⁻¹) * ((l : G)⁻¹)⁻¹ ∈ B at hh
  simpa only [inv_inv, inv_mul_cancel_left, mul_assoc, inv_mul_cancel, mul_one] using hh

/-- The point residual fixes every lift of its fixed natural point. -/
theorem local_centralizes_point (g : Sp E.input.field.Carrier)
    (hp : m.flag.space 0 = (point E.input.field.Carrier).map (toLinear g).toLinearMap) :
    E.L₁ ≤ centralizer (E.V₁ : Set G) := by
  intro l hl x hx
  let a : L := ⟨l,E.L₁_le hl⟩
  let v : V := ⟨x,E.V₁_le hx⟩
  let c := Coordinates.sp4 m.action
  have hv : (c.projection v).toAdd ∈ (point E.input.field.Carrier).map (toLinear g).toLinearMap := by
    rw [←hp]
    apply (c.mem_preimage _ v).mp
    change x ∈ m.flag.Vi 0
    rwa [←m.point_preimage]
  obtain ⟨w,hw,he⟩ := hv
  have ha : PointModel.quotientMap m a ∈ pointLocal.map (MulAut.conj g).toMonoidHom := by
    rw [← PointModel.local_identification m g hp]
    exact ⟨a,hl,rfl⟩
  obtain ⟨b,hb,hbe⟩ := ha
  have hwfix : b • w = w := by
    obtain ⟨t,rfl⟩ := Submodule.mem_span_singleton.mp hw
    change (toLinear b) (t • e 0) = t • e 0
    rw [map_smul]
    exact congrArg (t • ·) ((mem_pointLocal_iff_fixed b).mp hb)
  have hvfix : (toLinear (PointModel.quotientMap m a)) (c.projection v).toAdd = (c.projection v).toAdd := by
    rw [←he,←hbe]
    change (g*b*g⁻¹) • (g • w) = g • w
    simp only [mul_smul, inv_smul_smul,hwfix]
  have hh := Terminal.component_fixed_of_projection_fixed m a v (by
    apply Multiplicative.toAdd.injective
    exact (c.projection_component_conjugation a v).trans hvfix)
  have heq := congrArg Subtype.val hh
  exact (mul_inv_eq_iff_eq_mul.mp heq).symm

/-- The actual full-cover R₁ action fixes the original point preimage. -/
theorem radical_centralizes_point (g : Sp E.input.field.Carrier)
    (hp : m.flag.space 0 = (point E.input.field.Carrier).map (toLinear g).toLinearMap) :
    E.R₁ ≤ centralizer (E.V₁ : Set G) := by
  have hN : E.R₁ ≤ normalizer (V : Set G) :=
    (localRadical_le_sylow E.V₁).trans E.input.sylow_normalizes
  intro r hr x hx
  let a : normalizer (V : Set G) := ⟨r,hN hr⟩
  have him : V.normalizerMonoidHom a ∈ actionImage (V := V) E.R₁ :=
    ⟨a,hr,rfl⟩
  obtain ⟨l,hl,he⟩ := RadicalAction.FullAmbient.radical_image_le m g hp him
  have hc := local_centralizes_point E m g hp ((pCoreIn_le 2 E.L₁) hl) x hx
  have heq := congrArg (fun f : MulAut V => (f ⟨x,E.V₁_le hx⟩ : G)) he
  change l.val * x * l.val⁻¹ = r*x*r⁻¹ at heq
  have hh : r*x*r⁻¹ = x := heq.symm.trans (mul_inv_eq_iff_eq_mul.mpr hc.symm)
  exact (mul_inv_eq_iff_eq_mul.mp hh).symm


/-- Any embedded replacement containing V inside R₁ has V in its omega orbit. -/
theorem seed_le_omegaOrbit_image
    (g : Sp E.input.field.Carrier)
    (hp : m.flag.space 0 = (point E.input.field.Carrier).map (toLinear g).toLinearMap)
    {H : Type*} [Group H] [Finite H] (R : Subgroup H)
    (f : H →* G) (hf : Function.Injective f)
    (hLf : L ≤ f.range) (hVR : V ≤ R.map f) (hR : R.map f ≤ E.R₁) :
    V ≤ (ChapterC.MSCentralOrbit.omegaOrbit R).map f := by
  apply seed_le_of_point_le E m
  · have htop : (⊤ : Subgroup H).map f ≤
        normalizer ((ChapterC.MSCentralOrbit.omegaOrbit R).map f : Set G) := by
      rw [←normalizer_eq_top (H := ChapterC.MSCentralOrbit.omegaOrbit R)]
      exact le_normalizer_map f
    exact hLf.trans ((MonoidHom.range_eq_map f).le.trans htop)
  · intro x hx
    obtain ⟨r,hr,he⟩ := hVR (E.V₁_le hx)
    refine ⟨r,subset_normalClosure ?_,he⟩
    apply (mem_omegaCenterIn_iff R r).mpr
    refine ⟨hr,?_,?_⟩
    · intro s hs
      apply hf
      simp only [map_mul]
      rw [he]
      exact (radical_centralizes_point E m g hp (hR (mem_map_of_mem f hs)) x hx).symm
    · apply hf
      rw [map_pow,map_one,he]
      let := D.elementary
      exact elemPow_eq_one_of_isElementaryAbelian x (E.V₁_le hx)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.CharacteristicBlock

namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.CharacteristicBlock
open Subgroup Theory.GroupTheory
open Stellmacher.PushingUp.AmalgamGraph
open ChapterC.BinaryMS.MS93 ChapterC.MSCentralOrbit
open scoped IsMulCommutative

private theorem normalizer_mapped_characteristic
    {P G : Type*} [Group P] [Group G]
    (C : Subgroup P) (F : Subgroup C) [F.Characteristic]
    (i : P →* G) (hi : Function.Injective i) :
    normalizer (C.map i : Set G) ≤ normalizer ((F.map C.subtype).map i : Set G) := by
  let e := C.equivMapOfInjective i hi
  let K := F.map e.toMonoidHom
  have hK : K.Characteristic := by
    apply characteristic_iff_le_comap.mpr
    intro a x hx
    obtain ⟨y, hy, rfl⟩ := hx
    refine ⟨(MulAut.congr e.symm a) y,
      characteristic_iff_le_comap.mp inferInstance (MulAut.congr e.symm a) hy, ?_⟩
    exact e.apply_symm_apply (a (e y))
  have he : (F.map C.subtype).map i = K.map (C.map i).subtype := by
    rw [map_map, map_map]
    rfl
  rw [he]
  exact normalizer_le_normalizer_characteristic_image (C.map i) K

/-- At distance greater than two, the edge layer controls every ambient
normalizer conjugate of a seed in the original omega orbit. -/
private theorem closure_commutative_of_large_distance
    {H G : Type*} [Group H] [Finite H] [Group G]
    (R : Subgroup H) (f : H →* G) (hf : Function.Injective f)
    (A N : Subgroup G) (hAR : A ≤ R.map f) (hAZ : A ≤ (omegaOrbit R).map f)
    (hN : N ≤ normalizer (R.map f : Set G))
    (graph : ChapterC.BinaryMS.MS93.Geometry R) (hb : 2 < graph.b R) :
    IsMulCommutative (conjugateSpanBy A N) := by
  let B := ChapterC.BinaryMS.MS93.V R (beta R)
  let C := B.comap (embedS R)
  let : IsMulCommutative B := DistanceFour.Flags.RankOne.edgeRadius_abelian
    graph hb (alpha R) (beta R) rfl (base_adjacent R)
  let : IsMulCommutative C := B.comap_injective_isMulCommutative (embedS_injective R)
  let : C.Characteristic := DistanceFour.Flags.RankOne.edgeRadius_comap_characteristic
  have hZ : Z R (alpha R) ≤ B := by
    change Z R (alpha R) ≤ ChapterC.BinaryMS.MS93.V R (beta R)
    rw [DistanceFour.Flags.RankOne.V_eq_neighborSpan (alpha R) (beta R) rfl (base_adjacent R)]
    exact le_iSup_of_le (alpha R) (le_iSup_of_le (adjacent_symm R (base_adjacent R)) le_rfl)
  have hAC : A ≤ (C.map R.subtype).map f := by
    intro x hx
    obtain ⟨r,hr,rfl⟩ := hAR hx
    obtain ⟨z,hz,he⟩ := hAZ hx
    have hzr : z = r := hf he
    subst z
    have hzr' : embedM R r ∈ Z R (alpha R) := by
      rw [Z_alpha_eq_omegaOrbit]
      exact mem_map_of_mem _ hz
    refine ⟨r,⟨⟨r,hr⟩,?_,rfl⟩,rfl⟩
    change embedS R ⟨r,hr⟩ ∈ B
    rw [← DFunLike.congr_fun (embedM_comp_subtype R) ⟨r,hr⟩]
    exact hZ hzr'
  have hNC := hN.trans (normalizer_mapped_characteristic R C f hf)
  have hle := conjugateSpanBy_le hAC hNC
  exact IsMulCommutative.of_setLike_mul_comm fun a ha b hb =>
    setLike_mul_comm (hle ha) (hle hb)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.CharacteristicBlock

namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.CharacteristicBlock
open Subgroup Theory.GroupTheory Theory.SpecificGroups.SymplecticFour
open CFSG.Quasithin.Chapter12.Section02
open ChapterC.BinaryMS.MS93 ChapterC.RankTwo.NonbinarySymplectic
open RadicalAction
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} (E : Geometry D) (m : MarkedFlag E)

/-- Nonabelianness of the original G₁-closure forces a genuine minimum
characteristic replacement of distance two for its literal MS-pair. -/
theorem msPair_distance_two_of_nonabelian
    (g : Sp E.input.field.Carrier)
    (hp : m.flag.space 0 = (point E.input.field.Carrier).map (toLinear g).toLinearMap)
    (hms : LocalGeometry.Normalizers.PointBlocks.NonbinaryMSPair
      E.input.field L (E.G₁.pCoreIn 2))
    (hne : ¬ IsMulCommutative E.W) :
    ∃ d : CharacteristicReduction (L.subgroupOf (L ⊔ E.G₁.pCoreIn 2))
      ((E.G₁.pCoreIn 2).subgroupOf (L ⊔ E.G₁.pCoreIn 2)),
      ∃ graph : ChapterC.BinaryMS.MS93.Geometry d.radical,
        graph.b d.radical = 2 := by
  let J := L ⊔ E.G₁.pCoreIn 2
  let R := (E.G₁.pCoreIn 2).subgroupOf J
  let h := intrinsicMSInput E m hms
  obtain ⟨d,graph,hpos,heven,_⟩ := h.exists_positive_even_replacement
  refine ⟨d,graph,?_⟩
  have hnlarge : ¬ 2 < graph.b d.radical := by
    intro hlarge
    let f : d.overgroup →* G := J.subtype.comp d.overgroup.subtype
    have hf : Function.Injective f := J.subtype_injective.comp d.overgroup.subtype_injective
    have hLf : L ≤ f.range := by
      intro l hl
      exact ⟨⟨⟨l,mem_sup_left hl⟩,mem_sup_left hl⟩,rfl⟩
    have hVJ : V ≤ J := D.le_component.trans le_sup_left
    have hJN : J ≤ normalizer (V : Set G) :=
      sup_le D.normalizes ((core_le_sylow E m).trans E.input.sylow_normalizes)
    have hVC : V ≤ J.pCoreIn 2 := by
      let := D.elementary
      exact le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 V) hVJ hJN
    have hVC' : V.subgroupOf J ≤ pCore 2 J := by
      apply (map_le_map_iff_of_injective J.subtype_injective).mp
      rw [map_subgroupOf_eq_of_le hVJ]
      exact hVC
    have hVR : V ≤ d.radical.map f := by
      intro v hv
      let vJ : J := ⟨v,hVJ hv⟩
      have ha : vJ ∈ d.ambient :=
        d.core_containment ⟨mem_sup_left (D.le_component hv),hVC' hv⟩
      exact ⟨⟨vJ,mem_sup_right ha⟩,ha,rfl⟩
    have hmap : d.radical.map f = d.ambient.map J.subtype := by
      rw [show f = J.subtype.comp d.overgroup.subtype from rfl,←map_map]
      rw [map_subgroupOf_eq_of_le (show d.ambient ≤ d.overgroup from le_sup_right)]
    have hRQ : d.radical.map f ≤ E.G₁.pCoreIn 2 := by
      rw [hmap]
      exact (map_mono (map_subtype_le d.subgroup)).trans_eq
        (map_subgroupOf_eq_of_le (show E.G₁.pCoreIn 2 ≤ J from le_sup_right))
    have hQR : E.G₁.pCoreIn 2 ≤ E.R₁ :=
      pCoreIn_le_of_sylow_le T le_sup_right
        (sup_le ((residualIn_le _).trans inf_le_right) m.sylow_le_point_normalizer)
    have hN : E.G₁ ≤ normalizer (d.radical.map f : Set G) := by
      rw [hmap]
      let := d.characteristic
      have hh := normalizer_mapped_characteristic R d.subgroup J.subtype J.subtype_injective
      rw [map_subgroupOf_eq_of_le (show E.G₁.pCoreIn 2 ≤ J from le_sup_right)] at hh
      exact (point_normalizer_normalizes_core E).trans hh
    have hZ := seed_le_omegaOrbit_image E m g hp d.radical f hf hLf hVR (hRQ.trans hQR)
    exact hne (closure_commutative_of_large_distance d.radical f hf V E.G₁ hVR hZ hN graph hlarge)
  obtain ⟨k,hk⟩ := heven
  omega

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.CharacteristicBlock

namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic
open Subgroup Theory.SpecificGroups.SymplecticFour
open CFSG.Quasithin.Chapter12.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} (E : Geometry D) (m : MarkedFlag E)

variable
    (g : Sp E.input.field.Carrier)
    (hpoint : m.flag.space 0 = (point E.input.field.Carrier).map (toLinear g).toLinearMap)
    (hthree : m.flag.space 2 =
      ((form E.input.field.Carrier).orthogonal (point E.input.field.Carrier)).map
        (toLinear g).toLinearMap)
    (hX : LocalGeometry.IsCartan T L E.X)
    (hcartan : PointModel.image m (E.L₁ ⊔ E.X) =
      pointParabolic.map (MulAut.conj g).toMonoidHom)
    (hn3 : E.L₁ ⊔ (T : Subgroup G) ≤ normalizer (E.V₃ : Set G))
    (hirr : ∀ A : Subgroup G, E.V₁ ≤ A → A ≤ E.V₃ →
      E.L₁ ⊔ (T : Subgroup G) ≤ normalizer (A : Set G) → A = E.V₁ ∨ A = E.V₃)
    (hti : ∀ x ∈ E.M, V ⊓ V.map (MulAut.conj x).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj x).toMonoidHom = V)
    (hgen : E.G₁ ≤ (E.K ⊔ E.Y) ⊔ E.M₁) (hVX : ⁅V,E.X⁆ = V)
    (hfour : ∀ P : Subgroup G, ⁅P,E.X⁆ = P → P ≤ (T : Subgroup G) →
      (frattini P).map P.subtype ≤ E.G₁.pCoreIn 2 → ⁅P,E.Y⁆ ≤ E.Y.pCoreIn 2)
    (hfive : ⁅(L ⊔ (T : Subgroup G)).pCoreIn 2,E.X⁆ ≤
      (E.K ⊔ (T : Subgroup G)).pCoreIn 2)

include hpoint hthree hX hcartan hn3 hirr hti hgen hVX hfour hfive in
/-- The symplectic branch of 11.5.7 from its exact preceding source geometry.
All intermediate radical, core-recognition and distance premises are proved. -/
theorem abelian_of_preceding
    (p : Terminal.PointCoordinates E m)
    (σ : MulAut (Sp E.input.field.Carrier))
    (hlocal₁ : (E.L₁.subgroupOf L).map
      (σ.toMonoidHom.comp (Terminal.RadicalGeometry.componentQuotient m)) = pointLocal)
    (hlocal₂ : (E.L₂.subgroupOf L).map
      (σ.toMonoidHom.comp (Terminal.RadicalGeometry.componentQuotient m)) = planeLocal)
    (hunique : Source.UniqueNoncentralComponent (normalizer (E.V₂ : Set G)) E.V₂ E.L₂)
    (hmoved₁ : ⁅V,E.L₁⁆ = E.V₃) (hmoved₂ : ⁅V,E.L₂⁆ = V)
    (hcontrol : normalizer (E.V₃ : Set G) ⊓ normalizer (E.L₁ : Set G) ≤ E.M)
    (hout : ¬ centralizer (E.V₁ : Set G) ≤ E.M)
    : IsMulCommutative E.W := by
  by_contra hn
  apply hn
  apply abelian_of_preceding_and_distance_two E m g hpoint hthree hX hcartan
    hn3 hirr hti hgen hVX hfour hfive p σ hlocal₁ hlocal₂ hunique hmoved₁ hmoved₂
    hcontrol hout
  intro hms
  exact CharacteristicBlock.msPair_distance_two_of_nonabelian E m g hpoint hms hn

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic
