module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointCentralizer
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.OriginalCharacteristicFour
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Center.Decomposition
public import Theory.GroupTheory.Commutator.RelativeGeneration
public import Theory.GroupAction.BinaryThreePointCubic
public import Theory.GroupAction.SubgroupConjugation
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.CoreActions.ThreeLayer.Center
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.ComponentIntersection.InnerSplitting.SectionAction

/-!
# Commuting cubics in the original binary point centralizer

A cubic actor in the section centralizer acts trivially on the actual
component quotient. Coprime fixed-point lifting makes its centralizer still
surject onto SL3(2), whose natural point stabilizers contain cubics. This
constructs an order-three lift centralizing both the actor and the point.

The original moving plane lies in the natural commutator of the core center.
The genuine MS93 CommonFacts and Earlier center decomposition identify this
commutator inside the marked natural eight, including when the actor lies
outside the characteristic replacement. The original residual geometry
supplies the first cubic, and quotient faithfulness separates the second.

Application: Aschbacher–Smith, 15.3.23, printed p.1128, binary alternative
of C.1.34. No fixation of the original source four by the original overgroup
is assumed or inferred from the characteristic replacement.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve.ExchangedCases.SL3Geometry.SourceCases
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.OriginalSource
open CoreActions ThreeLayer ComponentIntersection.InnerSplitting
variable {G : Type*} [Group G] [Finite G]
local notation "SL" => Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)

/-- An actual cubic section-centralizing actor permits a second cubic fixing
any point in a marked natural subgroup of the component. -/
theorem exists_cubic_centralizing_section_actor
    (L A : Subgroup G) (hA : Nat.card A = 3)
    (hAL : A ≤ Chapter4.sectionCentralizer L)
    (e : (L ⧸ pCore 2 L) ≃* SL)
    (v : Fin 3 → ZMod 2) :
    ∃ c : L, orderOf (c : G) = 3 ∧ (c : G) ∈ centralizer (A : Set G) ∧
      c ∉ pCore 2 L ∧ e (QuotientGroup.mk' (pCore 2 L) c) • v = v := by
  have hAN : A ≤ normalizer (L : Set G) :=
    hAL.trans ((Chapter4.le_sectionCentralizer_iff _ L).mp le_rfl).1
  let _ := conjMulDistribMulActionOfLeNormalizer A L hAN
  let π : L →* SL := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hk : π.ker = pCore 2 L := by
    ext l
    change e (QuotientGroup.mk' (pCore 2 L) l) = 1 ↔ l ∈ pCore 2 L
    rw [e.map_eq_one_iff]
    exact QuotientGroup.eq_one_iff l
  have hp : IsPGroup 2 π.ker := hk ▸ pCore_isPGroup
  have hcop : Nat.Coprime (Nat.card A) (Nat.card π.ker) := by
    obtain ⟨n,hn⟩ := hp.exists_card_eq
    rw [hA,hn]
    exact (by decide : Nat.Coprime 3 2).pow_right n
  have htriv : ∀ a : A, ∀ l : L, π (a • l) = π l := by
    intro a l
    have he := DFunLike.congr_fun
      ((sectionAction_eq_one_iff L ⟨a,hAN a.property⟩).mpr (hAL a.property))
      (QuotientGroup.mk' (pCore 2 L) l)
    rw [sectionAction_apply] at he
    exact congrArg e he
  obtain ⟨c,hcf,hc,hcn,hcv⟩ :=
    Theory.GroupAction.BinaryThreePointCubic.exists_fixed_cubic_fixing_vector
      π (e.surjective.comp (QuotientGroup.mk'_surjective _)) hp hcop htriv
      v
  have hcA : (c : G) ∈ centralizer (A : Set G) := by
    intro a ha
    have he := congrArg Subtype.val (hcf (⟨a,ha⟩ : A))
    change a * (c : G) * a⁻¹ = c at he
    exact (mul_inv_eq_iff_eq_mul.mp he)
  refine ⟨c,(Subgroup.orderOf_coe c).trans hc,hcA,?_,hcv⟩
  intro hcK
  apply hcn
  change c ∈ π.ker
  rwa [hk]

/-- The abstract vector fixer centralizes the literal original natural point. -/
theorem exists_cubic_centralizing_section_actor_and_point
    (L N A : Subgroup G) (hA : Nat.card A = 3)
    (hAL : A ≤ Chapter4.sectionCentralizer L)
    (e : (L ⧸ pCore 2 L) ≃* SL)
    (m : LayerModel L N ⊥ e (NaturalCopies (ZMod 2) 1)) (z : N) :
    ∃ c : L, orderOf (c : G) = 3 ∧ (c : G) ∈ centralizer (A : Set G) ∧
      (c : G) ∈ centralizer ({(z : G)} : Set G) ∧ c ∉ pCore 2 L := by
  obtain ⟨c,hc,hcA,hcn,hcv⟩ := exists_cubic_centralizing_section_actor
    L A hA hAL e (naturalCoordinates m z).toAdd
  refine ⟨c,hc,hcA,?_,hcn⟩
  have he := naturalCoordinates_intertwining m c z
  change (naturalCoordinates m (layerConjugate L N m.normalized c z)).toAdd =
    e (QuotientGroup.mk' (pCore 2 L) c) • (naturalCoordinates m z).toAdd at he
  rw [hcv] at he
  have hz := congrArg Subtype.val ((naturalCoordinates m).injective
    (Multiplicative.toAdd.injective he))
  change (c : G) * (z : G) * (c : G)⁻¹ = z at hz
  exact mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hz)

open ChapterC BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph

/-- The original component maps into the actual source amalgam through its
inclusion in the characteristic replacement. -/
@[expose] noncomputable def originalComponentEmbedding
    {κ : GroupClass} {L T : Subgroup G} {b : BinaryMS.Input κ L T}
    (t : InputSetup b) : L →* FreeAmalgam t.reduction.radical :=
  (embedM t.reduction.radical).comp (inclusion le_sup_left)

/-- The genuine CommonFacts natural action supplies the point, while the
coprime section actor supplies the commuting lift. No component splitting
or original ambient fixation of the source four is used. -/
theorem original_natural_point_cubic
    {κ : GroupClass} {L T : Subgroup G} {b : BinaryMS.Input κ L T}
    (t : InputSetup b)
    (common : CommonFacts t.reduction.radical t.source t.geometry)
    (A : Subgroup G) (hA : Nat.card A = 3)
    (hAL : A ≤ Chapter4.sectionCentralizer L)
    (z : L) (hz : originalComponentEmbedding t z ∈ U t.reduction.radical (alpha t.reduction.radical)) :
    ∃ c : L, orderOf (c : G) = 3 ∧ (c : G) ∈ centralizer (A : Set G) ∧
      (c : G) ∈ centralizer ({(z : G)} : Set G) ∧ c ∉ pCore 2 L := by
  let u : U t.reduction.radical (alpha t.reduction.radical) :=
    ⟨originalComponentEmbedding t z,hz⟩
  let e := b.quotientEquiv.trans common.natural.marking
  obtain ⟨c,hc,hcA,hcn,hcv⟩ := exists_cubic_centralizing_section_actor
    L A hA hAL e (common.natural.equiv u).toAdd
  let cm : t.reduction.overgroup := inclusion (show L ≤ t.reduction.overgroup from le_sup_left) c
  let v : U t.reduction.radical (alpha t.reduction.radical) :=
    ⟨embedM t.reduction.radical cm * u * (embedM t.reduction.radical cm)⁻¹,
      (mem_normalizer_iff.mp (common.natural.normalized ⟨cm,rfl⟩) u).mp u.property⟩
  have he := common.natural.action cm u v rfl
  have hp : t.source.projection cm = b.quotientEquiv (QuotientGroup.mk' (pCore 2 L) c) :=
    t.projection_component c
  rw [hp] at he
  change (common.natural.equiv v).toAdd = e (QuotientGroup.mk' (pCore 2 L) c) •
    (common.natural.equiv u).toAdd at he
  rw [hcv] at he
  have hconj := congrArg Subtype.val (common.natural.equiv.injective
    (Multiplicative.toAdd.injective he))
  change originalComponentEmbedding t c * originalComponentEmbedding t z *
    (originalComponentEmbedding t c)⁻¹ = originalComponentEmbedding t z at hconj
  have hi : Function.Injective (originalComponentEmbedding t) :=
    (embedM_injective _).comp (inclusion_injective le_sup_left)
  have hz' : c * z * c⁻¹ = z := by
    apply hi
    simpa only [map_mul,map_inv] using hconj
  refine ⟨c,hc,hcA,?_,hcn⟩
  apply mem_centralizer_singleton_iff.mpr
  exact congrArg Subtype.val (mul_inv_eq_iff_eq_mul.mp hz')

/-- The actual natural commutator of the original core embeds into the
natural eight supplied by CommonFacts. Fixed center factors contribute no
component commutators, independently of their original ambient action. -/
theorem original_sourceNatural_point_mem
    {κ : GroupClass} {L T : Subgroup G} {b : BinaryMS.Input κ L T}
    (t : InputSetup b)
    (common : CommonFacts t.reduction.radical t.source t.geometry)
    (earlier : DistanceEight.CoreFactors.Earlier t.reduction.radical t.geometry)
    (z : L) (hz : (z : G) ∈ sourceNatural L) :
    originalComponentEmbedding t z ∈ U t.reduction.radical (alpha t.reduction.radical) := by
  let R := t.reduction.radical
  let K := core R (alpha R)
  let K0 := K.comap (embedM R)
  let C0 := (center K0).map K0.subtype
  let D0 := ⁅C0,L.subgroupOf t.reduction.overgroup⁆
  have hK : K0.map t.reduction.overgroup.subtype = BinaryMS.commutatorCore L :=
    t.core_pullback
  have hD : D0.map t.reduction.overgroup.subtype = sourceNatural L := by
    dsimp only [D0,C0]
    rw [map_commutator,map_subgroup_center_eq _ t.reduction.overgroup.subtype_injective,
      hK,map_subgroupOf_eq_of_le (show L ≤ t.reduction.overgroup from le_sup_left)]
    rfl
  have hKr : K ≤ (embedM R).range := by
    rw [show K = (BinaryMS.commutatorCore (L.subgroupOf t.reduction.overgroup)).map
      (embedM R) from core_alpha R t.source.two_group t.source.core_le t.source.residual]
    exact map_le_range _ _
  have hKe : K0.map (embedM R) = K := map_comap_eq_self hKr
  have hDe : D0.map (embedM R) =
      ⁅(center K).map K.subtype,Ltilde R (alpha R)⁆ := by
    dsimp only [D0,C0]
    rw [map_commutator,map_subgroup_center_eq _ (embedM_injective R),hKe,
      ←t.Ltilde_embedded]
  have hU : U R (alpha R) ≤ K :=
    DistanceTwo.U_le_core t.geometry (by have := common.large_distance; omega) _ rfl
  have hbound : D0.map (embedM R) ≤ U R (alpha R) := by
    rw [hDe,DistanceEight.CoreFactors.Center.core_center_eq_U_sup_fixedFactor common earlier]
    apply commutator_sup_le_of_relative_normal K _ _ _ _
      (hKr.trans common.natural.normalized) hU inf_le_left
      common.full_commutation.le
    rw [commutator_eq_bot_iff_le_centralizer.mpr inf_le_right]
    exact bot_le
  have hzD : (z : G) ∈ D0.map t.reduction.overgroup.subtype := hD.symm ▸ hz
  obtain ⟨q,hq,hqz⟩ := hzD
  have hqeq : q = inclusion (show L ≤ t.reduction.overgroup from le_sup_left) z :=
    Subtype.ext hqz
  change embedM R (inclusion (show L ≤ t.reduction.overgroup from le_sup_left) z) ∈ _
  rw [←hqeq]
  exact hbound (mem_map_of_mem (embedM R) hq)

/-- First cubic for an actual original natural-commutator point. All natural
module data are supplied by the genuine CommonFacts and Earlier inputs. -/
theorem original_sourceNatural_point_cubic
    {κ : GroupClass} {L T : Subgroup G} {b : BinaryMS.Input κ L T}
    (t : InputSetup b)
    (common : CommonFacts t.reduction.radical t.source t.geometry)
    (earlier : DistanceEight.CoreFactors.Earlier t.reduction.radical t.geometry)
    (A : Subgroup G) (hA : Nat.card A = 3)
    (hAL : A ≤ Chapter4.sectionCentralizer L)
    (z : L) (hz : (z : G) ∈ sourceNatural L) :
    ∃ c : L, orderOf (c : G) = 3 ∧ (c : G) ∈ centralizer (A : Set G) ∧
      (c : G) ∈ centralizer ({(z : G)} : Set G) ∧ c ∉ pCore 2 L :=
  original_natural_point_cubic t common A hA hAL z
    (original_sourceNatural_point_mem t common earlier z hz)

open Extension.SourceCases

/-- The actor may lie outside the MS overgroup. The natural point and its
commuting cubic are transported along the literal subgroup inclusions. -/
theorem ambient_sourceNatural_point_cubic
    {κ : GroupClass} {L H : Subgroup G} (hLH : L ≤ H)
    {T : Subgroup H} {b : BinaryMS.Input κ (L.subgroupOf H) T}
    (t : InputSetup b)
    (common : CommonFacts t.reduction.radical t.source t.geometry)
    (earlier : DistanceEight.CoreFactors.Earlier t.reduction.radical t.geometry)
    (A : Subgroup G) (hA : Nat.card A = 3)
    (hAL : A ≤ Chapter4.sectionCentralizer L)
    (z : L) (hz : (z : G) ∈ (sourceNatural (L.subgroupOf H)).map H.subtype) :
    ∃ c : L, orderOf (c : G) = 3 ∧ (c : G) ∈ centralizer (A : Set G) ∧
      (c : G) ∈ centralizer ({(z : G)} : Set G) ∧ c ∉ pCore 2 L := by
  let eL := subgroupOfEquivOfLe hLH
  let zi := eL.symm z
  have hzi : (zi : H) ∈ sourceNatural (L.subgroupOf H) := by
    obtain ⟨w,hw,hwz⟩ := hz
    have he : w = (zi : H) := by
      apply Subtype.ext
      exact hwz.trans (congrArg Subtype.val (eL.apply_symm_apply z)).symm
    exact he ▸ hw
  let u : U t.reduction.radical (alpha t.reduction.radical) :=
    ⟨originalComponentEmbedding t zi,original_sourceNatural_point_mem t common earlier zi hzi⟩
  let ei := b.quotientEquiv.trans common.natural.marking
  let e := ambientMarking hLH ei
  obtain ⟨c,hc,hcA,hcn,hcv⟩ := exists_cubic_centralizing_section_actor
    L A hA hAL e (common.natural.equiv u).toAdd
  let ci := eL.symm c
  have hemark : e (QuotientGroup.mk' (pCore 2 L) c) =
      ei (QuotientGroup.mk' (pCore 2 (L.subgroupOf H)) ci) := by
    have he := ambientMarking_apply hLH ei ci
    change e (QuotientGroup.mk (eL ci)) = ei (QuotientGroup.mk ci) at he
    simpa only [QuotientGroup.mk'_apply,ci,eL.apply_symm_apply] using he
  rw [hemark] at hcv
  let cm : t.reduction.overgroup := inclusion
    (show L.subgroupOf H ≤ t.reduction.overgroup from le_sup_left) ci
  let v : U t.reduction.radical (alpha t.reduction.radical) :=
    ⟨embedM t.reduction.radical cm * u * (embedM t.reduction.radical cm)⁻¹,
      (mem_normalizer_iff.mp (common.natural.normalized ⟨cm,rfl⟩) u).mp u.property⟩
  have he := common.natural.action cm u v rfl
  have hp : t.source.projection cm = b.quotientEquiv
      (QuotientGroup.mk' (pCore 2 (L.subgroupOf H)) ci) := t.projection_component ci
  rw [hp] at he
  change (common.natural.equiv v).toAdd = ei (QuotientGroup.mk' _ ci) •
    (common.natural.equiv u).toAdd at he
  rw [hcv] at he
  have hconj := congrArg Subtype.val (common.natural.equiv.injective
    (Multiplicative.toAdd.injective he))
  change originalComponentEmbedding t ci * originalComponentEmbedding t zi *
    (originalComponentEmbedding t ci)⁻¹ = originalComponentEmbedding t zi at hconj
  have hi : Function.Injective (originalComponentEmbedding t) :=
    (embedM_injective _).comp (inclusion_injective le_sup_left)
  have hz' : ci * zi * ci⁻¹ = zi := by
    apply hi
    simpa only [map_mul,map_inv] using hconj
  have hz'' : c * z * c⁻¹ = z := by
    have he := congrArg eL hz'
    simpa only [map_mul,map_inv,ci,zi,eL.apply_symm_apply] using he
  refine ⟨c,hc,hcA,?_,hcn⟩
  exact mem_centralizer_singleton_iff.mpr
    (congrArg Subtype.val (mul_inv_eq_iff_eq_mul.mp hz''))

/-- The original moving plane lies in the natural center commutator, so every
one of its points admits the required commuting cubic outside the two-core. -/
theorem movingPlane_point_cubic
    {κ : GroupClass} (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) [IsElementaryAbelian 2 (d.componentSpan c.L)]
    (e : (c.L ⧸ pCore 2 c.L) ≃* SL)
    (h : ResidualSourceData d c.L e) (hg : ResidualGeometry d c.L)
    (b : BinaryMS.Input κ (c.L.subgroupOf (c.L ⊔ d.S)) (d.S.subgroupOf (c.L ⊔ d.S)))
    (t : InputSetup b)
    (common : CommonFacts t.reduction.radical t.source t.geometry)
    (earlier : DistanceEight.CoreFactors.Earlier t.reduction.radical t.geometry)
    (A : Subgroup G) (hA : Nat.card A = 3)
    (hAL : A ≤ Chapter4.sectionCentralizer c.L)
    (z : G) (hz : z ∈ movingPlane d c.L) :
    ∃ a : c.L, orderOf (a : G) = 3 ∧ (a : G) ∈ centralizer (A : Set G) ∧
      (a : G) ∈ centralizer ({z} : Set G) ∧ a ∉ pCore 2 c.L := by
  have hUZ := movingPlane_le_coreCenter d c hg.component_normalized h.core_le h.radical
  have hUL : movingPlane d c.L ≤ c.L :=
    hUZ.trans ((map_subtype_le _).trans
      ((commutatorCore_le c.L).trans (c.L.pCoreIn_le 2)))
  have hYL : YL d c.L ≤ c.L :=
    (ComponentIntersection.intersectionResidual_le _ _).trans inf_le_right
  have hUN : movingPlane d c.L ≤ coreNatural c.L := by
    obtain ⟨_,_,_,_,_,hmove,_,_⟩ := hg.coordinates
    rw [←hmove]
    exact commutator_mono hUZ hYL
  let zi : c.L := ⟨z,hUL hz⟩
  have hzi : (zi : G) ∈ (sourceNatural (c.L.subgroupOf (c.L ⊔ d.S))).map
      (c.L ⊔ d.S).subtype := by
    rw [sourceNatural_map (show c.L ≤ c.L ⊔ d.S from le_sup_left) b.component]
    exact hUN hz
  exact ambient_sourceNatural_point_cubic le_sup_left t common earlier A hA hAL zi hzi

omit [Finite G] in
/-- A component element with nontrivial binary simple quotient image cannot
belong to the section centralizer. This separates the two cubics below. -/
theorem component_not_sectionCentralizer
    (L : Subgroup G) (e : (L ⧸ pCore 2 L) ≃* SL)
    (c : L) (hc : c ∉ pCore 2 L) : (c : G) ∉ Chapter4.sectionCentralizer L := by
  intro hcS
  have hact := (sectionAction_eq_one_iff L (inclusion L.le_normalizer c)).mpr hcS
  rw [sectionAction_on_component] at hact
  have he : MulAut.conj (e (QuotientGroup.mk' (pCore 2 L) c)) = 1 := by
    apply MulEquiv.ext
    intro x
    obtain ⟨q,rfl⟩ := e.surjective x
    have hh := DFunLike.congr_fun hact q
    change QuotientGroup.mk' (pCore 2 L) c * q *
      (QuotientGroup.mk' (pCore 2 L) c)⁻¹ = q at hh
    change e (QuotientGroup.mk' (pCore 2 L) c) * e q *
      (e (QuotientGroup.mk' (pCore 2 L) c))⁻¹ = e q
    simpa only [map_mul,map_inv] using congrArg e hh
  have heq := Matrix.PSL3Two.MarkedAutomorphisms.conj_injective
    (he.trans (map_one MulAut.conj).symm)
  exact hc ((QuotientGroup.eq_one_iff c).mp
    (e.injective (heq.trans e.map_one.symm)))

/-- The actual residual centralizer supplies the first cubic. The natural
point stabilizer then supplies a commuting cubic in the component, outside
the entire section centralizer and hence outside the first cubic subgroup. -/
theorem movingPlane_commuting_cubics
    {κ : GroupClass} (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) [IsElementaryAbelian 2 (d.componentSpan c.L)]
    (e : (c.L ⧸ pCore 2 c.L) ≃* SL)
    (h : ResidualSourceData d c.L e) (hg : ResidualGeometry d c.L)
    (b : BinaryMS.Input κ (c.L.subgroupOf (c.L ⊔ d.S)) (d.S.subgroupOf (c.L ⊔ d.S)))
    (t : InputSetup b)
    (common : CommonFacts t.reduction.radical t.source t.geometry)
    (earlier : DistanceEight.CoreFactors.Earlier t.reduction.radical t.geometry)
    (z : G) (hz : z ∈ movingPlane d c.L) :
    ∃ a : YC d c.L, ∃ v : c.L,
      orderOf (a : G) = 3 ∧ orderOf (v : G) = 3 ∧
      (a : G) ∈ centralizer ({z} : Set G) ∧
      (v : G) ∈ centralizer ({z} : Set G) ∧
      (a : G) * (v : G) = (v : G) * (a : G) ∧
      (v : G) ∉ Chapter4.sectionCentralizer c.L := by
  have hdiv : 3 ∣ Nat.card (YC d c.L) := by
    apply Nat.dvd_of_factorization_pos
    intro hn
    have he := h.centralizer_three_part
    rw [hn,pow_zero] at he
    omega
  obtain ⟨a,ha⟩ := exists_prime_orderOf_dvd_card' (G := YC d c.L) 3 hdiv
  have haG : orderOf (a : G) = 3 := (Subgroup.orderOf_coe a).trans ha
  let A := zpowers (a : G)
  have hAC : A ≤ YC d c.L := zpowers_le.mpr a.property
  have hA : Nat.card A = 3 := by rw [Nat.card_zpowers,haG]
  have hCS : YC d c.L ≤ Chapter4.sectionCentralizer c.L :=
    (ComponentIntersection.centralizerResidual_le _ _).trans inf_le_right
  obtain ⟨v,hv,hvA,hvz,hvQ⟩ := movingPlane_point_cubic
    d c e h hg b t common earlier A hA (hAC.trans hCS) z hz
  refine ⟨a,v,haG,hv,?_,hvz,hvA _ (mem_zpowers _),
    component_not_sectionCentralizer c.L e v hvQ⟩
  exact mem_centralizer_singleton_iff.mpr ((hg.plane_centralized a.property) z hz).symm

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.OriginalSource

namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
open Subgroup ChapterC BinaryMS.MS93 LinearThree.OriginalSource
open CFSG.Quasithin.Chapter15.Section03.RankTwo
variable {G : Type*} [Group G] [Finite G]

/-- Original Chapter15 data produce the commuting cubic for every original
moving-plane point and every cubic actor in the literal section centralizer. -/
theorem binary_three_source_moving_point_cubic
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : ChapterA.Section05To06.IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {I : Subgroup G} (hI : I ∈ d.Hplus) (htwo : OutsideStructure.RankTwoCase d I)
    (hf : HasCharacteristicTwo I) (c : ComponentWitness d I)
    (e : (c.L ⧸ pCore 2 c.L) ≃* PSL(3,ZMod 2))
    (b : BinaryMS.Input KnownSimple.IsKnownSimple
      (c.L.subgroupOf (c.L ⊔ d.S)) (d.S.subgroupOf (c.L ⊔ d.S)))
    (t : InputSetup b)
    (common : CommonFacts t.reduction.radical t.source t.geometry)
    (earlier : DistanceEight.CoreFactors.Earlier t.reduction.radical t.geometry)
    (A : Subgroup G) (hA : Nat.card A = 3)
    (hAL : A ≤ Chapter4.sectionCentralizer c.L)
    (z : G) (hz : z ∈ LinearThree.movingPlane d c.L) :
    ∃ a : c.L, orderOf (a : G) = 3 ∧ (a : G) ∈ centralizer (A : Set G) ∧
      (a : G) ∈ centralizer ({z} : Set G) ∧ a ∉ pCore 2 c.L := by
  obtain ⟨hW,hJ,hcore,_⟩ := source_lemma_15_3_16_local_geometry
    hG d hempty hM hu hmany hI htwo hf c
  let := hW
  obtain ⟨hne,hBaum,_⟩ := InitialSource.UniformControl.source_controls_of_ordering_maximal
    hG d.T hempty hM hu hmany (d.action.card_centralInvolutions d.T d.sylow_le)
  let eSL := e.trans (BinaryLinear.OuterCyclic.projectiveEquivSL (by decide))
  obtain ⟨_,h,hg⟩ := residual_geometry_of_original hG d hempty hM hu hmany hne hBaum
    hI c (OutsideStructure.rankTwoCase_three_rank hG d hI htwo) eSL hW hJ hcore
  exact movingPlane_point_cubic d c eSL h hg b t common earlier A hA hAL z hz

/-- Two independent commuting cubics in an original moving-plane point centralizer,
with the first actor supplied by the original residual geometry. -/
theorem binary_three_source_moving_point_commuting_cubics
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : ChapterA.Section05To06.IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {I : Subgroup G} (hI : I ∈ d.Hplus) (htwo : OutsideStructure.RankTwoCase d I)
    (hf : HasCharacteristicTwo I) (c : ComponentWitness d I)
    (e : (c.L ⧸ pCore 2 c.L) ≃* PSL(3,ZMod 2))
    (b : BinaryMS.Input KnownSimple.IsKnownSimple
      (c.L.subgroupOf (c.L ⊔ d.S)) (d.S.subgroupOf (c.L ⊔ d.S)))
    (t : InputSetup b)
    (common : CommonFacts t.reduction.radical t.source t.geometry)
    (earlier : DistanceEight.CoreFactors.Earlier t.reduction.radical t.geometry)
    (z : G) (hz : z ∈ LinearThree.movingPlane d c.L) :
    ∃ a : YC d c.L, ∃ v : c.L,
      orderOf (a : G) = 3 ∧ orderOf (v : G) = 3 ∧
      (a : G) ∈ centralizer ({z} : Set G) ∧
      (v : G) ∈ centralizer ({z} : Set G) ∧
      (a : G) * (v : G) = (v : G) * (a : G) ∧
      (v : G) ∉ Chapter4.sectionCentralizer c.L := by
  obtain ⟨hW,hJ,hcore,_⟩ := source_lemma_15_3_16_local_geometry
    hG d hempty hM hu hmany hI htwo hf c
  let := hW
  obtain ⟨hne,hBaum,_⟩ := InitialSource.UniformControl.source_controls_of_ordering_maximal
    hG d.T hempty hM hu hmany (d.action.card_centralInvolutions d.T d.sylow_le)
  let eSL := e.trans (BinaryLinear.OuterCyclic.projectiveEquivSL (by decide))
  obtain ⟨_,h,hg⟩ := residual_geometry_of_original hG d hempty hM hu hmany hne hBaum
    hI c (OutsideStructure.rankTwoCase_three_rank hG d hI htwo) eSL hW hJ hcore
  exact movingPlane_commuting_cubics d c eSL h hg b t common earlier z hz

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
