module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointNaturalSeed
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreeOriginalCoreSections

/-!
# One original marking for the seed and characteristic core layers

The natural eight and all three original characteristic sections use the
same literal MS93 quotient marking. Transport through the original join
inclusion before descending through the actual point map keeps this actor
synchronized, including its precise two-core kernel.

Source context: MS93 (4.5), Aschbacher--Smith 15.3.23.
-/
public noncomputable section
open Subgroup Theory.GroupTheory Matrix Stellmacher.PushingUp.AmalgamGraph
open scoped Pointwise MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
open LinearThree LinearThree.OriginalSource CoreActions Extension.SourceCases ChapterC BinaryMS.MS93
open CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve.ExchangedCases.SL3Geometry.SourceCases
local notation "sCenter" => CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.centerIn
variable {G : Type*} [Group G] [Finite G]

private theorem natural_seed_for_literal_actor
    (d : LocalData G) (L : Subgroup G)
    (b : BinaryMS.Input KnownSimple.IsKnownSimple
      (L.subgroupOf (L ⊔ d.S)) (d.S.subgroupOf (L ⊔ d.S)))
    (t : InputSetup b)
    (common : CommonFacts t.reduction.radical t.source t.geometry)
    (hb : 4 < t.geometry.b t.reduction.radical) :
    let i := subgroupOfEquivOfLe (show L ≤ L ⊔ d.S from le_sup_left)
    let a := (linearThreeActor (b.quotientEquiv.trans common.natural.marking)).comp i.symm.toMonoidHom
    Function.Surjective a ∧ a.ker=pCore 2 L ∧
      HasSectionModel L (⁅coreCenter L,L⁆) ⊥ a
        (Representation.specialLinearNatural (k := ZMod 2) 3) := by
  let J := L ⊔ d.S
  let Q₀ := BinaryMS.commutatorCore (L.subgroupOf J)
  have hmap : Q₀.map J.subtype = LinearThree.commutatorCore L :=
    sourceQ_map_subtype (show L ≤ J from le_sup_left) b.component
  have hms : msQ (L.subgroupOf J) (d.S.subgroupOf J) = Q₀ := by
    have hp : (⊤ : Subgroup J).pCoreIn 2 = pCore 2 J := pCore_map_iso 2 topEquiv
    rw [msQ,b.sup_eq_top,hp]
  have hs := (t.center_source_sections common hb).2.2.2
  change HasSectionModel (L.subgroupOf J)
    (⁅CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.centerIn
      (msQ (L.subgroupOf J) (d.S.subgroupOf J)),L.subgroupOf J⁆) ⊥ _ _ at hs
  rw [hms] at hs
  let V₀ := ⁅CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.centerIn Q₀,L.subgroupOf J⁆
  let V := ⁅coreCenter L,L⁆
  have hm : V₀.map J.subtype = V := by
    rw [map_commutator,map_subgroupOf_eq_of_le (show L ≤ J from le_sup_left)]
    change ⁅((center Q₀).map Q₀.subtype).map J.subtype,L⁆ = _
    rw [map_subgroup_center_eq _ J.subtype_injective,hmap]
    rfl
  have hVJ : V ≤ J := hm ▸ map_subtype_le _
  have hVsub : V₀ = V.subgroupOf J := by
    rw [←hm]
    exact (comap_map_eq_self_of_injective J.subtype_injective V₀).symm
  let i := subgroupOfEquivOfLe (show L ≤ J from le_sup_left)
  let π := linearThreeActor (b.quotientEquiv.trans common.natural.marking)
  let a := π.comp i.symm.toMonoidHom
  have ha : Function.Surjective a :=
    (b.quotientEquiv.trans common.natural.marking).surjective.comp
      ((QuotientGroup.mk'_surjective _).comp i.symm.surjective)
  have hπker : π.ker=pCore 2 (L.subgroupOf J) := by
    exact (MonoidHom.ker_comp_of_injective (QuotientGroup.mk' (pCore 2 (L.subgroupOf J)))
      (b.quotientEquiv.trans common.natural.marking).toMonoidHom
      (b.quotientEquiv.trans common.natural.marking).injective).trans (QuotientGroup.ker_mk' _)
  have hk : a.ker=pCore 2 L := by
    calc
      a.ker = π.ker.comap i.symm.toMonoidHom := rfl
      _ = (pCore 2 (L.subgroupOf J)).comap i.symm.toMonoidHom := congrArg _ hπker
      _ = (pCore 2 (L.subgroupOf J)).map i.toMonoidHom :=
        comap_equiv_eq_map_symm i.symm _
      _ = pCore 2 L := pCore_map_iso 2 i
  have hi : π = a.comp i.toMonoidHom := by
    apply MonoidHom.ext
    intro x
    exact congrArg π (i.symm_apply_apply x).symm
  change HasSectionModel (L.subgroupOf J) V₀ ⊥ π _ at hs
  rw [hVsub,hi] at hs
  exact ⟨ha,hk,HasSectionModel.of_subgroupOf (J := J) le_sup_left hVJ bot_le a _
    (by simpa only [bot_subgroupOf] using hs)⟩


private theorem core_sections_for_literal_actor
    (d : LocalData G) (L : Subgroup G)
    (b : BinaryMS.Input KnownSimple.IsKnownSimple
      (L.subgroupOf (L ⊔ d.S)) (d.S.subgroupOf (L ⊔ d.S)))
    (t : InputSetup b)
    (common : CommonFacts t.reduction.radical t.source t.geometry)
    (hb : 4 < t.geometry.b t.reduction.radical)
    (hfixed : core t.reduction.radical (alpha t.reduction.radical) ⊓ centralizer
      (Ltilde t.reduction.radical (alpha t.reduction.radical) : Set (FreeAmalgam t.reduction.radical)) =
        H t.reduction.radical (alpha t.reduction.radical)) :
    let i := subgroupOfEquivOfLe (show L ≤ L ⊔ d.S from le_sup_left)
    let a := (linearThreeActor (b.quotientEquiv.trans common.natural.marking)).comp i.symm.toMonoidHom
    let Q := LinearThree.commutatorCore L
    let Phi := frattiniIn Q
    let D := Q ⊓ centralizer (Phi : Set G)
    let v := Representation.specialLinearNatural (k := ZMod 2) 3
    HasSectionModel L Phi (sCenter Q) a v.dual ∧
      HasSectionModel L D Phi a (v.dual.prod v.dual) ∧
      HasSectionModel L Q D a (v.prod v) := by
  let J := L ⊔ d.S
  let Q := commutatorCore L
  have hQJ : Q ≤ J := (commutatorCore_le L).trans ((map_subtype_le _).trans le_sup_left)
  have hQ0 : msQ (L.subgroupOf J) (d.S.subgroupOf J) = Q.subgroupOf J := by
    apply Subgroup.map_injective J.subtype_injective
    have hms : msQ (L.subgroupOf J) (d.S.subgroupOf J) =
        BinaryMS.commutatorCore (L.subgroupOf J) := by
      have hp : (⊤ : Subgroup J).pCoreIn 2 = pCore 2 J := pCore_map_iso 2 topEquiv
      rw [msQ,b.sup_eq_top,hp]
    rw [hms,map_subgroupOf_eq_of_le hQJ]
    exact sourceQ_map_subtype (show L ≤ J from le_sup_left) b.component
  have hs := t.frattini_sectionModel_of_fixedFactor common hb hfixed
  obtain ⟨hm,ht⟩ := t.frattini_pairSectionModels_of_fixedFactor common hb hfixed
  change HasSectionModel (L.subgroupOf J)
    (frattiniIn (msQ (L.subgroupOf J) (d.S.subgroupOf J)))
    (CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.centerIn
      (msQ (L.subgroupOf J) (d.S.subgroupOf J))) _ _ at hs
  rw [hQ0,frattiniIn_subgroupOf hQJ,centerIn_subgroupOf hQJ] at hs
  have hPhiJ : frattiniIn Q ≤ J := (map_subtype_le (frattini Q)).trans hQJ
  have hDc : Q.subgroupOf J ⊓ centralizer ((frattiniIn Q).subgroupOf J : Set J) =
      (Q ⊓ centralizer (frattiniIn Q : Set G)).subgroupOf J := by
    ext x
    constructor
    · rintro ⟨hx,hc⟩
      exact ⟨hx,fun z hz => congrArg Subtype.val (hc ⟨z,hPhiJ hz⟩ hz)⟩
    · rintro ⟨hx,hc⟩
      exact ⟨hx,fun z hz => Subtype.ext (hc z hz)⟩
  change HasSectionModel (L.subgroupOf J)
    (msQ (L.subgroupOf J) (d.S.subgroupOf J) ⊓
      centralizer (frattiniIn (msQ (L.subgroupOf J) (d.S.subgroupOf J)) : Set J))
    (frattiniIn (msQ (L.subgroupOf J) (d.S.subgroupOf J))) _ _ at hm
  change HasSectionModel (L.subgroupOf J)
    (msQ (L.subgroupOf J) (d.S.subgroupOf J))
    (msQ (L.subgroupOf J) (d.S.subgroupOf J) ⊓
      centralizer (frattiniIn (msQ (L.subgroupOf J) (d.S.subgroupOf J)) : Set J)) _ _ at ht
  rw [hQ0,frattiniIn_subgroupOf hQJ,hDc] at hm ht
  let i := subgroupOfEquivOfLe (show L ≤ J from le_sup_left)
  let π := linearThreeActor (b.quotientEquiv.trans common.natural.marking)
  let a := π.comp i.symm.toMonoidHom
  have hactor : π = a.comp i.toMonoidHom := by
    apply MonoidHom.ext
    intro x
    exact congrArg π (i.symm_apply_apply x).symm
  change linearThreeActor (b.quotientEquiv.trans common.natural.marking) = a.comp i.toMonoidHom at hactor
  rw [hactor] at hs hm ht
  have hDJ : Q ⊓ centralizer (frattiniIn Q : Set G) ≤ J := inf_le_left.trans hQJ
  exact ⟨HasSectionModel.of_subgroupOf (J := J) le_sup_left hPhiJ
    ((map_subtype_le (center Q)).trans hQJ) a _ hs,
    HasSectionModel.of_subgroupOf (J := J) le_sup_left hDJ hPhiJ a _ hm,
    HasSectionModel.of_subgroupOf (J := J) le_sup_left hQJ hDJ a _ ht⟩


private theorem descend_synchronized_actor
    {A B H : Type*} [Group A] [Group B] [Group H] [Finite A] [Finite B]
    (f : A →* B) (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker)
    (a : A →* H) (ha : Function.Surjective a) (hak : a.ker=pCore 2 A) :
    ∃ β : B →* H, Function.Surjective β ∧ β.ker=pCore 2 B ∧ β.comp f=a := by
  have hle : f.ker ≤ a.ker := hak ▸ le_sSup ⟨inferInstance,hk⟩
  let e := QuotientGroup.quotientKerEquivOfSurjective f hf
  let β := (QuotientGroup.lift f.ker a hle).comp e.symm.toMonoidHom
  have hβf (x : A) : β (f x)=a x := by
    change QuotientGroup.lift f.ker a hle
      (e.symm (e (QuotientGroup.mk' f.ker x)))=a x
    rw [e.symm_apply_apply]
    rfl
  have he : β.comp f=a := MonoidHom.ext hβf
  have hβ : Function.Surjective β := by
    intro y
    obtain ⟨x,rfl⟩ := ha y
    exact ⟨f x,hβf x⟩
  have hβk : β.ker=pCore 2 B := by
    apply (Subgroup.comap_injective hf)
    change (β.comp f).ker=(pCore 2 B).comap f
    rw [he,hak,f.comap_pCore_of_ker_isPGroup hf hk]
  exact ⟨β,hβ,hβk,he⟩


/-- One original quotient marking simultaneously identifies the natural
seed and all three characteristic core sections, with exact actor kernel. -/
theorem binary_three_source_synchronized_sections
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
    (hc : ¬ IsMulCommutative (BinaryMS.commutatorCore (c.L.subgroupOf (c.L ⊔ d.S))))
    (hb : 4 < t.geometry.b t.reduction.radical) :
    ∃ a : c.L →* SpecialLinearGroup (Fin 3) (ZMod 2),
      Function.Surjective a ∧ a.ker=pCore 2 c.L ∧
      let Q := LinearThree.commutatorCore c.L
      let Phi := frattiniIn Q
      let D := Q ⊓ centralizer (Phi : Set G)
      let v := Representation.specialLinearNatural (k := ZMod 2) 3
      HasSectionModel c.L (⁅coreCenter c.L,c.L⁆) ⊥ a v ∧
      HasSectionModel c.L Phi (sCenter Q) a v.dual ∧
      HasSectionModel c.L D Phi a (v.dual.prod v.dual) ∧
      HasSectionModel c.L Q D a (v.prod v) := by
  obtain ⟨hW,hJ,hcore,_⟩ := source_lemma_15_3_16_local_geometry
    hG d hempty hM hu hmany hI htwo hf c
  obtain ⟨hne,hBaum,_⟩ := InitialSource.UniformControl.source_controls_of_ordering_maximal
    hG d.T hempty hM hu hmany (d.action.card_centralInvolutions d.T d.sylow_le)
  let eSL := e.trans (BinaryLinear.OuterCyclic.projectiveEquivSL (by decide))
  obtain ⟨_,h,hg⟩ := residual_geometry_of_original hG d hempty hM hu hmany hne hBaum
    hI c (OutsideStructure.rankTwoCase_three_rank hG d hI htwo) eSL hW hJ hcore
  obtain ⟨common⟩ := t.commonFacts hc
  have hi := d.action.planeStabilizer_index_two d.T d.sylow_le 1
  have hnot : ¬ (d.T : Subgroup G) ≤ d.S := by
    intro hTS
    have ht : d.S.subgroupOf (d.T : Subgroup G) = ⊤ := top_unique (fun x _ => hTS x.property)
    rw [ht,index_top] at hi
    omega
  obtain ⟨g,hgT,hgS⟩ := SetLike.not_le_iff_exists.mp hnot
  have hfixed := source_fixedFactor_eq_H_of_original_exchange
    d c.L eSL h hg b t common (DistanceEight.PathCentrality.Source44.OriginalEarlier.earlier common hb)
      g hgT hgS
  let i := subgroupOfEquivOfLe (show c.L ≤ c.L ⊔ d.S from le_sup_left)
  let a := (linearThreeActor (b.quotientEquiv.trans common.natural.marking)).comp i.symm.toMonoidHom
  obtain ⟨ha,hak,hseed⟩ := natural_seed_for_literal_actor d c.L b t common hb
  have hsections := core_sections_for_literal_actor d c.L b t common hb hfixed
  exact ⟨a,ha,hak,hseed,hsections⟩


/-- The synchronized original section marking descends to the actual
B=q(L), preserving q and the exact two-core actor kernel. -/
theorem binary_three_point_synchronized_sections
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
    (hc : ¬ IsMulCommutative (BinaryMS.commutatorCore (c.L.subgroupOf (c.L ⊔ d.S))))
    (hb : 4 < t.geometry.b t.reduction.radical)
    (z : G) (hLC : c.L ≤ centralizer ({z} : Set G)) :
    let C := centralizer ({z} : Set G)
    let q := QuotientGroup.mk' (pCore 2 C)
    let B := (c.L.subgroupOf C).map q
    ∃ (f : c.L →* B) (β : B →* SpecialLinearGroup (Fin 3) (ZMod 2)),
      Function.Surjective f ∧
      (∀ l : c.L, (f l : C ⧸ pCore 2 C)=q ⟨l,hLC l.property⟩) ∧
      Function.Surjective β ∧ β.ker=pCore 2 B ∧
      let Q := LinearThree.commutatorCore c.L
      let Phi := frattiniIn Q
      let D := Q ⊓ centralizer (Phi : Set G)
      let a := β.comp f
      let v := Representation.specialLinearNatural (k := ZMod 2) 3
      HasSectionModel c.L (⁅coreCenter c.L,c.L⁆) ⊥ a v ∧
      HasSectionModel c.L Phi (sCenter Q) a v.dual ∧
      HasSectionModel c.L D Phi a (v.dual.prod v.dual) ∧
      HasSectionModel c.L Q D a (v.prod v) := by
  let C := centralizer ({z} : Set G)
  let q := QuotientGroup.mk' (pCore 2 C)
  let B := (c.L.subgroupOf C).map q
  let f₀ := q.comp (inclusion hLC)
  have hr : f₀.range=B := by
    rw [MonoidHom.range_comp,inclusion_range]
  let E := MulEquiv.subgroupCongr hr
  let f := E.toMonoidHom.comp f₀.rangeRestrict
  have hfs : Function.Surjective f := E.surjective.comp f₀.rangeRestrict_surjective
  have hfk : f.ker=(pCore 2 C).comap (inclusion hLC) := by
    have he := MonoidHom.ker_comp_of_injective f₀.rangeRestrict E.toMonoidHom E.injective
    calc
      f.ker = f₀.rangeRestrict.ker := he
      _ = f₀.ker := MonoidHom.ker_rangeRestrict f₀
      _ = q.ker.comap (inclusion hLC) := rfl
      _ = (pCore 2 C).comap (inclusion hLC) := congrArg _ (QuotientGroup.ker_mk' _)
  have hk : IsPGroup 2 f.ker := by
    rw [hfk]
    exact pCore_isPGroup.comap_of_injective _ (inclusion_injective hLC)
  obtain ⟨a,ha,hak,hmodels⟩ := binary_three_source_synchronized_sections
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb
  obtain ⟨β,hβ,hβk,hβf⟩ := descend_synchronized_actor f hfs hk a ha hak
  refine ⟨f,β,hfs,fun _ => rfl,hβ,hβk,?_⟩
  rw [hβf]
  exact hmodels

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
