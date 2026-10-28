module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointCentralizerAction

/-!
# The original natural eight with its exact actor kernel

The marked MS93 center section is transported through the literal original
join inclusion. Its actor is the original component modulo precisely its
two-core. This kernel equality is needed when descending the seed action
to the unchanged smaller subgroup in the point quotient.
-/
public noncomputable section
open Subgroup Theory.GroupTheory Matrix
open scoped Pointwise MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
open LinearThree LinearThree.OriginalSource CoreActions ChapterC BinaryMS.MS93
open CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G]

/-- The original moving eight is naturally marked by an actor whose
kernel is exactly the original component two-core. -/
theorem binary_three_original_natural_seed
    (d : LocalData G) (L : Subgroup G)
    (b : BinaryMS.Input KnownSimple.IsKnownSimple
      (L.subgroupOf (L ⊔ d.S)) (d.S.subgroupOf (L ⊔ d.S)))
    (t : InputSetup b)
    (common : CommonFacts t.reduction.radical t.source t.geometry)
    (hb : 4 < t.geometry.b t.reduction.radical) :
    ∃ a : L →* SpecialLinearGroup (Fin 3) (ZMod 2), Function.Surjective a ∧ a.ker=pCore 2 L ∧
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
  exact ⟨a,ha,hk,HasSectionModel.of_subgroupOf (J := J) le_sup_left hVJ bot_le a _
    (by simpa only [bot_subgroupOf] using hs)⟩


private theorem descend_actor_through_two_kernel
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

/-- The same original natural seed descends to the actual smaller subgroup
of the point quotient, retaining both the original quotient map and its
precise actor two-core. -/
theorem binary_three_point_natural_seed
    (d : LocalData G) (L : Subgroup G)
    (b : BinaryMS.Input KnownSimple.IsKnownSimple
      (L.subgroupOf (L ⊔ d.S)) (d.S.subgroupOf (L ⊔ d.S)))
    (t : InputSetup b)
    (common : CommonFacts t.reduction.radical t.source t.geometry)
    (hb : 4 < t.geometry.b t.reduction.radical)
    (z : G) (hLC : L ≤ centralizer ({z} : Set G)) :
    let C := centralizer ({z} : Set G)
    let q := QuotientGroup.mk' (pCore 2 C)
    let B := (L.subgroupOf C).map q
    ∃ (f : L →* B) (β : B →* SpecialLinearGroup (Fin 3) (ZMod 2)),
      Function.Surjective f ∧
      (∀ l : L, (f l : C ⧸ pCore 2 C)=q ⟨l,hLC l.property⟩) ∧
      Function.Surjective β ∧ β.ker=pCore 2 B ∧
      HasSectionModel L (⁅coreCenter L,L⁆) ⊥ (β.comp f)
        (Representation.specialLinearNatural (k := ZMod 2) 3) := by
  let C := centralizer ({z} : Set G)
  let q := QuotientGroup.mk' (pCore 2 C)
  let B := (L.subgroupOf C).map q
  let f₀ := q.comp (inclusion hLC)
  have hr : f₀.range=B := by
    rw [MonoidHom.range_comp,inclusion_range]
  let E := MulEquiv.subgroupCongr hr
  let f := E.toMonoidHom.comp f₀.rangeRestrict
  have hf : Function.Surjective f := E.surjective.comp f₀.rangeRestrict_surjective
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
  obtain ⟨a,ha,hak,hmodel⟩ := binary_three_original_natural_seed d L b t common hb
  obtain ⟨β,hβ,hβk,hβf⟩ := descend_actor_through_two_kernel f hf hk a ha hak
  refine ⟨f,β,hf,fun _ => rfl,hβ,hβk,?_⟩
  rw [hβf]
  exact hmodel

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
