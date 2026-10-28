module
public import CFSG.Quasithin.Chapter2.Section05.Overcomponents.Prime.Rows
public import Theory.SpecificGroups.PSL3Even.InvolutionResidualRows.ComponentFixer
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.OuterInvolutionCentralizer.ComponentFixer
public import Theory.GroupAction.CommutingFixedComponentFixer
public import Theory.GroupAction.FixedComponentNormalizer

/-!
# The unique fixed component and its two-element fixer in the retained prime rows

The PSL3(4) field and J2 outer rows have a unique ordinary fixed component and a commuting pointwise fixer of order at most two. Descent through the literal containing center transfers that bound to the original source component.

Source: Aschbacher–Smith 2.5.19, printed pp.560–563.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter2.Section05.Overcomponents.PrimeRows

private theorem component_unique_of_simple {Q : Type*} [Group Q] [IsSimpleGroup Q]
    (B C : Subgroup Q) (hB : IsComponent Q B) (hC : IsComponent Q C) : B = C := by
  have ht (D : Subgroup Q) (hD : IsComponent Q D) : D = ⊤ := by
    rcases hD.1.eq_bot_or_top_of_isSimpleGroup inferInstance with hb | ht
    · have hs : Group.IsSolvable D := by rw [hb]; infer_instance
      exact (hD.isCComponent.not_isSolvable hs).elim
    · exact ht
  exact (ht B hB).trans (ht C hC).symm

theorem prime_fixed_quotient_component_unique
    {Q : Type*} [Group Q] [Finite Q] (a : MulAut Q) (ha : orderOf a = 2)
    (hm : PrimeFixedQuotientModels Q a)
    (B C : Subgroup a.fixedSubgroup)
    (hB : IsComponent a.fixedSubgroup B) (hC : IsComponent a.fixedSubgroup C) : B = C := by
  rcases hm with ⟨F,_,_,hF,e,hfield⟩ | ⟨e,ho⟩
  · let b := MulAut.congr e a
    let f := MulAut.compatibleFixedSubgroupCongr e a
    have hBt := Matrix.PSL3Even.InvolutionResidualRows.field_case_component_eq_top
      b hfield (B.map f.toMonoidHom) (hB.map_equiv f)
    have hCt := Matrix.PSL3Even.InvolutionResidualRows.field_case_component_eq_top
      b hfield (C.map f.toMonoidHom) (hC.map_equiv f)
    exact map_injective f.injective (hBt.trans hCt.symm)
  · let b := MulAut.congr e a
    let f := MulAut.compatibleFixedSubgroupCongr e a
    have hb : orderOf b = 2 := ((MulAut.congr e).orderOf_eq a).trans ha
    have hbo : b ∉ (MulAut.conj : Sporadic.LeechRelated.J2.Carrier →* _).range := by
      rintro ⟨g,hg⟩
      apply ho (e.symm g)
      apply (MulAut.congr e).injective
      rw [MulAut.congr_conj,e.apply_symm_apply]
      exact hg.symm
    obtain ⟨d⟩ := Sporadic.LeechRelated.J2.OuterInvolutionCentralizer.outer_fixed_equiv b hb hbo
    have hBt := Sporadic.LeechRelated.J2.OuterInvolutionCentralizer.component_map_eq_inner
      b d (B.map f.toMonoidHom) (hB.map_equiv f)
    have hCt := Sporadic.LeechRelated.J2.OuterInvolutionCentralizer.component_map_eq_inner
      b d (C.map f.toMonoidHom) (hC.map_equiv f)
    exact map_injective f.injective (map_injective d.injective (hBt.trans hCt.symm))

theorem prime_fixed_quotient_componentIn_unique
    {Q : Type*} [Group Q] [Finite Q] (a : MulAut Q) (ha : orderOf a = 2)
    (hm : PrimeFixedQuotientModels Q a)
    (B C : Subgroup Q) (hB : IsComponentIn B a.fixedSubgroup)
    (hC : IsComponentIn C a.fixedSubgroup) : B = C := by
  have he := prime_fixed_quotient_component_unique a ha hm
    (B.subgroupOf a.fixedSubgroup) (C.subgroupOf a.fixedSubgroup) hB.2 hC.2
  have hh := congrArg (map a.fixedSubgroup.subtype) he
  simpa only [map_subgroupOf_eq_of_le hB.1,map_subgroupOf_eq_of_le hC.1] using hh

theorem prime_fixed_quotient_fixer_card_le_two
    {Q : Type*} [Group Q] [Finite Q] (a : MulAut Q) (ha : orderOf a = 2)
    (hm : PrimeFixedQuotientModels Q a)
    (B : Subgroup a.fixedSubgroup) (hB : IsComponent a.fixedSubgroup B) :
    Nat.card (MulAut.commutingFixedComponentFixer a B) ≤ 2 := by
  rcases hm with ⟨F,_,_,hF,e,hfield⟩ | ⟨e,ho⟩
  · let f := MulAut.compatibleFixedSubgroupCongr e a
    have hcard := Matrix.PSL3Even.InvolutionResidualRows.field_case_commuting_component_fixer_card_le_two
      (by decide : 0 < 2) (by simpa using hF) (MulAut.congr e a)
      (((MulAut.congr e).orderOf_eq a).trans ha) hfield
      (B.map f.toMonoidHom) (hB.map_equiv f)
    exact (MulAut.commutingFixedComponentFixer_card_le_of_equiv a B e).trans hcard
  · let b := MulAut.congr e a
    let f := MulAut.compatibleFixedSubgroupCongr e a
    have hb : orderOf b = 2 := ((MulAut.congr e).orderOf_eq a).trans ha
    have hbo : b ∉ (MulAut.conj : Sporadic.LeechRelated.J2.Carrier →* _).range := by
      rintro ⟨g,hg⟩
      apply ho (e.symm g)
      apply (MulAut.congr e).injective
      rw [MulAut.congr_conj,e.apply_symm_apply]
      exact hg.symm
    have hcard := Sporadic.LeechRelated.J2.OuterInvolutionCentralizer.commuting_component_fixer_card_le_two
      b hb hbo (B.map f.toMonoidHom) (hB.map_equiv f)
    exact (MulAut.commutingFixedComponentFixer_card_le_of_equiv a B e).trans hcard

open ComponentRefinement ComponentSelection

theorem source_prime_quotient_fixer_card_le_two
    {G : Type*} [Group G] [Finite G]
    {H K M : Subgroup G} {S : Sylow 2 H} {z : G}
    (c : MathieuSourceSetup H K M S z)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (hb : ¬ ClassificationModels.IsBenderModel K)
    {E : Type*} [Group E] [Finite E] [Group.IsPerfect E]
    (a : MulAut E) (ha : orderOf a = 2)
    (B : Subgroup a.fixedSubgroup) (hB : IsComponent a.fixedSubgroup B) (eK : K ≃* B)
    (hm : PrimeFixedQuotientModels (E ⧸ center E) (quotientAut (center E) a)) :
    Nat.card (MulAut.commutingFixedComponentFixer a B) ≤ 2 := by
  obtain ⟨hc,haq,hC,_⟩ := source_fixed_component_central_quotient
    c hG hempty hgen hb a ha B hB eK
  have hcard := prime_fixed_quotient_fixer_card_le_two _ haq hm _ hC
  exact (MulAut.commutingFixedComponentFixer_card_le_quotient a B (MulEquiv.refl _)).trans hcard

end CFSG.Quasithin.Chapter2.Section05.Overcomponents.PrimeRows
