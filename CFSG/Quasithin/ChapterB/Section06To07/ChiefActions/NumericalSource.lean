module
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.NaturalSource
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.PairResidual
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.PairSymmetric.NoStrong
public import Theory.Representation.SL2NaturalOffenders.NaturalPair
public import Theory.Representation.BinaryOffender.RatioFromStrong
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceCompletion.BinaryConstituents
public import CFSG.Quasithin.ChapterB.Section06To07.ChiefActions
/-!
# The faithful minimal-parabolic numerical source

This module proves the B.6.9 numerical bound for a faithful irreducible binary
action when the acting group and module use the same universe.  A hypothetical
ratio below one gives a strong offender.  The existing source induction splits
its quasisimple offender section into the literal rank-one and paired models;
those model theorems force ratio one or contradict strongness.  The argument
uses no model classification premise in its public theorem.

Source: Aschbacher--Smith B.6.9(1), printed p.115.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative ENNReal
namespace CFSG.Quasithin.ChapterB
open SourceInduction QuasisimpleSource
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
private theorem section_ratio
    (ρ : Representation (ZMod 2) G V)
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (hff : IsFFModule ρ) (hcore : pCore 2 G = ⊥)
    (hq : IsQuasisimple (generalizedFitting (offenderSubgroup ρ)))
    (c : ProjectiveLine.QuasisimpleSourceConclusion
      (ρ.comp (offenderSubgroup ρ).subtype) (generalizedFitting (offenderSubgroup ρ))) :
    quadraticRatio c.sectionData.action = 1 := by
  have hi := source_offender_quasisimple_irreducible ρ T hP hff hcore hq c
  have h3 := source_offender_quasisimple_three_exclusions ρ T hP hff hcore hq c
  have hb := source_offender_quasisimple_binary_rows_excluded ρ T hP hff hcore hq c
  have hsp := source_offender_quasisimple_symplectic_exclusion ρ T hP hff hcore hq c
  have h6 := source_offender_quasisimple_six_exclusions ρ T hP hff hcore hq c
  have h8 (e : generalizedFitting (offenderSubgroup ρ) ≃* alternatingGroup (Fin 8)) : False := by
    apply source_offender_quasisimple_not_binary_linear ρ T hP hff hcore hq (Or.inl rfl)
    exact ⟨e.trans (Atlas.Order20160A8.sl4TwoEquivPSL.trans
      Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8).symm⟩
  cases hi.2.2.2 with
  | linearTwo F hgen e ho hr => exact hr
  | linearThree F hgen e hr => exact (h3.1 F ⟨e⟩).elim
  | symplectic F hF hgen e hr => exact (hsp F hF ⟨e⟩).elim
  | symplecticTwo e hr => exact (h6.2 ⟨e⟩).elim
  | g2 F hF hgen e ho hr => exact hr
  | g2Two e ho hr => exact hr
  | symmetric n hn e ho hr => exact hr
  | alternatingSix hgen e ho hr => exact hr
  | alternatingSeven hgen hw e hd ho hr => exact hr
  | tripleSix hgen a hr => exact hr
  | binaryLinear d hd hgen e hr => exact (hb.1 d hd ⟨e⟩).elim
  | orthogonalSix hgen hw e ho hr => exact hr
  | symmetricEight hw e hr => exact (h8 e.subgroupEquiv).elim
  | exteriorFive hgen hw e hd ho hr => exact hr

private theorem section_not_strong
    (ρ : Representation (ZMod 2) G V)
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (hff : IsFFModule ρ) (hcore : pCore 2 G = ⊥)
    (hq : IsQuasisimple (generalizedFitting (offenderSubgroup ρ)))
    (c : ProjectiveLine.QuasisimpleSourceConclusion
      (ρ.comp (offenderSubgroup ρ).subtype) (generalizedFitting (offenderSubgroup ρ))) :
    ¬ IsStrongFFModule ρ := by
  apply not_strong_of_offenderSubgroup ρ
  rintro ⟨A,hA⟩
  have hq := section_ratio ρ T hP hff hcore hq c
  have hns : ¬ IsStrongFFModule c.sectionData.action := by
    rw [isStrongFFModule_iff_quadraticRatio_lt_one, hq]
    exact lt_irrefl _
  have h₁ := fixedCodim_quotient_add_subrepresentation_le
    c.sectionData.space.toRepresentation c.sectionData.central A
  have h₂ := fixedCodim_subrepresentation_le
    (ρ.comp (offenderSubgroup ρ).subtype) c.sectionData.space A
  exact hns ⟨A,hA.1,(Nat.le_add_right _ _).trans h₁ |>.trans h₂ |>.trans_lt hA.2⟩
private theorem symmetric_not_strong
    (ρ : Representation (ZMod 2) G V)
    (d : SourceTwoFactorCase (ρ.comp (offenderSubgroup ρ).subtype))
    (c : d.MarkedProduct (BinaryPermutation.naturalRepresentation (Fin 5))) :
    ¬ IsStrongFFModule ρ :=
  SourceTwoFactorCase.MarkedProduct.symmetric_not_strong ρ d c

private theorem pair_not_strong (ρ : Representation (ZMod 2) G V)
    (d : SourceTwoFactorCase (ρ.comp (offenderSubgroup ρ).subtype))
    (F : BinaryField) (c : d.MarkedProduct (linearNatural F 2)) :
    ¬ IsStrongFFModule ρ := by
  apply not_strong_of_offenderSubgroup ρ
  apply SL2NaturalOffenders.not_strong_of_naturalPair_quotient
    (ρ.comp (offenderSubgroup ρ).subtype) c.action.groupEquiv.toMonoidHom
    c.action.groupEquiv.injective c.quotientMap c.quotientMap_surjective
  intro g v
  exact c.quotientMap_action g v
universe u
variable {H W : Type u} [Group H] [Finite H] [AddCommGroup W]
  [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]

/-- B.6.9(1), in the faithful source convention. -/
public theorem minimalParabolic_faithful_quadraticRatio_ge_one
    (hH : IsSQTK KnownSimple.IsKnownSimple H)
    (T : Sylow 2 H) (hP : IsMinimalParabolicOver T ⊤)
    (ρ : Representation (ZMod 2) H W)
    [Representation.IsIrreducible ρ]
    (hfaith : Function.Injective ρ) :
    1 ≤ quadraticRatio (imageRepresentation ρ) := by
  have hcore : pCore 2 H = ⊥ := by
    have hk := normal_p_subgroup_le_ker ρ (pCore 2 H) pCore_isPGroup
    exact bot_unique (hk.trans ((MonoidHom.ker_eq_bot_iff _).mpr hfaith).le)
  by_contra hlt
  have hltρ : quadraticRatio ρ < 1 := by
    rw [← QuasisimpleSource.SourceCompletion.image_ratio_of_faithful ρ hfaith]
    exact lt_of_not_ge hlt
  have hstrong : IsStrongFFModule ρ :=
    (isStrongFFModule_iff_quadraticRatio_lt_one ρ).mpr hltρ
  have hff : IsFFModule ρ := by
    obtain ⟨A,hA⟩ := hstrong
    exact ⟨A, ⟨hA.1, hA.2.le⟩⟩
  by_cases hs : Group.IsSolvable H
  · exact (not_lt_of_ge (solvable_irreducible_image_ratio_ge_one ρ hs)) (lt_of_not_ge hlt)
  · let c : SQTKQuotient KnownSimple.IsKnownSimple H := {
      Cover := H
      kernel := (MonoidHom.id H).ker
      sqtk := hH
      equiv := QuotientGroup.quotientKerEquivOfSurjective (MonoidHom.id H)
        (fun x => ⟨x, rfl⟩) }
    have hsrc := nonsolvable_offender_natural_source ρ T hP hs hfaith hff hcore ⟨c⟩
    rcases hsrc with ⟨hqs,⟨c,_⟩⟩ | ⟨d,hd₁,hd₂⟩
    · exact (section_not_strong ρ T hP hff hcore hqs c) hstrong
    · obtain ⟨_,_,_,hmodel⟩ := source_offender_two_factor_shared_natural
        ρ T hP hff hcore d
      rcases hmodel with ⟨F,⟨c⟩⟩ | ⟨c⟩
      · exact (pair_not_strong ρ _ F c) hstrong
      · obtain ⟨c⟩ := c
        exact (SourceTwoFactorCase.MarkedProduct.symmetric_not_strong ρ _ c) hstrong
end CFSG.Quasithin.ChapterB
