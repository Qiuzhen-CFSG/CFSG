module
public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.Classification.TwoFactorSpaces

/-!
# Natural product rows on the original moved module

The actual component is oriented into one factor of B.5.6(3). Its natural
SL2 quotient gives PSL2(4); the single and doubled SL3 quotients give one or
two natural copies. A nonzero kernel in the single-natural row instead
gives rank four. Its fixed supplement and B.4.8(2) identify Sylow-fixed
vectors with component-fixed vectors, proving that the original Omega_1
Z(T) centralizes L.

The literal source consumer retains only the S5 deleted quotient and the
exceptional upper four-space rows, with their full original product records.
Those rows are not claimed as established markings here.

Source: Aschbacher--Smith 13.1.10, pp.871--872; B.5.6(3), p.105.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.Classification
open Chapter1 Chapter1.Section02 Chapter12.Section02 ChapterB.SourceInduction
open ChapterB.QuasisimpleSource
universe u
variable {G : Type u} [Group G] [Finite G]

open Stellmacher

/-- A natural-three moved section with a fixed supplement centralizes the
original Sylow omega-center in its nonsplit rank-four case. -/
theorem sectionThree_omega_central
    {T : Sylow 2 G} (h : Hypothesis1311 T)
    (_hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {L : Subgroup G} (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L))
    (hmove : L = ⁅L, ChapterB.thompsonJ (T : Subgroup G) 0⁆)
    (s : MovedSection
      ((reducedRepresentation L).comp (offenderSubgroup (reducedRepresentation L)).subtype)
      ((NormalizerReducedAction.componentImage L).subgroupOf
        (offenderSubgroup (reducedRepresentation L))))
    (hi : IsIrrPlus
      ((reducedRepresentation L).comp (offenderSubgroup (reducedRepresentation L)).subtype)
      ((NormalizerReducedAction.componentImage L).subgroupOf
        (offenderSubgroup (reducedRepresentation L))) s.space.toSubmodule)
    (hz : s.central.toSubmodule ≠ ⊥)
    (a : ActionEquiv (s.action.comp
      ((NormalizerReducedAction.componentImage L).subgroupOf
        (offenderSubgroup (reducedRepresentation L))).subtype) (linearNatural BinaryField.two 3))
    (hs : s.space.toSubmodule ⊔ fixedSpace
      ((reducedRepresentation L).comp (offenderSubgroup (reducedRepresentation L)).subtype)
      ((NormalizerReducedAction.componentImage L).subgroupOf
        (offenderSubgroup (reducedRepresentation L))) = ⊤) :
    ⁅omegaOneCenterAmbient (T : Subgroup G), L⁆ = ⊥ := by
  have hTL := radicalLocal_invariant_source hL.1.1
    (uniqueness_local_quotient_sqtk h.simpleQTKE hL.1.1.2.2) hn
  have hj := componentImage_le_reducedOffender h hL hn hmove
  let C := NormalizerReducedAction.componentImage L
  let : C.Normal := reducedComponent_normal L
  let J := offenderSubgroup (reducedRepresentation L)
  let eK := subgroupOfEquivOfLe hj
  let E : C ≃* BinaryLinearThree.Group := eK.symm.trans a.groupEquiv
  let P := (T.subtype hTL).mapSurjective (f := NormalizerReducedAction.quotient L)
    (QuotientGroup.mk'_surjective _)
  obtain ⟨Q,hQ⟩ := P.exists_sylow_map_eq_inf_of_normal C
  let S : Sylow 2 BinaryLinearThree.Group := Q.mapSurjective (f := E.toMonoidHom) E.surjective
  apply commutator_eq_bot_iff_le_centralizer.mpr
  intro z hzT l hl
  have hzr := (source_omega_le_reduced h hL hn) hzT
  rw [normalizerReduced_eq] at hzr
  obtain ⟨z0,hz0,hz0eq⟩ := hzr
  change (z0 : G) = z at hz0eq
  let v : Additive (NormalizerReducedAction.Core L) := Additive.ofMul ⟨z0,hz0⟩
  have hv : ∀ g : S,
      ((reducedRepresentation L).comp J.subtype) (a.groupEquiv.symm (g : BinaryLinearThree.Group)) v = v := by
    intro g
    have hg : (g : BinaryLinearThree.Group) ∈ (Q : Subgroup C).map E.toMonoidHom := g.property
    obtain ⟨k,hk,hkg⟩ := hg
    have hkP : (k : NormalizerReducedAction.Star L) ∈ P := by
      have hh : (k : NormalizerReducedAction.Star L) ∈ (Q : Subgroup C).map C.subtype := ⟨k,hk,rfl⟩
      rw [hQ] at hh
      exact hh.1
    obtain ⟨t,ht,het⟩ := hkP
    have htT : (t : G) ∈ T := ht
    have hact : (((a.groupEquiv.symm (g : BinaryLinearThree.Group) : C.subgroupOf J) : J) :
        NormalizerReducedAction.Star L) = NormalizerReducedAction.quotient L t := by
      rw [← hkg]
      change ((eK (a.groupEquiv.symm (a.groupEquiv (eK.symm k))) : C) :
        NormalizerReducedAction.Star L) = _
      rw [a.groupEquiv.symm_apply_apply, eK.apply_symm_apply]
      exact het.symm
    have htfix : reducedRepresentation L (NormalizerReducedAction.quotient L t) v = v := by
      apply Additive.toMul.injective
      apply Subtype.ext
      apply Subtype.ext
      have hc : (t : G) * (z0 : G) = (z0 : G) * (t : G) := by
        rw [hz0eq]
        exact ((mem_omegaOneCenterAmbient_iff _ _).mp hzT).2.2 t htT
      exact (congrArg Subtype.val (reducedRepresentation_apply L t v)).trans
        (mul_inv_eq_iff_eq_mul.mpr hc)
    exact (congrArg (fun k => reducedRepresentation L k v) hact).trans htfix
  have hf := ProductMarkings.three_fixed_of_sylow s hi a hz hs S v hv
  have he := hf (eK.symm (reducedComponentMap L ⟨l,hl⟩))
  change reducedRepresentation L (NormalizerReducedAction.componentMap L ⟨l,hl⟩) v = v at he
  rw [NormalizerReducedAction.componentMap_eq] at he
  have he1 := congrArg Subtype.val
    (reducedRepresentation_apply L (inclusion L.le_normalizer ⟨l,hl⟩) v)
  change reducedRepresentation L
    (NormalizerReducedAction.quotient L (inclusion L.le_normalizer ⟨l,hl⟩)) v = v at he
  rw [he] at he1
  have he0 : l * (z0 : G) = (z0 : G) * l := mul_inv_eq_iff_eq_mul.mp he1.symm
  rw [hz0eq] at he0
  exact he0

/-- The linear-two product row constructs the genuine natural quotient
marking on the original moved subgroup. -/
theorem twoFactors_linearTwo_marked
    {T : Sylow 2 G} (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {L : Subgroup G} (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L))
    (hmove : L = ⁅L, ChapterB.thompsonJ (T : Subgroup G) 0⁆)
    (d : SourceTwoFactorCase ((reducedRepresentation L).comp
      (offenderSubgroup (reducedRepresentation L)).subtype))
    (hle : (NormalizerReducedAction.componentImage L).subgroupOf
      (offenderSubgroup (reducedRepresentation L)) ≤ d.first)
    (hm : d.firstSpace.toSubmodule = moved ((reducedRepresentation L).comp
      (offenderSubgroup (reducedRepresentation L)).subtype) d.first)
    (F : BinaryField)
    (a : ActionEquiv (((fixed ((reducedRepresentation L).comp
      (offenderSubgroup (reducedRepresentation L)).subtype)).quotientImage d.firstSpace).toRepresentation.comp
      d.first.subtype) (linearNatural F 2)) : Nonempty (FourWayMarking.{u,u} T L) := by
  have hTL := radicalLocal_invariant_source hL.1.1
    (uniqueness_local_quotient_sqtk h.simpleQTKE hL.1.1.2.2) hn
  let : IsElementaryAbelian 2 (normalizerMoved L) :=
    (faithful_maximal_normalizer_moved h.simpleQTKE hL hTL).1
  have hj := componentImage_le_reducedOffender h hL hn hmove
  let C := (NormalizerReducedAction.componentImage L).subgroupOf
    (offenderSubgroup (reducedRepresentation L))
  let : (NormalizerReducedAction.componentImage L).Normal := reducedComponent_normal L
  let : C.Normal := inferInstance
  have hC := reducedOffender_component h hmany hL hn hmove
  let : IsQuasisimple C := hC.2
  have hCA := ProductMarkings.component_eq_linearTwo hC hle F a.groupEquiv
  let s := MovedSection.ofNormal ((reducedRepresentation L).comp
    (offenderSubgroup (reducedRepresentation L)).subtype) C
  let b := composeAction (ProductMarkings.twoFactors_sectionImage d s hCA hm) a
  let e := (subgroupOfEquivOfLe hj).trans (reducedImageEquivMovedImage h hmany hL hn)
  obtain ⟨p,hp,hp3,hmodel⟩ := moved_component_pslTwo h hmany hL hn
  have hr := (prime_model_ranks hp hp3 (hmodel.of_mulEquiv e)).1
  exact ⟨.pslTwoFour (irreducibleFourMarking h hmany hL hn hmove s F
    (selected_two_degree F b.groupEquiv hr) b)⟩

/-- The single-natural SL3 quotient row constructs either a natural marking
or the rank-four marking with centralization of the original Omega center. -/
theorem twoFactors_linearThree_marked
    {T : Sylow 2 G} (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {L : Subgroup G} (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L))
    (hmove : L = ⁅L, ChapterB.thompsonJ (T : Subgroup G) 0⁆)
    (d : SourceTwoFactorCase ((reducedRepresentation L).comp
      (offenderSubgroup (reducedRepresentation L)).subtype))
    (hle : (NormalizerReducedAction.componentImage L).subgroupOf
      (offenderSubgroup (reducedRepresentation L)) ≤ d.first)
    (hm : d.firstSpace.toSubmodule = moved ((reducedRepresentation L).comp
      (offenderSubgroup (reducedRepresentation L)).subtype) d.first)
    (F : BinaryField) (ho : Odd F.degree)
    (a : ActionEquiv (((fixed ((reducedRepresentation L).comp
      (offenderSubgroup (reducedRepresentation L)).subtype)).quotientImage d.firstSpace).toRepresentation.comp
      d.first.subtype) (linearNatural F 3)) : Nonempty (FourWayMarking.{u,u} T L) := by
  have hTL := radicalLocal_invariant_source hL.1.1
    (uniqueness_local_quotient_sqtk h.simpleQTKE hL.1.1.2.2) hn
  let : IsElementaryAbelian 2 (normalizerMoved L) :=
    (faithful_maximal_normalizer_moved h.simpleQTKE hL hTL).1
  have hj := componentImage_le_reducedOffender h hL hn hmove
  let C := (NormalizerReducedAction.componentImage L).subgroupOf
    (offenderSubgroup (reducedRepresentation L))
  let : (NormalizerReducedAction.componentImage L).Normal := reducedComponent_normal L
  let : C.Normal := inferInstance
  have hC := reducedOffender_component h hmany hL hn hmove
  let : IsQuasisimple C := hC.2
  have hCA := ProductMarkings.component_eq_linearThree hC hle F ho a.groupEquiv
  let s := MovedSection.ofNormal ((reducedRepresentation L).comp
    (offenderSubgroup (reducedRepresentation L)).subtype) C
  let a' := composeAction (ProductMarkings.twoFactors_sectionImage d s hCA hm) a
  let e := (subgroupOfEquivOfLe hj).trans (reducedImageEquivMovedImage h hmany hL hn)
  obtain ⟨p,hp,hp3,hmodel⟩ := moved_component_pslTwo h hmany hL hn
  have hr := (prime_model_ranks hp hp3 (hmodel.of_mulEquiv e)).1
  let b := composeAction a' (ExtensionConsequences.degreeOneNaturalEquiv F
    (ProductMarkings.linearThree_degree F ho a'.groupEquiv hr) 3)
  rcases singleThree_marked_or_central h hmany hL hn hmove s ⟨b⟩ with hb | hz
  · exact hb
  · have hi := s.irrPlus_of_irreducible (ExtensionConsequences.irreducible_of_equiv b
      (ExtensionConsequences.linearNatural_irreducible BinaryField.two (by decide : 2 ≤ 3)))
    have hs : s.space.toSubmodule ⊔ fixedSpace ((reducedRepresentation L).comp
        (offenderSubgroup (reducedRepresentation L)).subtype) C = ⊤ := by
      have he : s.space.toSubmodule = d.firstSpace.toSubmodule :=
        s.space_eq.trans (by rw [show C = d.first from hCA]; exact hm.symm)
      rw [he]
      exact ProductMarkings.twoFactors_supplement d hCA.le
    let eg := (reducedImageEquivMovedImage h hmany hL hn).symm.trans
      ((subgroupOfEquivOfLe hj).symm.trans b.groupEquiv)
    exact ⟨.linearThreeRankFour {
      common := CommonMarking.of_source h hmany hL hn hmove
      image_model := ⟨ZMod 2,inferInstance,inferInstance,by simp,
        ⟨eg.trans (BinaryLinear.OuterCyclic.projectiveEquivSL (by decide : 0 < 3)).symm⟩⟩
      rank_four := singleThree_central_rank_four h hmany hL hn hmove s hi hz b
      omega_center_central := sectionThree_omega_central h hmany hL hn hmove s hi hz b hs }⟩

/-- The doubled quotient row has no hidden fixed kernel: the descended offender
bounds the original moved space by the quotient's six dimensions. -/
theorem twoFactors_doubleThree_marked
    {T : Sylow 2 G} (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {L : Subgroup G} (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L))
    (hmove : L = ⁅L, ChapterB.thompsonJ (T : Subgroup G) 0⁆)
    (d : SourceTwoFactorCase ((reducedRepresentation L).comp
      (offenderSubgroup (reducedRepresentation L)).subtype))
    (hle : (NormalizerReducedAction.componentImage L).subgroupOf
      (offenderSubgroup (reducedRepresentation L)) ≤ d.first)
    (hm : d.firstSpace.toSubmodule = moved ((reducedRepresentation L).comp
      (offenderSubgroup (reducedRepresentation L)).subtype) d.first)
    (F : BinaryField) (ho : Odd F.degree)
    (a : ActionEquiv (((fixed ((reducedRepresentation L).comp
      (offenderSubgroup (reducedRepresentation L)).subtype)).quotientImage d.firstSpace).toRepresentation.comp
      d.first.subtype) (repeated (linearNatural F 3) 2)) : Nonempty (FourWayMarking.{u,u} T L) := by
  have hTL := radicalLocal_invariant_source hL.1.1
    (uniqueness_local_quotient_sqtk h.simpleQTKE hL.1.1.2.2) hn
  let : IsElementaryAbelian 2 (normalizerMoved L) :=
    (faithful_maximal_normalizer_moved h.simpleQTKE hL hTL).1
  have hj := componentImage_le_reducedOffender h hL hn hmove
  let C := (NormalizerReducedAction.componentImage L).subgroupOf
    (offenderSubgroup (reducedRepresentation L))
  let : (NormalizerReducedAction.componentImage L).Normal := reducedComponent_normal L
  let : C.Normal := inferInstance
  have hC := reducedOffender_component h hmany hL hn hmove
  let : IsQuasisimple C := hC.2
  have hCA := ProductMarkings.component_eq_linearThree hC hle F ho a.groupEquiv
  let s := MovedSection.ofNormal ((reducedRepresentation L).comp
    (offenderSubgroup (reducedRepresentation L)).subtype) C
  let a' := composeAction (ProductMarkings.twoFactors_sectionImage d s hCA hm) a
  let e := (subgroupOfEquivOfLe hj).trans (reducedImageEquivMovedImage h hmany hL hn)
  obtain ⟨p,hp,hp3,hmodel⟩ := moved_component_pslTwo h hmany hL hn
  have hr := (prime_model_ranks hp hp3 (hmodel.of_mulEquiv e)).1
  let b := composeAction a' (ExtensionConsequences.degreeOneRepeatedEquiv F
    (ProductMarkings.linearThree_degree F ho a'.groupEquiv hr) 3 2)
  let : Nontrivial C := (Subgroup.nontrivial_iff_ne_bot C).mpr hC.isCComponent.ne_bot
  have hFF := ProductMarkings.twoFactors_moved_ff d
    (reducedOffender_hypothesis h hL hn).generated s hCA hm
  have hz := ProductMarkings.doubled_section_central_eq_bot s b hFF
  exact ⟨.linearThree (repeatedThreeMarking h hmany hL hn hmove s (by decide : 2 ≤ 2)
    (composeAction (sectionQuotientEquiv s hz) b))⟩

/-- The remaining product witness selects the factor containing the actual
component and retains both the full source record and its unsolved action row. -/
def RemainingTwoFactorCase (L : Subgroup G) : Prop :=
  ∃ d : SourceTwoFactorCase ((reducedRepresentation L).comp
      (offenderSubgroup (reducedRepresentation L)).subtype),
    (NormalizerReducedAction.componentImage L).subgroupOf
      (offenderSubgroup (reducedRepresentation L)) ≤ d.first ∧
    ProductMarkings.RemainingFactorCase d.first d.firstSpace

omit [Finite G] in
/-- Expose the two remaining rows while keeping the original product record and maps. -/
theorem remainingTwoFactorCase_iff (L : Subgroup G) :
    RemainingTwoFactorCase L ↔
      ∃ d : SourceTwoFactorCase ((reducedRepresentation L).comp
        (offenderSubgroup (reducedRepresentation L)).subtype),
        (NormalizerReducedAction.componentImage L).subgroupOf
          (offenderSubgroup (reducedRepresentation L)) ≤ d.first ∧
        ProductMarkings.RemainingFactorCase d.first d.firstSpace := Iff.rfl

/-- Orient the genuine product toward the selected component and construct
the natural SL2(4), single-natural, rank-four and doubled-natural markings. -/
theorem twoFactors_marked_or_remaining
    {T : Sylow 2 G} (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {L : Subgroup G} (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L))
    (hmove : L = ⁅L, ChapterB.thompsonJ (T : Subgroup G) 0⁆)
    (d : SourceTwoFactorCase ((reducedRepresentation L).comp
      (offenderSubgroup (reducedRepresentation L)).subtype)) :
    Nonempty (FourWayMarking.{u,u} T L) ∨ RemainingTwoFactorCase L := by
  have hc := reducedOffender_component h hmany hL hn hmove
  have step (d : SourceTwoFactorCase ((reducedRepresentation L).comp
      (offenderSubgroup (reducedRepresentation L)).subtype))
      (hle : (NormalizerReducedAction.componentImage L).subgroupOf
        (offenderSubgroup (reducedRepresentation L)) ≤ d.first) :
      Nonempty (FourWayMarking.{u,u} T L) ∨ RemainingTwoFactorCase L := by
    cases d.firstCase with
    | natural hm hn =>
      cases hn with
      | linearTwo F he =>
        obtain ⟨a⟩ := he
        exact Or.inl (twoFactors_linearTwo_marked h hmany hL ‹¬ IsQuasisimple (XiQuotient L)› hmove d hle hm F a)
      | symmetricFive he => exact Or.inr ⟨d,hle,.symmetricFive hm he⟩
      | linearThree F ho he =>
        obtain ⟨a⟩ := he
        exact Or.inl (twoFactors_linearThree_marked h hmany hL ‹¬ IsQuasisimple (XiQuotient L)› hmove d hle hm F ho a)
    | doubleNatural F ho hm he =>
      obtain ⟨a⟩ := he
      exact Or.inl (twoFactors_doubleThree_marked h hmany hL hn hmove d hle hm F ho a)
    | exceptional hm he => exact Or.inr ⟨d,hle,.exceptional hm he⟩
  rcases ProductMarkings.component_le_factor d.product hc with ha | hb
  · exact step d ha
  · exact step {
      first := d.second
      second := d.first
      product := d.product.swap
      firstSpace := d.secondSpace
      secondSpace := d.firstSpace
      decomposition := d.decomposition.symm
      firstCase := d.secondCase
      secondCase := d.firstCase } hb

/-- The literal source inputs now leave only the selected S5 quotient and
exceptional upper-extension product rows. All hyperplane and ordinary linear
product rows construct complete markings. -/
theorem reducedOffender_marked_or_remainingFactor
    {T : Sylow 2 G} (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {L : Subgroup G} (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L))
    (hmove : L = ⁅L, ChapterB.thompsonJ (T : Subgroup G) 0⁆) :
    Nonempty (FourWayMarking.{u,u} T L) ∨ RemainingTwoFactorCase L := by
  rcases reducedOffender_marked_or_twoFactors h hmany hL hn hmove with hm | hd
  · exact Or.inl hm
  · obtain ⟨d⟩ := hd
    exact twoFactors_marked_or_remaining h hmany hL hn hmove d

end CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.Classification
