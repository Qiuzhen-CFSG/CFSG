module
public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.Classification.SmallActions
public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.Classification.LinearThreeExtensions
public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.Classification.LinearTwoFour

/-!
# The natural and rank-four source markings

The small irreducible classification constructs the natural SL₂(4) quotient
and the one-copy SL₃(2) marking. In the nonsplit SL₃(2) case the original
Ω₁Z(T) lies in the reduced normalizer module. Its vectors are fixed by the
image of the original Sylow; the B.4.8(2) fixed-space calculation and the
B.5.1(5) fixed supplement therefore show that they centralize L. This
completes the rank-four marking, including the source centralization clause.

This uses the genuine B.5.1 supplement on the original reduced module; it
does not assume an identification of an omega-closure commutator with U.
The literal consumer retains only the marked symmetric-five branch and the
two product alternatives. No classification premise is added to the original
source inputs; the earlier Thompson movement remains explicit.

Source: Aschbacher--Smith 13.1.10, pp.871--872; B.4.8(2), B.5.1(5), I.1.6(4).
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.Classification
open Chapter1 Chapter1.Section02 Chapter12.Section02 ChapterB.SourceInduction
open ChapterB.QuasisimpleSource
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The unsolved irreducible outputs retain their genuine quotient markings.
The rank-four row still needs the original Z-centralization argument. -/
def RemainingIrreducibleAction {D V : Type*} [Group D]
    [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) D V} {K : Subgroup D}
    (s : MovedSection ρ K) : Prop :=
  (IsLinearNatural (s.action.comp K.subtype) BinaryField.two 3 ∧
    s.central.toSubmodule ≠ ⊥ ∧ Module.finrank (ZMod 2) s.space.toSubmodule = 4) ∨
  Nonempty (MarkedActionEquiv s.action (offenderSubgroup s.action) K
    (BinaryPermutation.naturalRepresentation (Fin 5)) (alternatingGroup (Fin 5)))

/-- Apply every new marking to the original source case. The uncompleted
rows retain the entire B.5 conclusion and its original quotient maps. -/
theorem reducedOffender_marked_or_extensions
    {T : Sylow 2 G} (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {L : Subgroup G} (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L))
    (hmove : L = ⁅L, ChapterB.thompsonJ (T : Subgroup G) 0⁆) :
    Nonempty (FourWayMarking.{u,u} T L) ∨
      (∃ d : ProjectiveLine.QuasisimpleSourceConclusion
        ((reducedRepresentation L).comp (offenderSubgroup (reducedRepresentation L)).subtype)
        ((NormalizerReducedAction.componentImage L).subgroupOf
          (offenderSubgroup (reducedRepresentation L))),
        IrreducibleSectionCase d.sectionData ∧ RemainingIrreducibleAction d.sectionData) ∨
      Nonempty (SourceTwoFactorCase ((reducedRepresentation L).comp
        (offenderSubgroup (reducedRepresentation L)).subtype)) ∨
      Nonempty (HyperplaneCase ((reducedRepresentation L).comp
        (offenderSubgroup (reducedRepresentation L)).subtype)) := by
  have hTL := radicalLocal_invariant_source hL.1.1
    (uniqueness_local_quotient_sqtk h.simpleQTKE hL.1.1.2.2) hn
  let : IsElementaryAbelian 2 (normalizerMoved L) :=
    (faithful_maximal_normalizer_moved h.simpleQTKE hL hTL).1
  rcases reducedOffender_marked_or_remaining h hmany hL hn hmove with hm | hi | hp
  · exact Or.inl hm
  · obtain ⟨d,hd,hsmall⟩ := irreducibleReduced_small h hmany hL hn hmove hi
    rcases hsmall with ⟨F,hF,⟨a⟩⟩ | ha | ha
    · exact Or.inl ⟨.pslTwoFour
        (irreducibleFourMarking h hmany hL hn hmove d.sectionData F hF a)⟩
    · rcases singleThree_marked_or_central h hmany hL hn hmove d.sectionData ha with hm | hz
      · exact Or.inl hm
      · obtain ⟨a⟩ := ha
        exact Or.inr (Or.inl ⟨d,hd,Or.inl ⟨⟨a⟩,hz,
          threeCover_dimension_four d.sectionData a ((irreducibleSectionCase_iff _).mp hd).1 hz⟩⟩)
    · exact Or.inr (Or.inl ⟨d,hd,Or.inr ha⟩)
  · exact Or.inr (Or.inr hp)

end CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.Classification

open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.Classification
open Chapter1 Chapter1.Section02 Chapter12.Section02 ChapterB.SourceInduction
open ChapterB.QuasisimpleSource
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The original Sylow omega-center belongs to the reduced normalizer module. -/
theorem source_omega_le_reduced
    {T : Sylow 2 G} (h : Hypothesis1311 T)
    {L : Subgroup G} (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L)) :
    omegaOneCenterAmbient (T : Subgroup G) ≤ normalizerReduced L := by
  have hTL := radicalLocal_invariant_source hL.1.1
    (uniqueness_local_quotient_sqtk h.simpleQTKE hL.1.1.2.2) hn
  obtain ⟨he,hne,_,hN⟩ := faithful_maximal_normalizer_moved h.simpleQTKE hL hTL
  let : IsElementaryAbelian 2 (normalizerMoved L) := he
  have hlocal : IsTwoLocal (NormalizerReducedAction.Ambient L) :=
    ⟨normalizerMoved L,hne,IsElementaryAbelian.isPGroup 2 _,hN.symm⟩
  have hHe := lemma_1_1_4_6 T (h.simpleQTKE.evenCharacteristic T)
    ⟨mem_H_of_isTwoLocal hlocal,hTL⟩
  have hi := sylow_omegaCenter_le_reduced (T.subtype hTL) (mem_He_iff.mp hHe)
  change omegaOneCenterAmbient ((T.subtype hTL : Sylow 2 (NormalizerReducedAction.Ambient L)) :
    Subgroup (NormalizerReducedAction.Ambient L)) ≤ NormalizerReducedAction.Core L at hi
  have hh := map_mono (f := (NormalizerReducedAction.Ambient L).subtype) hi
  rw [← omegaOneCenterAmbient_map_injective _ (NormalizerReducedAction.Ambient L).subtype_injective,
    Sylow.coe_subtype, map_subgroupOf_eq_of_le hTL] at hh
  rw [normalizerReduced_eq]
  exact hh

omit [Finite G] in
private theorem reduced_fixed_iff (L : Subgroup G)
    (t : NormalizerReducedAction.Ambient L)
    (v : Additive (NormalizerReducedAction.Core L)) :
    reducedRepresentation L (NormalizerReducedAction.quotient L t) v = v ↔
      (t : G) * (v.toMul : G) = (v.toMul : G) * (t : G) := by
  have he := congrArg Subtype.val (reducedRepresentation_apply L t v)
  constructor
  · intro h
    rw [h] at he
    exact mul_inv_eq_iff_eq_mul.mp he.symm
  · intro h
    apply Additive.toMul.injective
    apply Subtype.ext
    apply Subtype.ext
    exact he.trans (mul_inv_eq_iff_eq_mul.mpr h)

/-- In the actual nonsplit irreducible linear-three row, B.5.1(5) and
B.4.8(2) force the original Omega₁ Z(T) to centralize L. No centralization
hypothesis or callback is supplied. -/
theorem irreducibleThree_omega_central
    {T : Sylow 2 G} (h : Hypothesis1311 T)
    (_hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {L : Subgroup G} (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L))
    (hmove : L = ⁅L, ChapterB.thompsonJ (T : Subgroup G) 0⁆)
    (d : ProjectiveLine.QuasisimpleSourceConclusion
      ((reducedRepresentation L).comp (offenderSubgroup (reducedRepresentation L)).subtype)
      ((NormalizerReducedAction.componentImage L).subgroupOf
        (offenderSubgroup (reducedRepresentation L))))
    (hi : IrreducibleSectionCase d.sectionData)
    (hz : d.sectionData.central.toSubmodule ≠ ⊥)
    (a : ActionEquiv (d.sectionData.action.comp
      ((NormalizerReducedAction.componentImage L).subgroupOf
        (offenderSubgroup (reducedRepresentation L))).subtype) (linearNatural BinaryField.two 3)) :
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
      apply (reduced_fixed_iff L t v).mpr
      change (t : G) * (z0 : G) = (z0 : G) * (t : G)
      rw [hz0eq]
      exact ((mem_omegaOneCenterAmbient_iff _ _).mp hzT).2.2 t htT
    exact (congrArg (fun k => reducedRepresentation L k v) hact).trans htfix
  have hf := three_source_fixed_of_sylow d ((irreducibleSectionCase_iff _).mp hi).1 a hz S v hv
  have he := hf (eK.symm (reducedComponentMap L ⟨l,hl⟩))
  change reducedRepresentation L (NormalizerReducedAction.componentMap L ⟨l,hl⟩) v = v at he
  rw [NormalizerReducedAction.componentMap_eq] at he
  have he0 := (reduced_fixed_iff L (inclusion L.le_normalizer ⟨l,hl⟩) v).mp he
  change l * (z0 : G) = (z0 : G) * l at he0
  rw [hz0eq] at he0
  exact he0


end CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.Classification

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.Classification
open Chapter1 Chapter1.Section02 Chapter12.Section02 ChapterB.SourceInduction
open ChapterB.QuasisimpleSource
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The nonsplit irreducible branch supplies all clauses of source row (4),
including centralization of the original Sylow omega-center. -/
def irreducibleThreeRankFourMarking
    {T : Sylow 2 G} (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {L : Subgroup G} [IsElementaryAbelian 2 (normalizerMoved L)]
    (hL : FaithfulMaximalLocal T L) (hn : ¬ IsQuasisimple (XiQuotient L))
    (hmove : L = ⁅L, ChapterB.thompsonJ (T : Subgroup G) 0⁆)
    (d : ProjectiveLine.QuasisimpleSourceConclusion
      ((reducedRepresentation L).comp (offenderSubgroup (reducedRepresentation L)).subtype)
      ((NormalizerReducedAction.componentImage L).subgroupOf
        (offenderSubgroup (reducedRepresentation L))))
    (hi : IrreducibleSectionCase d.sectionData)
    (hz : d.sectionData.central.toSubmodule ≠ ⊥)
    (a : ActionEquiv (d.sectionData.action.comp
      ((NormalizerReducedAction.componentImage L).subgroupOf
        (offenderSubgroup (reducedRepresentation L))).subtype) (linearNatural BinaryField.two 3)) :
    LinearThreeRankFourMarking T L := by
  have hj := componentImage_le_reducedOffender h hL hn hmove
  let e := (reducedImageEquivMovedImage h hmany hL hn).symm.trans
    ((subgroupOfEquivOfLe hj).symm.trans a.groupEquiv)
  exact {
    common := CommonMarking.of_source h hmany hL hn hmove
    image_model := ⟨ZMod 2,inferInstance,inferInstance,by simp,
      ⟨e.trans (BinaryLinear.OuterCyclic.projectiveEquivSL (by decide : 0 < 3)).symm⟩⟩
    rank_four := singleThree_central_rank_four h hmany hL hn hmove d.sectionData ((irreducibleSectionCase_iff _).mp hi).1 hz a
    omega_center_central := irreducibleThree_omega_central h hmany hL hn hmove d hi hz a }

/-- The source action now yields a complete marking except for the actual S5
row and the two product rows, which retain all their original source data. -/
theorem reducedOffender_marked_or_symmetric_products
    {T : Sylow 2 G} (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {L : Subgroup G} (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L))
    (hmove : L = ⁅L, ChapterB.thompsonJ (T : Subgroup G) 0⁆) :
    Nonempty (FourWayMarking.{u,u} T L) ∨
      (∃ d : ProjectiveLine.QuasisimpleSourceConclusion
        ((reducedRepresentation L).comp (offenderSubgroup (reducedRepresentation L)).subtype)
        ((NormalizerReducedAction.componentImage L).subgroupOf
          (offenderSubgroup (reducedRepresentation L))),
        IrreducibleSectionCase d.sectionData ∧
        Nonempty (MarkedActionEquiv d.sectionData.action (offenderSubgroup d.sectionData.action)
          ((NormalizerReducedAction.componentImage L).subgroupOf
            (offenderSubgroup (reducedRepresentation L)))
          (BinaryPermutation.naturalRepresentation (Fin 5)) (alternatingGroup (Fin 5)))) ∨
      Nonempty (SourceTwoFactorCase ((reducedRepresentation L).comp
        (offenderSubgroup (reducedRepresentation L)).subtype)) ∨
      Nonempty (HyperplaneCase ((reducedRepresentation L).comp
        (offenderSubgroup (reducedRepresentation L)).subtype)) := by
  have hTL := radicalLocal_invariant_source hL.1.1
    (uniqueness_local_quotient_sqtk h.simpleQTKE hL.1.1.2.2) hn
  let : IsElementaryAbelian 2 (normalizerMoved L) :=
    (faithful_maximal_normalizer_moved h.simpleQTKE hL hTL).1
  rcases reducedOffender_marked_or_extensions h hmany hL hn hmove with hm | hi | hp
  · exact Or.inl hm
  · obtain ⟨d,hd,hrem⟩ := hi
    rcases hrem with ⟨⟨a⟩,hz,_⟩ | ha
    · exact Or.inl ⟨.linearThreeRankFour
        (irreducibleThreeRankFourMarking h hmany hL hn hmove d hd hz a)⟩
    · exact Or.inr (Or.inl ⟨d,hd,ha⟩)
  · exact Or.inr (Or.inr hp)

end CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.Classification
