module
public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.ClassificationOrbits.SourceSections

/-!
# Product and hyperplane rows in the original centralizer analysis

The original B.5 product coordinates are transported to the moved subgroup.
The natural-three quotient is retained through the central-cover argument,
including the nonsplit rank-four case. Each natural row supplies the literal
orbit, core and quaternion-action interfaces; the deleted S5 row retains its
actual marking for its symmetric-three stabilizer application.

Source: Aschbacher--Smith 13.1.10--12, pp.871--874; B.5.6(3),(5).
-/

public noncomputable section
open scoped IsMulCommutative
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.Classification
open Chapter1 Chapter1.Section02 Chapter12.Section02 SourceCentralizerStructure.Elimination
open ChapterB.QuasisimpleSource ChapterB.SourceInduction
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L : Subgroup G} {p : ℕ} [Fact p.Prime]

/-- The hyperplane source row supplies both original centralizer inputs. -/
theorem hyperplane_centralizer_inputs (h : Context T L p)
    (hmove : L = ⁅L, ChapterB.thompsonJ (T : Subgroup G) 0⁆)
    (d : HyperplaneCase ((reducedRepresentation L).comp
      (offenderSubgroup (reducedRepresentation L)).subtype)) :
    OrbitFacts T L p ∧ SieveActions h := by
  have hTL := radicalLocal_invariant_source h.maximal.1.1
    (uniqueness_local_quotient_sqtk h.hypothesis.simpleQTKE h.maximal.1.1.2.2) h.nonquasisimple
  let : IsElementaryAbelian 2 (normalizerMoved L) :=
    (faithful_maximal_normalizer_moved h.hypothesis.simpleQTKE h.maximal hTL).1
  have hj := componentImage_le_reducedOffender h.hypothesis h.maximal h.nonquasisimple hmove
  let C := (NormalizerReducedAction.componentImage L).subgroupOf
    (offenderSubgroup (reducedRepresentation L))
  let : (NormalizerReducedAction.componentImage L).Normal := reducedComponent_normal L
  let : C.Normal := inferInstance
  let s := MovedSection.ofNormal ((reducedRepresentation L).comp
    (offenderSubgroup (reducedRepresentation L)).subtype) C
  rcases ProductMarkings.hyperplane_component_actions d
      (reducedOffender_component h.hypothesis h.many h.maximal h.nonquasisimple hmove) s with ⟨r,hr,⟨a⟩⟩ | ⟨F,⟨a⟩⟩
  · exact (repeatedThreeMarking h.hypothesis h.many h.maximal h.nonquasisimple hmove s hr a).centralizer_inputs h
  · let e := (subgroupOfEquivOfLe hj).trans (reducedImageEquivMovedImage h.hypothesis h.many h.maximal h.nonquasisimple)
    obtain ⟨p,hp,hp3,hm⟩ := moved_component_pslTwo h.hypothesis h.many h.maximal h.nonquasisimple
    have hr := (prime_model_ranks hp hp3 (hm.of_mulEquiv e)).1
    exact (irreducibleFourMarking h.hypothesis h.many h.maximal h.nonquasisimple hmove s F
      (selected_two_degree F a.groupEquiv hr) a).centralizer_inputs h

/-- The product natural SL2 quotient supplies the A5-cover centralizer inputs. -/
theorem twoFactors_linearTwo_centralizer_inputs (h : Context T L p)
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
      d.first.subtype) (linearNatural F 2)) : OrbitFacts T L p ∧ SieveActions h := by
  have hTL := radicalLocal_invariant_source h.maximal.1.1
    (uniqueness_local_quotient_sqtk h.hypothesis.simpleQTKE h.maximal.1.1.2.2) h.nonquasisimple
  let : IsElementaryAbelian 2 (normalizerMoved L) :=
    (faithful_maximal_normalizer_moved h.hypothesis.simpleQTKE h.maximal hTL).1
  have hj := componentImage_le_reducedOffender h.hypothesis h.maximal h.nonquasisimple hmove
  let C := (NormalizerReducedAction.componentImage L).subgroupOf
    (offenderSubgroup (reducedRepresentation L))
  let : (NormalizerReducedAction.componentImage L).Normal := reducedComponent_normal L
  let : C.Normal := inferInstance
  have hC := reducedOffender_component h.hypothesis h.many h.maximal h.nonquasisimple hmove
  let : IsQuasisimple C := hC.2
  have hCA := ProductMarkings.component_eq_linearTwo hC hle F a.groupEquiv
  let s := MovedSection.ofNormal ((reducedRepresentation L).comp
    (offenderSubgroup (reducedRepresentation L)).subtype) C
  let b := composeAction (ProductMarkings.twoFactors_sectionImage d s hCA hm) a
  let e := (subgroupOfEquivOfLe hj).trans (reducedImageEquivMovedImage h.hypothesis h.many h.maximal h.nonquasisimple)
  obtain ⟨p,hp,hp3,hmodel⟩ := moved_component_pslTwo h.hypothesis h.many h.maximal h.nonquasisimple
  have hr := (prime_model_ranks hp hp3 (hmodel.of_mulEquiv e)).1
  exact (irreducibleFourMarking h.hypothesis h.many h.maximal h.nonquasisimple hmove s F
    (selected_two_degree F b.groupEquiv hr) b).centralizer_inputs h

/-- Retain the natural-three projection through the zero-kernel and rank-four cover cases. -/
theorem twoFactors_linearThree_centralizer_inputs (h : Context T L p)
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
      d.first.subtype) (linearNatural F 3)) : OrbitFacts T L p ∧ SieveActions h := by
  have hTL := radicalLocal_invariant_source h.maximal.1.1
    (uniqueness_local_quotient_sqtk h.hypothesis.simpleQTKE h.maximal.1.1.2.2) h.nonquasisimple
  let : IsElementaryAbelian 2 (normalizerMoved L) :=
    (faithful_maximal_normalizer_moved h.hypothesis.simpleQTKE h.maximal hTL).1
  have hj := componentImage_le_reducedOffender h.hypothesis h.maximal h.nonquasisimple hmove
  let C := (NormalizerReducedAction.componentImage L).subgroupOf
    (offenderSubgroup (reducedRepresentation L))
  let : (NormalizerReducedAction.componentImage L).Normal := reducedComponent_normal L
  let : C.Normal := inferInstance
  have hC := reducedOffender_component h.hypothesis h.many h.maximal h.nonquasisimple hmove
  let : IsQuasisimple C := hC.2
  have hCA := ProductMarkings.component_eq_linearThree hC hle F ho a.groupEquiv
  let s := MovedSection.ofNormal ((reducedRepresentation L).comp
    (offenderSubgroup (reducedRepresentation L)).subtype) C
  let a' := composeAction (ProductMarkings.twoFactors_sectionImage d s hCA hm) a
  let e := (subgroupOfEquivOfLe hj).trans (reducedImageEquivMovedImage h.hypothesis h.many h.maximal h.nonquasisimple)
  obtain ⟨p,hp,hp3,hmodel⟩ := moved_component_pslTwo h.hypothesis h.many h.maximal h.nonquasisimple
  have hr := (prime_model_ranks hp hp3 (hmodel.of_mulEquiv e)).1
  let b := composeAction a' (ExtensionConsequences.degreeOneNaturalEquiv F
    (ProductMarkings.linearThree_degree F ho a'.groupEquiv hr) 3)
  have hi := s.irrPlus_of_irreducible (ExtensionConsequences.irreducible_of_equiv b
    (ExtensionConsequences.linearNatural_irreducible BinaryField.two (by decide : 2 ≤ 3)))
  exact centralizer_inputs_of_three_section h hj s hi b

/-- The doubled product quotient has no hidden central kernel and supplies the original orbit and quaternion actions. -/
theorem twoFactors_doubleThree_centralizer_inputs (h : Context T L p)
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
      d.first.subtype) (repeated (linearNatural F 3) 2)) : OrbitFacts T L p ∧ SieveActions h := by
  have hTL := radicalLocal_invariant_source h.maximal.1.1
    (uniqueness_local_quotient_sqtk h.hypothesis.simpleQTKE h.maximal.1.1.2.2) h.nonquasisimple
  let : IsElementaryAbelian 2 (normalizerMoved L) :=
    (faithful_maximal_normalizer_moved h.hypothesis.simpleQTKE h.maximal hTL).1
  have hj := componentImage_le_reducedOffender h.hypothesis h.maximal h.nonquasisimple hmove
  let C := (NormalizerReducedAction.componentImage L).subgroupOf
    (offenderSubgroup (reducedRepresentation L))
  let : (NormalizerReducedAction.componentImage L).Normal := reducedComponent_normal L
  let : C.Normal := inferInstance
  have hC := reducedOffender_component h.hypothesis h.many h.maximal h.nonquasisimple hmove
  let : IsQuasisimple C := hC.2
  have hCA := ProductMarkings.component_eq_linearThree hC hle F ho a.groupEquiv
  let s := MovedSection.ofNormal ((reducedRepresentation L).comp
    (offenderSubgroup (reducedRepresentation L)).subtype) C
  let a' := composeAction (ProductMarkings.twoFactors_sectionImage d s hCA hm) a
  let e := (subgroupOfEquivOfLe hj).trans (reducedImageEquivMovedImage h.hypothesis h.many h.maximal h.nonquasisimple)
  obtain ⟨p,hp,hp3,hmodel⟩ := moved_component_pslTwo h.hypothesis h.many h.maximal h.nonquasisimple
  have hr := (prime_model_ranks hp hp3 (hmodel.of_mulEquiv e)).1
  let b := composeAction a' (ExtensionConsequences.degreeOneRepeatedEquiv F
    (ProductMarkings.linearThree_degree F ho a'.groupEquiv hr) 3 2)
  let : Nontrivial C := (Subgroup.nontrivial_iff_ne_bot C).mpr hC.isCComponent.ne_bot
  have hFF := ProductMarkings.twoFactors_moved_ff d
    (reducedOffender_hypothesis h.hypothesis h.maximal h.nonquasisimple).generated s hCA hm
  have hz := ProductMarkings.doubled_section_central_eq_bot s b hFF
  exact (repeatedThreeMarking h.hypothesis h.many h.maximal h.nonquasisimple hmove s (by decide : 2 ≤ 2)
    (composeAction (sectionQuotientEquiv s hz) b)).centralizer_inputs h

/-- The exceptional upper-four-space product row has a natural moved three-space, which supplies the original centralizer inputs. -/
theorem twoFactors_exceptional_centralizer_inputs (h : Context T L p)
    (hmove : L = ⁅L, ChapterB.thompsonJ (T : Subgroup G) 0⁆)
    (d : SourceTwoFactorCase ((reducedRepresentation L).comp
      (offenderSubgroup (reducedRepresentation L)).subtype))
    (hle : (NormalizerReducedAction.componentImage L).subgroupOf
      (offenderSubgroup (reducedRepresentation L)) ≤ d.first)
    (hm : moved ((reducedRepresentation L).comp
      (offenderSubgroup (reducedRepresentation L)).subtype) d.first ≤ d.firstSpace.toSubmodule)
    (q : FourDimensionalSource (((fixed ((reducedRepresentation L).comp
      (offenderSubgroup (reducedRepresentation L)).subtype)).quotientImage d.firstSpace).toRepresentation.comp
      d.first.subtype)) : OrbitFacts T L p ∧ SieveActions h := by
  have hTL := radicalLocal_invariant_source h.maximal.1.1
    (uniqueness_local_quotient_sqtk h.hypothesis.simpleQTKE h.maximal.1.1.2.2) h.nonquasisimple
  let : IsElementaryAbelian 2 (normalizerMoved L) :=
    (faithful_maximal_normalizer_moved h.hypothesis.simpleQTKE h.maximal hTL).1
  let C := (NormalizerReducedAction.componentImage L).subgroupOf
    (offenderSubgroup (reducedRepresentation L))
  let : (NormalizerReducedAction.componentImage L).Normal := reducedComponent_normal L
  let : C.Normal := inferInstance
  have hC := reducedOffender_component h.hypothesis h.many h.maximal h.nonquasisimple hmove
  have hCA := ProductMarkings.component_eq_binaryThree hC hle q.natural.groupEquiv
  let s := MovedSection.ofNormal ((reducedRepresentation L).comp
    (offenderSubgroup (reducedRepresentation L)).subtype) C
  have hd : Module.finrank (ZMod 2) (moved ((reducedRepresentation L).comp
      (offenderSubgroup (reducedRepresentation L)).subtype) C) = 3 := by
    rw [show C = d.first from hCA]
    exact ProductMarkings.exceptional_moved_dimension d.first d.firstSpace hm q
  let e := (MulEquiv.subgroupCongr hCA).trans q.natural.groupEquiv
  let b := ProductMarkings.threeMovedEquiv s e hd
  exact (repeatedThreeMarking h.hypothesis h.many h.maximal h.nonquasisimple hmove s (by decide : 1 ≤ 2)
    (composeAction b (ProductMarkings.oneCopy _))).centralizer_inputs h

omit [Fact p.Prime] in
/-- The symmetric-five product row retains the actual original LT marking. -/
theorem twoFactors_symmetricFive_row (h : Context T L p)
    (hmove : L = ⁅L, ChapterB.thompsonJ (T : Subgroup G) 0⁆)
    (d : SourceTwoFactorCase ((reducedRepresentation L).comp
      (offenderSubgroup (reducedRepresentation L)).subtype))
    (hle : (NormalizerReducedAction.componentImage L).subgroupOf
      (offenderSubgroup (reducedRepresentation L)) ≤ d.first)
    (hm : d.firstSpace.toSubmodule = moved ((reducedRepresentation L).comp
      (offenderSubgroup (reducedRepresentation L)).subtype) d.first)
    (a : ActionEquiv (((fixed ((reducedRepresentation L).comp
      (offenderSubgroup (reducedRepresentation L)).subtype)).quotientImage d.firstSpace).toRepresentation.comp
      d.first.subtype) (BinaryPermutation.naturalRepresentation (Fin 5))) :
    Nonempty (SymmetricFiveRow T L) := by
  have hTL := radicalLocal_invariant_source h.maximal.1.1
    (uniqueness_local_quotient_sqtk h.hypothesis.simpleQTKE h.maximal.1.1.2.2) h.nonquasisimple
  let : IsElementaryAbelian 2 (normalizerMoved L) :=
    (faithful_maximal_normalizer_moved h.hypothesis.simpleQTKE h.maximal hTL).1
  have hj := componentImage_le_reducedOffender h.hypothesis h.maximal h.nonquasisimple hmove
  let C := (NormalizerReducedAction.componentImage L).subgroupOf
    (offenderSubgroup (reducedRepresentation L))
  let : (NormalizerReducedAction.componentImage L).Normal := reducedComponent_normal L
  let : C.Normal := inferInstance
  have hC := reducedOffender_component h.hypothesis h.many h.maximal h.nonquasisimple hmove
  let : IsQuasisimple C := hC.2
  let s := MovedSection.ofNormal ((reducedRepresentation L).comp
    (offenderSubgroup (reducedRepresentation L)).subtype) C
  let m := ProductMarkings.twoFactors_fiveAction d s hle hm a
    (ProductMarkings.five_component_map hC hle a.groupEquiv)
  let c := fullSectionSpaceEquiv hj s
  let k := (subgroupOfEquivOfLe hj).symm
  let b : ActionEquiv ((fullMovedSection L).space.toRepresentation.comp
      (NormalizerReducedAction.componentImage L).subtype) (alternatingNatural 5) := {
    groupEquiv := k.trans m.subgroupEquiv
    linearEquiv := c.trans m.action.linearEquiv
    intertwines := by
      intro g v
      have h1 := fullSectionSpaceEquiv_intertwines hj s (k g) v
      have h2 := (ExtensionConsequences.markedRestriction m).intertwines (k g) (c v)
      exact (congrArg m.action.linearEquiv h1).trans h2 }
  have hfull : Function.Surjective (fiveActor b.groupEquiv) := by
    intro p
    obtain ⟨g,rfl⟩ := m.action.groupEquiv.surjective p
    refine ⟨((g : offenderSubgroup (reducedRepresentation L)) : NormalizerReducedAction.Star L),?_⟩
    apply BinaryPermutation.naturalMulAction_injective_of_odd (Fin 5) (by decide)
    apply MulEquiv.ext
    intro v
    obtain ⟨w,hw⟩ := b.linearEquiv.surjective v.toAdd
    have he := fiveActor_equivariant (fullMovedSection L).space.toRepresentation b
      ((g : offenderSubgroup (reducedRepresentation L)) : NormalizerReducedAction.Star L) w
    have h1 := fullSectionSpaceEquiv_intertwines hj s g.val w
    have h2 := m.action.intertwines g (c w)
    have hh := he.symm.trans ((congrArg m.action.linearEquiv h1).trans h2)
    apply Multiplicative.toAdd.injective
    change BinaryPermutation.naturalRepresentation (Fin 5) (fiveActor b.groupEquiv g) v.toAdd =
      BinaryPermutation.naturalRepresentation (Fin 5) (m.action.groupEquiv g) v.toAdd
    change BinaryPermutation.naturalRepresentation (Fin 5) (fiveActor b.groupEquiv g)
      (b.linearEquiv w) = BinaryPermutation.naturalRepresentation (Fin 5)
        (m.action.groupEquiv g) (b.linearEquiv w) at hh
    simpa only [hw] using hh
  exact ⟨fullSymmetricFiveMarking h.hypothesis h.many h.maximal h.nonquasisimple hmove b hfull⟩

/-- Orient the actual B.5.6(3) product toward the original component. Every
natural and exceptional row supplies the source inputs; the deleted S5
row retains its actual marking for the symmetric-three stabilizer application. -/
theorem twoFactors_inputs_or_symmetric (h : Context T L p)
    (hmove : L = ⁅L, ChapterB.thompsonJ (T : Subgroup G) 0⁆)
    (d : SourceTwoFactorCase ((reducedRepresentation L).comp
      (offenderSubgroup (reducedRepresentation L)).subtype)) :
    (OrbitFacts T L p ∧ SieveActions h) ∨ Nonempty (SymmetricFiveRow T L) := by
  have hc := reducedOffender_component h.hypothesis h.many h.maximal h.nonquasisimple hmove
  have step (d : SourceTwoFactorCase ((reducedRepresentation L).comp
      (offenderSubgroup (reducedRepresentation L)).subtype))
      (hle : (NormalizerReducedAction.componentImage L).subgroupOf
        (offenderSubgroup (reducedRepresentation L)) ≤ d.first) :
      (OrbitFacts T L p ∧ SieveActions h) ∨ Nonempty (SymmetricFiveRow T L) := by
    cases d.firstCase with
    | natural hm hn =>
      cases hn with
      | linearTwo F he =>
        exact Or.inl (twoFactors_linearTwo_centralizer_inputs h hmove d hle hm F he.some)
      | symmetricFive he =>
        exact Or.inr (twoFactors_symmetricFive_row h hmove d hle hm he.some)
      | linearThree F ho he =>
        exact Or.inl (twoFactors_linearThree_centralizer_inputs h hmove d hle hm F ho he.some)
    | doubleNatural F ho hm he =>
      exact Or.inl (twoFactors_doubleThree_centralizer_inputs h hmove d hle hm F ho he.some)
    | exceptional hm he =>
      exact Or.inl (twoFactors_exceptional_centralizer_inputs h hmove d hle hm he)
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


end CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.Classification
