module
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.OriginalSource.SpecialLinearFourCoordinates
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.OriginalSource.ProjectiveTwoFourTerminal
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.LinearThreeFour
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CriticalSource
public import Theory.Representation.BinaryOffender.NonFFDisplacement
public import Theory.Representation.SL3FourNaturalDual.QuadraticActors.RankBound

/-!
# The original full SL₃(4) contradiction and higher-field exclusion

Native natural-plus-dual coordinates retain the scalar center and actual
component action on U_H/V₁. The proved absence of FF-offenders excludes
rank-one displacements, so the original critical geometry supplies its
selected pair and quadratic actor. The model normalizer calculation places
that actor in the component; its root-plane parameters give rank at most
four and the explicit critical shapes.

The literal image of D_H has the original corank bound, and its displacements
lie in the image of the same conjugate of V₁. That image has dimension at
most one. The concrete common-line obstruction therefore excludes full
SL₃(4). All higher-field alternatives now contradict the source context,
including components of unrestricted original overgroups.

The earlier LocalSetup, maximality, F.9 applicability and centralizer/core
premises retain their original producers, with qt-d-1381-source owning their
final discharge. Whole-quotient binary exclusion and the complete 13.8.19–21
assembly remain with qt-d-138-fields-source.
Source: Aschbacher–Smith, 13.8.20, printed pp.954–955, using F.9.13(6),
F.9.16(2), B.4.5 and F.9.18(4,7).
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender

open Representation.SL3FourNaturalDual
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.OriginalSource
open SourceCompletion TransvectionRecognition.Component.ModelExtension
open LinearThree.Geometry.CoveredProduct.ResidualPlacement
open CriticalGeometry CriticalGeometry.Reorientation
open ExceptionalFields.LinearThreeFour.AutomorphismModule
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}

/-- The original full SL₃(4) component contradicts the critical common-line
geometry on the literal U_H/V₁. All module and actor markings are constructed. -/
theorem source_specialLinearThree_false
    (c : FieldComponents.SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (eK : Source.starImage H K ≃* SL) : False := by
  classical
  let : (K.subgroupOf H).Normal := c.component.normal
  let : (Source.starImage H K).Normal :=
    c.component.normal.map _ (QuotientGroup.mk'_surjective _)
  have hH := c.component.local_overgroup
  have hF9 := c.f9 H hH
  let : IsElementaryAbelian 2 (Source.UH H V₃) := c.localSetup.uh_elementary hH
  let act := Comparison.conjugationAction (c.localSetup.line_le_uh H) hF9.plus_le_H
    (hF9.H_centralizes.trans (Subgroup.centralizer_le_normalizer _))
    hF9.commutator_UH_QH_le_point
  let s := Comparison.sourceSection act hF9.H_centralizes
  have hf := f9_section_faithful _ hF9 s
  obtain ⟨e,E,hE⟩ := source_specialLinearThree_coordinates c act eK
  have hqs := (SolvableSource.component_fitting_source c.localSetup c.maximal c.f9
    c.centralizer c.noncentral_core c.earlier1339 hH K c.component.component).2
  obtain ⟨w⟩ := CriticalSource.exists_selected_witness c.localSetup hH hF9
    (by rw [←c.component.generated,sup_assoc]) c.component.component c.component.normal hqs
    c.centralizer c.noncentral_core act.representation act.conjugation
    (not_rank_one_of_not_ff act.representation hf (source_specialLinearThree_not_ff c act eK))
  have hgeo := local_earlierGeometry c.localSetup hF9 w.pair
  have hshape := QuadraticActors.criticalShapes_of_equivariant_unbounded act.representation hf
    (Source.starImage H K) e E hE (Source.starImage H (w.pair.Ugamma V₃))
      w.quadratic_member.1 w.quadratic_member.2.1 w.quadratic_member.2.2
  have hUgH : w.pair.Ugamma V₃ ≤ H :=
    (map_mono (conjugateSpanBy_mono c.localSetup.seed_le le_rfl)).trans w.actor_le
  have hreverse : Source.UH H V₃ ≤ H.map (MulAut.conj (w.pair.gb : G)).toMonoidHom := by
    rw [←w.pair.vertexGroup_gamma]
    exact (conjugateSpanBy_mono c.localSetup.seed_le le_rfl).trans hgeo.VH_endpoint
  have hline := s.critical_line_displacement_of_conjugate (w.pair.Ugamma V₃)
    (w.pair.gb : G) hreverse c.localSetup.line_card
  obtain ⟨z,hz⟩ := (finrank_le_one_iff (K := ZMod 2)).mp hline.1
  apply ExceptionalFields.LinearThreeFour.sl3_four_critical_obstruction act.representation
    (Source.starImage H (w.pair.Ugamma V₃)) hshape
    (s.image (Source.DH (Source.UH H V₃) (w.pair.Ugamma V₃) (w.pair.Aone V₁))) z.val
  · rw [s.quotient_finrank _ (s.line_le_DH _ _ hUgH)]
    exact w.comparison
  · intro a ha d hd
    have hm := hline.2 a ha d hd
    obtain ⟨b,hb⟩ := hz ⟨act.representation a d-d,hm⟩
    exact Submodule.mem_span_singleton.mpr ⟨b,congrArg Subtype.val hb⟩

/-- Full field-four special-linear component quotients are excluded, without
passing to the projective quotient or discarding their scalar center. -/
theorem source_not_specialLinearThree_four
    (c : FieldComponents.SourceContext T L V V₁ V₂ V₃ M G₁ H K) :
    ¬ Chapter1.Section02.LocalModels.IsSL (K ⧸ pCore 2 K) 3 4 := by
  rintro ⟨Q,hQ,hfin,hcard,⟨e⟩⟩
  let := Fintype.ofFinite Q
  let := Fintype.ofFinite F
  let a : Q ≃+* F := FiniteField.ringEquivOfCardEq (by
    rw [←Nat.card_eq_fintype_card,←Nat.card_eq_fintype_card,hcard,
      ExceptionalFields.LinearThreeFour.AutomorphismModule.LocalAlternatives.sl3Field_card]
    norm_num)
  have hKH : K ≤ H := (le_sup_left.trans le_sup_left).trans_eq c.component.generated
  let eK := (Components.componentStarEquiv H K hKH c.component.component).symm.trans
    (e.trans (Atlas.fieldEquivSL 3 a))
  exact source_specialLinearThree_false c eK

/-- Every original higher-field component alternative is excluded. -/
theorem source_no_higher_field
    (c : FieldComponents.SourceContext T L V V₁ V₂ V₃ M G₁ H K) :
    ¬ HigherFieldAlternative (K ⧸ pCore 2 K) := fun hfield =>
  source_not_specialLinearThree_four c (source_higher_field_specialLinear_four c hfield)

/-- The full higher-field exclusion applies to every component of an
unrestricted original overgroup, preserving its intrinsic quotient. -/
theorem original_no_higher_field
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (h : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hF9 : ∀ J ∈ Source.Hz (one L T V₁) T G₁ M,
      (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ J).Hypothesis)
    (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
    (hcomm : ⁅V₃,G₁.pCoreIn 2⁆ ≠ ⊥)
    (hH : H ∈ Source.Hz (one L T V₁) T G₁ M)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent) :
    ¬ HigherFieldAlternative (K ⧸ pCore 2 K) := by
  let c := Overgroups.context_of_original d h hF9 hcentral hcomm hH
  exact source_no_higher_field (Overgroups.reducedContext c K hKH hK)
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.OriginalSource
