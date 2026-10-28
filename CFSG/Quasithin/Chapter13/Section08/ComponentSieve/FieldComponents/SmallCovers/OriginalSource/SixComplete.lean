module
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction.CubicGeometry
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.OriginalSource.SixTerminal
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.OriginalSource.MathieuSieve

/-!
# Completing the original triple-cover exclusions

The original source action has a fixed-free cubic center. The critical-line
geometry bounds its binary dimension by nine, while the extraspecial Sylow
three-group forces divisibility by six on every component submodule. Thus
its dimension is six and its component restriction is irreducible. Native
recognition identifies the whole action with the hexacode action, and the
already proved literal V_H/U_H permutation obstruction excludes it.

This removes the six-cover premise without assuming homogeneous invariance.
The genuine smaller-context replacement then also excludes the Mathieu
triple cover. Applying both results with the ordinary Mathieu exclusion
leaves only higher-field exclusion as a premise of the quotient list,
L₁-containment, H=KT and U_H=[U_H,K] applications below.

The field-sieve owner qt-d-138-fields-source retains the higher-field and
whole-quotient binary exclusions and unrestricted-overgroup assembly;
qt-d-1381-source supplies the preceding SourceContext.
Source: Aschbacher–Smith, 13.8.21(1–4), printed pp.955–957, using
F.9.13–16, B.4.5 and the native triple-cover automorphism structure.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.OriginalSource
open Reduction Reduction.ModuleRecognition SourceCompletion
open LinearThree.Geometry.CoveredProduct.ResidualPlacement
open HigherFieldReduction.ExternalModules
open CriticalGeometry CriticalGeometry.SectionActions CriticalGeometry.Reorientation
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}

section Action
variable [IsElementaryAbelian 2 (Source.UH H V₃)]

/-- The cubic center and original critical line force a whole hexacode model. -/
theorem source_six_cover_model
    (c : SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (e : (K ⧸ pCore 2 K) ≃* Components.Models.A6Triple)
    (act : QuotientAction H V₃ V₁) :
    Nonempty (HexacodeModel (Source.starImage H K) act.representation) := by
  classical
  let := c.component.normal
  let : (Source.starImage H K).Normal := Selection.starImage_normal H K
  let : Nontrivial (Additive (Source.Utilde H V₃ V₁)) := source_quotient_nontrivial c
  have hH := c.component.local_overgroup
  have hF9 := c.f9 H hH
  have hKH : K ≤ H := (le_sup_left.trans le_sup_left).trans_eq c.component.generated
  let eK := (Components.componentStarEquiv H K hKH c.component.component).symm.trans e
  have hc : centralizer (Source.starImage H K : Set (Source.Hstar H)) ≤ Source.starImage H K := by
    rw [←source_six_cover_fitting c e]
    exact centralizer_generalizedFitting_le _
  obtain ⟨z,hz,ho,hzc,hp⟩ := source_six_cover_cubic_polynomial c e act
  let raw : LinearThree.SourceAction H V₃ V₁ := {
    line_le := act.line_le
    seed_le := act.seed_le
    representation := act.representation
    conjugation := act.conjugation }
  have hf := f9_section_faithful _ hF9 (Comparison.sourceSection raw hF9.H_centralizes)
  have hn : (zpowers z).Normal := by rw [hzc]; infer_instance
  have hno := CubicGeometry.no_transvections act.representation _ eK z hz hzc hp hf ho hn
  let : IsQuasisimple Atlas.Codes.HexEvenAutomorphisms := Hexacode.even_isQuasisimple
  have hqs : IsQuasisimple (Source.starImage H K) := IsQuasisimple.of_mulEquiv eK.symm
  have hgen : H = K ⊔ (one L T V₁ ⊔ (T : Subgroup G)) := by
    rw [←c.component.generated,sup_assoc]
  obtain ⟨w⟩ := CriticalSource.exists_selected_witness c.localSetup hH hF9 hgen
    c.component.component c.component.normal hqs c.centralizer c.noncentral_core
    act.representation act.conjugation hno
  let s := CriticalInputs.sourceSection H V₃ V₁ act.representation act.conjugation
    hF9.plus_le_H (c.localSetup.line_le_plane.trans c.localSetup.plane_le_seed) hF9.H_centralizes
  have er := CriticalSource.earlier_inputs c.localSetup hH hF9 c.centralizer c.noncentral_core
    act.representation act.conjugation
  have hUgH : w.pair.Ugamma V₃ ≤ H :=
    (map_mono (conjugateSpanBy_mono c.localSetup.seed_le le_rfl)).trans w.actor_le
  have hUA : Source.UH H V₃ ≤ normalizer (w.pair.Aone V₁ : Set G) :=
    ((conjugateSpanBy_mono c.localSetup.seed_le le_rfl).trans (er.geometry w.pair).VH_endpoint).trans
      (SectionActions.CriticalPair.normalizes_Aone w.pair V₁
        (hF9.H_centralizes.trans (Subgroup.centralizer_le_normalizer _)))
  have hcard : Nat.card (w.pair.Aone V₁) = 2 :=
    (Nat.card_congr ((MulAut.conj (w.pair.gb : G)).subgroupMap V₁).toEquiv.symm).trans
      c.localSetup.line_card
  obtain ⟨hline,hdisp⟩ := s.critical_line_displacement (w.pair.Ugamma V₃) (w.pair.Aone V₁) hUA hcard
  have hcodim : Module.finrank (ZMod 2) (Additive (Source.Utilde H V₃ V₁) ⧸
      s.image (Source.DH (Source.UH H V₃) (w.pair.Ugamma V₃) (w.pair.Aone V₁))) ≤
      rank (Source.starImage H (w.pair.Ugamma V₃)) := by
    rw [s.quotient_finrank _ (s.line_le_DH _ _ hUgH)]
    exact w.comparison
  have hd := CubicGeometry.degree_six_of_critical act.representation _ eK z hz hzc hp hf hc ho
    _ w.quadratic_member.1 w.quadratic_member.2.1 w.quadratic_member.2.2
    _ _ hcodim hline hdisp
  have hi := CubicGeometry.component_irreducible_of_degree_six act.representation _ eK z hz hzc hp hd
  exact LocalGeometry.DynkinExclusion.Recognition.model_of_irreducible act.representation _
    (LocalGeometry.DynkinExclusion.Recognition.smallInput_of_irreducibleInputs _
      (source_six_cover_irreducibleInputs c e)) hf hi (source_quotient_small_ratio c act)

/-- The recognized source action contradicts the literal V_H/U_H permutation action. -/
theorem source_six_cover_false
    (c : SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (e : (K ⧸ pCore 2 K) ≃* Components.Models.A6Triple)
    (act : QuotientAction H V₃ V₁) : False := by
  let := c.component.normal
  let : Nontrivial (Additive (Source.Utilde H V₃ V₁)) := source_quotient_nontrivial c
  obtain ⟨m⟩ := source_six_cover_model c e act
  let q : (Additive (Source.Utilde H V₃ V₁) ⧸
      (⊥ : Subrepresentation act.representation).toSubmodule) ≃ₗ[ZMod 2]
      Additive (Source.Utilde H V₃ V₁) := Submodule.quotEquivOfEqBot _ rfl
  have ht : (⊥ : Subrepresentation act.representation) ≠ ⊤ := by
    intro he
    exact bot_ne_top (congrArg Subrepresentation.toSubmodule he)
  apply source_six_cover_false_of_quotient_model c e act ⊥ ht
  exact {
    actor := m.actor
    faithful := m.faithful
    component_image := m.component_image
    coordinates := q.trans m.coordinates
    intertwines := by
      intro g v
      induction v using Submodule.Quotient.induction_on with
      | H v => exact m.intertwines g v }
end Action

/-- Exclude the triple-six component from the preceding source context alone. -/
theorem source_no_six_cover
    (c : SourceContext T L V V₁ V₂ V₃ M G₁ H K) :
    ¬ Nonempty ((K ⧸ pCore 2 K) ≃* Components.Models.A6Triple) := by
  rintro ⟨e⟩
  have hH := c.component.local_overgroup
  have hF9 := c.f9 H hH
  let : IsElementaryAbelian 2 (Source.UH H V₃) := c.localSetup.uh_elementary hH
  let raw := Comparison.conjugationAction (c.localSetup.line_le_uh H) hF9.plus_le_H
    (hF9.H_centralizes.trans (Subgroup.centralizer_le_normalizer _)) hF9.commutator_UH_QH_le_point
  exact source_six_cover_false c e {
    line_le := raw.line_le
    seed_le := raw.seed_le
    representation := raw.representation
    conjugation := raw.conjugation }

/-- Exclude the triple Mathieu component through its actual smaller source context. -/
theorem source_no_mathieu_cover
    (c : SourceContext T L V V₁ V₂ V₃ M G₁ H K) :
    ¬ Nonempty ((K ⧸ pCore 2 K) ≃* Components.Models.M22Triple) :=
  source_no_mathieu_cover_of_six_exclusion c (fun _ _ c' => source_no_six_cover c')

/-- All small-cover and Mathieu rows are discharged in the original quotient sieve. -/
theorem source_remainingQuotient_of_field_exclusion
    (c : SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (hfield : ¬ HigherFieldAlternative (K ⧸ pCore 2 K)) :
    RemainingQuotient (K ⧸ pCore 2 K) :=
  remainingQuotient_of_exclusions c.catalogue hfield (source_no_six_cover c)
    (source_no_mathieu c) (source_no_mathieu_cover c)

/-- Apply the completed small-cover sieve to containment, product and movement. -/
theorem source_consequences_of_field_exclusion
    (c : SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (hfield : ¬ HigherFieldAlternative (K ⧸ pCore 2 K)) :
    one L T V₁ ≤ K ∧ RemainingQuotient (K ⧸ pCore 2 K) ∧
      H = K ⊔ (T : Subgroup G) ∧ Source.UH H V₃ = ⁅Source.UH H V₃,K⁆ :=
  source_consequences_of_field_and_six_exclusion c hfield (fun _ _ c' => source_no_six_cover c')
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.OriginalSource
