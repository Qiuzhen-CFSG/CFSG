module
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.OriginalSource.Action
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CriticalSource
public import Theory.Representation.PerfectInvolutionExtension
public import Theory.Representation.BinaryOffender.NormalCubic

/-!
# Transvection-free original external field geometry

The faithful original quotient module has dimension greater than two, because
its nontrivial perfect component has no faithful binary action in smaller
dimension. The normal external cubic acts without fixed vectors, so a
rank-one displacement would force a fixed displacement line. This excludes
transvections and supplies the selected critical actor of rank greater than
one, with its quadratic action and conjugate placement in the original core.

The final application constructs the literal source action and applies the
original Borel dichotomy. It needs no FF recognition and makes no assertion
that the component moved space is the whole module. External and exceptional
field elimination remain with qt-d-138-fields-source; qt-d-1381-source
supplies the preceding original SourceContext.
Source: Aschbacher–Smith, 13.8.18(4) and 13.8.20(a), printed pp.953–954.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.OriginalSource
open SourceCompletion TransvectionRecognition.Component.ModelExtension
open LinearThree.Geometry.CoveredProduct.ResidualPlacement
open ExternalModules
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}
  [IsElementaryAbelian 2 (Source.UH H V₃)]

/-- Faithfulness on the original nontrivial perfect component forces the
literal quotient module to have dimension greater than two. -/
theorem source_quotient_dimension_gt_two
    (c : FieldComponents.SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (act : LinearThree.SourceAction H V₃ V₁) :
    2 < Module.finrank (ZMod 2) (Additive (Source.Utilde H V₃ V₁)) := by
  have hH := c.component.local_overgroup
  have hF9 := c.f9 H hH
  have hf := f9_section_faithful _ hF9 (Comparison.sourceSection act hF9.H_centralizes)
  let Ks := Source.starImage H K
  let hqs : IsQuasisimple Ks :=
    (SolvableSource.component_fitting_source c.localSetup c.maximal c.f9
      c.centralizer c.noncentral_core c.earlier1339 hH K c.component.component).2
  let : IsSimpleGroup (Ks ⧸ center Ks) := hqs.simple
  let : Nontrivial Ks := (QuotientGroup.mk'_surjective (center Ks)).nontrivial
  by_contra! hd
  obtain ⟨k,hk⟩ := exists_ne (1 : Ks)
  apply hk
  apply Subtype.ext
  apply hf
  apply LinearMap.ext
  intro v
  change act.representation (Ks.subtype k) v = act.representation (1 : Source.Hstar H) v
  rw [map_one]
  exact Representation.PerfectInvolutionExtension.small_action_trivial
    (act.representation.comp Ks.subtype) hd k v

/-- The normal external cubic excludes every transvection on the original
U_H/V₁ without any FF or whole-module recognition premise. -/
theorem source_external_no_transvections
    (c : FieldComponents.SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (act : LinearThree.SourceAction H V₃ V₁)
    (X : Subgroup G) (ha : ExternalXAlternative H K X)
    (hs : ExternalSourceData H K X) (hseed : V₃ = ⁅V₃,X⁆)
    (g : Source.Hstar H) : fixedCodim act.representation (zpowers g) ≠ 1 := by
  let : (Source.starImage H X).Normal := hs.2.2.1
  obtain ⟨s,_,_,hm,_,hf,_⟩ := source_external_cubic_action act X ha hs hseed
  have hfix : fixedSpace act.representation (Source.starImage H X) = ⊥ := by
    apply bot_unique
    intro v hv
    apply hf
    exact hv ⟨s InvertedCubicTensor.cubic, by
      rw [←hm]
      exact mem_map_of_mem s (by rw [Equiv.Perm.mem_alternatingGroup]; decide)⟩
  exact no_transvections_of_normal_cubic act.representation (Source.starImage H X)
    hs.1 hfix (source_quotient_dimension_gt_two c act) g

/-- All critical selection, rank, conjugation and quadraticity premises in
the external field branch now follow from the original source context. -/
theorem source_external_selected_witness
    (c : FieldComponents.SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (act : LinearThree.SourceAction H V₃ V₁)
    (X : Subgroup G) (ha : ExternalXAlternative H K X)
    (hs : ExternalSourceData H K X) (hseed : V₃ = ⁅V₃,X⁆) :
    Nonempty (CriticalInputs.SelectedWitness L (T : Subgroup G) H V
      (one L T V₁) V₃ V₁ act.representation) := by
  have hH := c.component.local_overgroup
  have hqs := (SolvableSource.component_fitting_source c.localSetup c.maximal c.f9
    c.centralizer c.noncentral_core c.earlier1339 hH K c.component.component).2
  exact CriticalSource.exists_selected_witness c.localSetup hH (c.f9 H hH)
    (by rw [←c.component.generated,sup_assoc]) c.component.component c.component.normal hqs
    c.centralizer c.noncentral_core act.representation act.conjugation
    (fun g => by
      rw [←fixedCodim_zpowers_eq_displacement_rank]
      exact source_external_no_transvections c act X ha hs hseed g)
omit [IsElementaryAbelian 2 (Source.UH H V₃)] in
/-- The original higher-field dichotomy now includes all critical geometry
in its external branch, on the same faithful quotient action. -/
theorem source_higher_field_critical_geometry
    (c : FieldComponents.SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (hfield : HigherFieldAlternative (K ⧸ pCore 2 K)) :
    letI : IsElementaryAbelian 2 (Source.UH H V₃) :=
      c.localSetup.uh_elementary c.component.local_overgroup
    ∃ act : LinearThree.SourceAction H V₃ V₁,
      Function.Injective act.representation ∧
      ((∃ X : Subgroup G,
          ExternalXAlternative H K X ∧ ExternalSourceData H K X ∧ V₃ = ⁅V₃,X⁆ ∧
          (∀ g, fixedCodim act.representation (zpowers g) ≠ 1) ∧
          Nonempty (CriticalInputs.SelectedWitness L (T : Subgroup G) H V
            (one L T V₁) V₃ V₁ act.representation)) ∨
        ∃ t : ((T : Subgroup G) ⊓ L : Subgroup G),
          ExceptionalOuterAlternative.{u,0} H K
            (QuotientGroup.mk' (pCore 2 H)
              ⟨t.val,c.component.local_overgroup.1.2 (mem_sup_right t.property.1)⟩)) := by
  let : IsElementaryAbelian 2 (Source.UH H V₃) :=
    c.localSetup.uh_elementary c.component.local_overgroup
  have hF9 := c.f9 H c.component.local_overgroup
  let act := Comparison.conjugationAction (c.localSetup.line_le_uh H) hF9.plus_le_H
    (hF9.H_centralizes.trans (Subgroup.centralizer_le_normalizer _))
    hF9.commutator_UH_QH_le_point
  refine ⟨act,f9_section_faithful _ hF9 (Comparison.sourceSection act hF9.H_centralizes),?_⟩
  obtain ⟨_,_,_,X,t,_,_,hseed,hb⟩ := source_borel_structure c hfield
  rcases hb with ⟨hx,_,hs⟩ | ho
  · exact Or.inl ⟨X,hx.1,hs,hseed,source_external_no_transvections c act X hx.1 hs hseed,
      source_external_selected_witness c act X hx.1 hs hseed⟩
  · exact Or.inr ⟨t,ho⟩

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.OriginalSource
