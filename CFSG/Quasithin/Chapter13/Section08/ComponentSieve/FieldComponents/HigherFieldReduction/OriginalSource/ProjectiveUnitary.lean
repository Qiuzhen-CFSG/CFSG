module
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.OriginalSource.ProjectiveFour
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.UnitaryEight.Projective

/-!
# The original PSU₃(8) exclusion and the three remaining higher-field carriers

The faithful source quadratic actor supplies every premise of the native
projective-unitary obstruction. It acts on the literal U_H/V₁, and restricting
to its generated subgroup and an irreducible section preserves its full rank.
This excludes PSU₃(8) before proving L₁ containment. Transport through the
actual component quotient gives the same exclusion for K/O₂(K).

The original Borel reduction therefore retains only PSL₂(4), SL₃(4), and
SU₃(8), with the Borel, local cubic, inverter and full covering centers still
marked. The final application treats arbitrary original overgroups by the
proved KL₁T reduction, preserving their intrinsic component quotient.
The three exceptional contradictions, binary exclusion and final assembly
remain with qt-d-138-fields-source; preceding source inputs retain their
producers through qt-d-1381-source. This does not assert full 13.8.20.
Source: Aschbacher–Smith, 13.8.20, printed pp.954–955.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.OriginalSource
open SourceCompletion TransvectionRecognition.Component.ModelExtension
open LinearThree.Geometry.CoveredProduct.ResidualPlacement
open ExceptionalFields.Containment.Reduction
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}

/-- The original faithful quadratic actor excludes PSU₃(8) on the literal
component star image, before any assertion L₁ ≤ K. -/
theorem source_no_projective_unitaryThree_eight_star
    [IsElementaryAbelian 2 (Source.UH H V₃)]
    (c : FieldComponents.SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (act : LinearThree.SourceAction H V₃ V₁) :
    ¬ ClassicalGroup.IsPSU (Source.starImage H K) 3 8 := by
  intro hm
  let : (Source.starImage H K).Normal :=
    c.component.normal.map _ (QuotientGroup.mk'_surjective _)
  have hF9 := c.f9 H c.component.local_overgroup
  have hf := f9_section_faithful _ hF9 (Comparison.sourceSection act hF9.H_centralizes)
  have hsq := Components.Swapped.LinearTwo.ModuleAlternatives.F918Sections.NoStrong.IrreducibleReduction.sqtk_two_quotient
    (source_sqtk c) (pCore 2 H) pCore_isPGroup
  obtain ⟨A,hA,hAC⟩ := source_quotient_faithful_quadratic_actor c act
  exact ExceptionalFields.UnitaryEight.Projective.no_quadratic_actor act.representation
    (Source.starImage H K) A hsq hm hf hA.1 hA.2.1 hA.2.2 hAC

/-- The intrinsic component two-core quotient cannot be PSU₃(8), under
exactly the preceding original source context. -/
theorem source_no_projective_unitaryThree_eight
    (c : FieldComponents.SourceContext T L V V₁ V₂ V₃ M G₁ H K) :
    ¬ ClassicalGroup.IsPSU (K ⧸ pCore 2 K) 3 8 := by
  intro hm
  let : IsElementaryAbelian 2 (Source.UH H V₃) :=
    c.localSetup.uh_elementary c.component.local_overgroup
  have hKH : K ≤ H := (le_sup_left.trans le_sup_left).trans_eq c.component.generated
  have hF9 := c.f9 H c.component.local_overgroup
  let act := Comparison.conjugationAction (c.localSetup.line_le_uh H) hF9.plus_le_H
    (hF9.H_centralizes.trans (Subgroup.centralizer_le_normalizer _))
    hF9.commutator_UH_QH_le_point
  exact source_no_projective_unitaryThree_eight_star c act
    (hm.of_mulEquiv (Components.componentStarEquiv H K hKH c.component.component).symm)

/-- The three remaining exceptional carriers retain the original local marks;
both projective degree-three alternatives are excluded. -/
theorem source_borel_exceptional_three
    [IsElementaryAbelian 2 (Source.UH H V₃)]
    (c : FieldComponents.SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (act : LinearThree.SourceAction H V₃ V₁)
    (hfield : HigherFieldAlternative (K ⧸ pCore 2 K)) :
    letI : (Source.starImage H K).Normal :=
      c.component.normal.map _ (QuotientGroup.mk'_surjective _)
    ∃ (hKH : K ≤ H) (hT : Chapter1.IsSylowIn 2 (T : Subgroup G) H),
      LocalBorel.borel H K (T : Subgroup G) hKH hT ≤ M ∧
      ∃ (X : Subgroup G) (t : ((T : Subgroup G) ⊓ L : Subgroup G)),
        ((Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) ∧ X = one L T V₁) ∨
          (Nonempty ((L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms) ∧
            X = plus L T V₁ ∧ coreAction (zero L) ⟨t.val,L_normalizes_zero L t.property.2⟩ = 1)) ∧
        LocalBorel.CentralizingCalculation.InvertsTwoCoreQuotient X t.val ∧ V₃ = ⁅V₃,X⁆ ∧
        (ClassicalGroup.IsPSL (Source.starImage H K) 2 4 ∨
          Chapter1.Section02.LocalModels.IsSL (Source.starImage H K) 3 4 ∨
          Chapter1.Section02.LocalModels.IsSU (Source.starImage H K) 3 8) ∧
        OuterStarAction H K
          (QuotientGroup.mk' (pCore 2 H)
            ⟨t.val,c.component.local_overgroup.1.2 (mem_sup_right t.property.1)⟩) := by
  let : (Source.starImage H K).Normal :=
    c.component.normal.map _ (QuotientGroup.mk'_surjective _)
  obtain ⟨hKH,hT,hBM,X,t,hlocal,hinv,hseed,hm,ho⟩ :=
    source_borel_exceptional_models c act hfield
  have hremaining : ClassicalGroup.IsPSL (Source.starImage H K) 2 4 ∨
      Chapter1.Section02.LocalModels.IsSL (Source.starImage H K) 3 4 ∨
      Chapter1.Section02.LocalModels.IsSU (Source.starImage H K) 3 8 := by
    rcases hm with hm | hm | hm | hm
    · exact Or.inl hm
    · exact Or.inr (Or.inl hm)
    · exact (source_no_projective_unitaryThree_eight_star c act hm).elim
    · exact Or.inr (Or.inr hm)
  exact ⟨hKH,hT,hBM,X,t,hlocal,hinv,hseed,hremaining,ho⟩

/-- The current higher-field list on the literal intrinsic component quotient.
Every alternative retains an actual matrix-group isomorphism. -/
theorem source_higher_field_exceptional_list
    (c : FieldComponents.SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (hfield : HigherFieldAlternative (K ⧸ pCore 2 K)) :
    ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 4 ∨
      Chapter1.Section02.LocalModels.IsSL (K ⧸ pCore 2 K) 3 4 ∨
      Chapter1.Section02.LocalModels.IsSU (K ⧸ pCore 2 K) 3 8 := by
  let : IsElementaryAbelian 2 (Source.UH H V₃) :=
    c.localSetup.uh_elementary c.component.local_overgroup
  have hKH : K ≤ H := (le_sup_left.trans le_sup_left).trans_eq c.component.generated
  have hF9 := c.f9 H c.component.local_overgroup
  let act := Comparison.conjugationAction (c.localSetup.line_le_uh H) hF9.plus_le_H
    (hF9.H_centralizes.trans (Subgroup.centralizer_le_normalizer _))
    hF9.commutator_UH_QH_le_point
  obtain ⟨_,_,_,_,_,_,_,_,hm,_⟩ := source_borel_exceptional_three c act hfield
  let eK := Components.componentStarEquiv H K hKH c.component.component
  rcases hm with hm | hm | hm
  · exact Or.inl (hm.of_mulEquiv eK)
  · obtain ⟨F,hF,hfin,hcard,⟨e⟩⟩ := hm
    exact Or.inr (Or.inl ⟨F,hF,hfin,hcard,⟨eK.trans e⟩⟩)
  · obtain ⟨F,hF,hfin,J,hcard,hconj,⟨e⟩⟩ := hm
    exact Or.inr (Or.inr ⟨F,hF,hfin,J,hcard,hconj,⟨eK.trans e⟩⟩)

/-- Apply the projective exclusion to each component of an unrestricted
original overgroup; H=KL₁T is supplied only inside the reduced context. -/
theorem original_no_projective_unitaryThree_eight
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (h : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hF9 : ∀ J ∈ Source.Hz (one L T V₁) T G₁ M,
      (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ J).Hypothesis)
    (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
    (hcomm : ⁅V₃,G₁.pCoreIn 2⁆ ≠ ⊥)
    (hH : H ∈ Source.Hz (one L T V₁) T G₁ M)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent) :
    ¬ ClassicalGroup.IsPSU (K ⧸ pCore 2 K) 3 8 := by
  let c := Overgroups.context_of_original d h hF9 hcentral hcomm hH
  exact source_no_projective_unitaryThree_eight (Overgroups.reducedContext c K hKH hK)

/-- The same three-carrier list for every component of an unrestricted
original overgroup. Its reduction to KL₁T does not change K/O₂(K). -/
theorem original_higher_field_exceptional_list
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (h : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hF9 : ∀ J ∈ Source.Hz (one L T V₁) T G₁ M,
      (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ J).Hypothesis)
    (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
    (hcomm : ⁅V₃,G₁.pCoreIn 2⁆ ≠ ⊥)
    (hH : H ∈ Source.Hz (one L T V₁) T G₁ M)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hfield : HigherFieldAlternative (K ⧸ pCore 2 K)) :
    ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 4 ∨
      Chapter1.Section02.LocalModels.IsSL (K ⧸ pCore 2 K) 3 4 ∨
      Chapter1.Section02.LocalModels.IsSU (K ⧸ pCore 2 K) 3 8 := by
  let c := Overgroups.context_of_original d h hF9 hcentral hcomm hH
  exact source_higher_field_exceptional_list (Overgroups.reducedContext c K hKH hK) hfield

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.OriginalSource
