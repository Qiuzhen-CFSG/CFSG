module
public import CFSG.Quasithin.Chapter13.Section05.A5Source.ChiefCatalogue
public import CFSG.Quasithin.Chapter13.Section05.A5Source.ChiefSieveComplete
public import CFSG.Quasithin.Chapter13.Section05.A5Source.NaturalExclusion

/-!
# Recognition from the original nonabelian A₅ source

The proved normal branch supplies the component selection used under the
negation of the degree-five model conclusion. Its actual selected component
has one of three natural central quotients. S₆ contradicts the original chief
count, A₈ contradicts the original core orders, and G₂(2)′ produces an order-four
fixed point inside the elementary second layer. Thus the original ambient
group has the degree-five model conclusion, with only genuine earlier A.3.12
retained and all component, quotient and parabolic premises discharged.
Source: Aschbacher–Smith13.5.17–25, printed pp.922–925.
-/
public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section05.A5Source
open ComponentReduction Section08.Source Recognition Recognition.Configuration
open Recognition.MarkedModule Recognition.MarkedModule.AlternatingParabolics
universe u
variable {G : Type u} [Group G] [Finite G] {D : ChapterF.Section09.Setup G}
  {V₂ : Subgroup G} [IsElementaryAbelian 2 D.V]
  (d : Context D.T D.L D.V D.V₁ V₂ D.Vplus) (h : D.Hypothesis)
  (hA312 : ∀ (Y : Type u) [Group Y] [Finite Y],
    IsSQTK KnownSimple.IsKnownSimple Y → pCore 2 Y = ⊥ → ∀ (S : Sylow 2 Y) (B : Subgroup Y),
    B ∈ ChapterA.Section03.localCComponents S → Chapter1.Section02.A312Conclusion B)
  (hH : D.H ∈ Section08.Source.Hz D.L₁ D.T
    (centralizer (D.V₁ : Set G)) (normalizer (D.L : Set G)))
  (hU : ¬ IsMulCommutative D.UH)
  [(D.V₁.subgroupOf D.UH).Normal] [IsElementaryAbelian 2 (Action.ModuleGroup D)]
  (hnot : ¬ ModelConclusion G 5)
include d h hA312 hH hU hnot

/-- The natural alternatives on the same selected configuration are impossible. -/
theorem source_configuration_false
    (K : Subgroup G) (s : Selected D K) [(componentCentralizer s h).Normal]
    (c : SourceConfiguration s h D.L₁ le_rfl) : False := by
  obtain ⟨hLK,_⟩ := Catalogue.source_local_le_component D K h s d.hypothesis.qtke hH.1.1
    d.third_index hU d.module_card c (residual_quotient_card d hA312 hH hU)
  obtain ⟨_,_,hn,_,_,hnat,_⟩ := source_central_quotient_of_configuration d h hA312 hH
    (fun J hJ hu hn => source13_5_17 d hA312 hJ hu hn) hnot hU K s c
  exact source_natural_quotient_false d h hA312 hH hU hnot K s hLK hn hnat

omit h hnot [(D.V₁.subgroupOf D.UH).Normal] [IsElementaryAbelian 2 (Action.ModuleGroup D)] in
/-- The original nonabelian A₅ source implies its ambient model conclusion. -/
theorem source_modelConclusion : ModelConclusion G 5 := by
  by_contra hnot
  let h := (source13_5_7 d hA312 hH).f9Hypothesis
  let : (D.V₁.subgroupOf D.UH).Normal := Action.point_normal D h
  let : IsElementaryAbelian 2 (Action.ModuleGroup D) := Action.quotient_elementary D h
  obtain ⟨K,s,c,_,_,_,_⟩ := source_exists_simple_component_complete d hA312 hH hU hnot
  let := componentCentralizer_normal s h
    (selected_star_local_normalization s h d.hypothesis.qtke hH.1.1)
  exact source_configuration_false d h hA312 hH hU hnot K s c
end CFSG.Quasithin.Chapter13.Section05.A5Source
