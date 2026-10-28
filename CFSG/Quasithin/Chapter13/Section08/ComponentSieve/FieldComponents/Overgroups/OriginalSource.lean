module
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.Overgroups
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Source

/-!
# Original-source assembly on unrestricted overgroups

The published 13.8.16–17 theorems supply normality and the concrete catalogue
for each relative component of the actual H. The literal quotient equivalence
transports the catalogue from K* to K/O₂(K), and the original 13.3.9 producer
supplies the residual input. The involution-centralizer inheritance theorem
gives SQTK on H itself, rather than only on H/O₂(H).

Applying the unrestricted-overgroup argument gives containment, the remaining
quotient list, the set product and commutator generation. The last application
constructs the precise ComponentConclusions and GroupFacts of the later linear
sieve. Only higher-field exclusion and the whole-quotient binary exclusion
remain with qt-d-138-fields-source. The preceding LocalSetup, maximal-local,
F.9 and 13.5.4 inputs retain their producers qt-d-135-preparation-source and
qt-d-1378-source, through qt-d-138-components-source; final unconditional
source discharge remains with qt-d-1381-source.
Source: Aschbacher–Smith, 13.8.21(1–4), printed pp.955–957, applied in
13.8.25, pp.959–960.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.Overgroups
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative Pointwise
open LinearThree.Geometry.CoveredProduct.ResidualPlacement
open SourceCompletion TransvectionRecognition.Component.ModelExtension
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ : Subgroup G}
  (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
  (h : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
  (hF9 : ∀ J ∈ Source.Hz (one L T V₁) T G₁ M,
    (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ J).Hypothesis)
  (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
  (hcomm : ⁅V₃,G₁.pCoreIn 2⁆ ≠ ⊥)

/-- Construct the unrestricted context from the published earlier source
normality, catalogue and residual theorems. The SQTK assertion is on H itself. -/
noncomputable def context_of_original {H : Subgroup G}
    (hH : H ∈ Source.Hz (one L T V₁) T G₁ M) : Context T L V V₁ V₂ V₃ M G₁ H := by
  have hs : IsSQTK KnownSimple.IsKnownSimple H := by
    obtain ⟨z,hz,_,_,_,hG⟩ := LocalFitting.line_involution d
    have hHN : H ≤ centralizer ({z} : Set G) := hH.2.1.trans hG
    exact (IsSQTK.equiv (subgroupOfEquivOfLe hHN)).mp
      ((d.counterexample.qtke.involution_centralizer_sqtk hz).subgroup
        (H.subgroupOf (centralizer ({z} : Set G))))
  exact {
    localSetup := d
    maximal := h
    f9 := hF9
    centralizer := hcentral
    noncentral_core := hcomm
    earlier1339 := Components.EarlierResidual.original_source d h
    sqtk := hs
    member := hH
    normal := fun K hKH hK => Components.original_component_normal d h hF9 hcentral hcomm hH hKH hK
    catalogue := fun K hKH hK =>
      (Components.original_component_catalogue d h hF9 hcentral hcomm hH hKH hK).of_mulEquiv
        (Components.componentStarEquiv H K hKH hK) }

variable
    (fields : ∀ {J C : Subgroup G}, SourceContext T L V V₁ V₂ V₃ M G₁ J C →
      ¬ HigherFieldAlternative (C ⧸ pCore 2 C))
include d h hF9 hcentral hcomm fields

/-- All nonbinary clauses of 13.8.21 for an arbitrary original overgroup,
with only higher-field exclusion still required from the field-sieve owner. -/
theorem original_consequences {H K : Subgroup G}
    (hH : H ∈ Source.Hz (one L T V₁) T G₁ M)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent) :
    one L T V₁ ≤ K ∧ RemainingQuotient (K ⧸ pCore 2 K) ∧
      (H : Set G) = (K : Set G) * (T : Set G) ∧
      Source.UH H V₃ = ⁅Source.UH H V₃,K⁆ := by
  let c := context_of_original d h hF9 hcentral hcomm hH
  have hf (C : Subgroup G) (hCH : C ≤ H) (hC : (C.subgroupOf H).IsCComponent) :=
    fields (reducedContext c C hCH hC)
  obtain ⟨hLK,hm⟩ := containment_and_models c hf K hKH hK
  exact ⟨hLK,hm,product c hf K hKH hK,commutator_eq c hf K hKH hK⟩

variable
    (binary : ∀ {J C : Subgroup G}, SourceContext T L V V₁ V₂ V₃ M G₁ J C →
      ¬ Nonempty (Source.Hstar J ≃* Matrix.PSL3Two.PSL))
include binary

/-- The complete input to the original linear sieve, after the two remaining
field-sieve exclusions. No component, catalogue, residual, containment,
product or automorphism conclusion is an additional input. -/
theorem original_component_conclusions :
    AlternatingAndLinear.LinearReduction.OriginalSource.ComponentConclusions (one L T V₁) T G₁ M :=
  component_conclusions (fun _J hJ => ⟨context_of_original d h hF9 hcentral hcomm hJ⟩) fields binary

/-- Apply unrestricted 13.8.21 to the actual binary-parabolic consumer. -/
theorem original_linear_group_facts :
    AlternatingAndLinear.LinearReduction.SourceReduction.GroupFacts L (one L T V₁) T V V₁ V₃ G₁ M :=
  AlternatingAndLinear.LinearReduction.OriginalSource.group_facts d h hF9 hcentral hcomm
    (Components.EarlierResidual.original_source d h)
    (original_component_conclusions d h hF9 hcentral hcomm fields binary)

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.Overgroups
