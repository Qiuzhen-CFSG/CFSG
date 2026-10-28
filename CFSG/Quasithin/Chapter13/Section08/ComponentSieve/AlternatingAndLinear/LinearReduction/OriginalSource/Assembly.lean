module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.OriginalSource.Groups
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.OriginalSource.Overgroup

/-!
# Original binary quotient reduction with one remaining middle-node branch

The original local setup constructs the parabolic inputs. Their uniform
degree-four reduction and the exclusion of the marked middle node imply
the covered local quotient and H* ≅ L₄(2). Applied to the actual lifted
component, this same uniform reduction proves H = G₁ without a general
embedding-classification premise.

The middle-node exclusion is explicitly conditional here. Its strict
orthogonal-module argument is still required; this module does not claim
that the original theorem has been completed. The independent preceding
13.8.21 component conclusions and uniform 13.8.24 exclusion are also
retained. The whole natural module is a separate subsequent argument.

Source: Aschbacher–Smith, 13.8.25, printed pp.959–960/PDF pp.976–977.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.OriginalSource
open TransvectionRecognition.Component.ModelExtension
open FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
open Chapter1.Section02.LocalModels
open Chapter2.ComponentRefinement.LieType.Binary
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ : Subgroup G}
  (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
  (h : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
  (hF9all : ∀ J ∈ Source.Hz (one L T V₁) T G₁ M,
    (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ J).Hypothesis)
  (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
  (hcomm : ⁅V₃, G₁.pCoreIn 2⁆ ≠ ⊥)
  (hsource : SolvableExclusion.Residual.Source1339 L (one L T V₁) (plus L T V₁) T M V V₁)
  (components : ComponentConclusions (one L T V₁) T G₁ M)
  (hmiddle : ∀ (J C : Subgroup G) (_hJ : J ∈ Source.Hz (one L T V₁) T G₁ M)
    (hCJ : C ≤ J) (hC : (C.subgroupOf J).IsCComponent)
    (e : (C ⧸ pCore 2 C) ≃* PSL 4),
    ¬ Parabolics.MiddleNodeMarking J C (one L T V₁) T hCJ hC e)

include d h hF9all hcentral hcomm hsource components hmiddle

/-- Both critical cases are retained; the only extra branch premise is
the exclusion of the actual marked S₈ action. -/
theorem binary_reduction_of_middle_exclusion
    {H K : Subgroup G} {n : ℕ}
    (hH : H ∈ Source.Hz (one L T V₁) T G₁ M) (hKH : K ≤ H)
    (hK : (K.subgroupOf H).IsCComponent) (hn₀ : 3 ≤ n) (hn₁ : n ≤ 5)
    (e : (K ⧸ pCore 2 K) ≃* PSL n) :
    n = 4 ∧ SolvableExclusion.IsTripleCoverSix (L ⧸ pCore 2 L) ∧
      Nonempty (Source.Hstar H ≃* PSL 4) := by
  obtain ⟨hn, halt⟩ := parabolic_reduction d h hF9all hcentral hcomm hsource components
    hH hKH hK hn₀ hn₁ e
  exact ⟨hn, halt.resolve_right (hmiddle H K hH hKH hK (hn ▸ e))⟩

omit d h hF9all hcentral hcomm hsource components hmiddle in
private theorem binary_model {X : Type*} [Group X] {n : ℕ}
    (h : ClassicalGroup.IsPSL X n 2) : Nonempty (X ≃* PSL n) := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h
  let : Fintype F := Fintype.ofFinite F
  let eF : F ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
    simpa only [← Nat.card_eq_fintype_card, Nat.card_zmod] using hF)
  exact ⟨e.trans (Atlas.fieldEquivPSL n eF)⟩

omit d h hF9all hcentral hcomm hsource components hmiddle in
private theorem triple_cover {X : Type*} [Group X]
    (h : SolvableExclusion.IsTripleCoverSix X) : IsAlternatingCover X 6 :=
  ⟨h.1, ⟨mulEquivOfPrimeCardEq h.2.1 (Nat.card_zmod 3)⟩, h.2.2⟩

/-- Group conclusions of original 13.8.25, conditional only on the
remaining middle-node branch and the stated earlier source conclusions.
No GroupFacts, LocalModuleData or embedding-classification record is assumed. -/
theorem source_linear_reduction_of_middle_exclusion
    (hA7 : ∀ {J C : Subgroup G}, J ∈ Source.Hz (one L T V₁) T G₁ M → C ≤ J →
      (C.subgroupOf J).IsCComponent → ¬ IsAlternating (C ⧸ pCore 2 C) 7)
    {H K : Subgroup G} {n : ℕ}
    (hH : H ∈ Source.Hz (one L T V₁) T G₁ M) (hKH : K ≤ H)
    (hK : (K.subgroupOf H).IsCComponent) (hn₀ : 3 ≤ n) (hn₁ : n ≤ 5)
    (hmodel : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) n 2) :
    n = 4 ∧ IsAlternatingCover (L ⧸ pCore 2 L) 6 ∧
      Nonempty (Source.Hstar H ≃* PSL 4) ∧ H = G₁ := by
  have groups := group_facts d h hF9all hcentral hcomm hsource components
  obtain ⟨e⟩ := binary_model hmodel
  obtain ⟨hn, hc, he⟩ := binary_reduction_of_middle_exclusion d h hF9all hcentral hcomm hsource
    components hmiddle hH hKH hK hn₀ hn₁ e
  have uniform : Overgroup.UniformComponentFacts L (one L T V₁) T G₁ M := {
    base_le := components.base_le
    componentList := components.models
    join_eq := groups.supplement
    normal := groups.component_normal
    not_A7 := hA7
    binaryReduction := by
      intro J C m hJ hCJ hC hm₀ hm₁ hmodel
      obtain ⟨eC⟩ := binary_model hmodel
      obtain ⟨hm, hcover, ⟨eJ⟩⟩ := binary_reduction_of_middle_exclusion d h hF9all hcentral hcomm hsource
        components hmiddle hJ hCJ hC hm₀ hm₁ eC
      exact ⟨hm, triple_cover hcover,
        ⟨ZMod 2, inferInstance, inferInstance, Nat.card_zmod 2, ⟨eJ⟩⟩⟩ }
  exact ⟨hn, triple_cover hc, he, source_eq_overgroup d uniform hH hKH hK (hn ▸ hmodel)⟩

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.OriginalSource
