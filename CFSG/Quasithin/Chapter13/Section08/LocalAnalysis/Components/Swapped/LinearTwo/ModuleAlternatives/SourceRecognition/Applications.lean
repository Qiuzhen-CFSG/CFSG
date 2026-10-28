module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.ModuleAlternatives.SourceRecognition.Quotients
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.ModuleAlternatives.SourceRecognition.Orthogonal

/-!
# Applications to the original exchanged component

The cubic argument lifts an orthogonal identification of the central
quotient to the whole source module. An identified orthogonal quotient
also excludes the FF branch, so the recognition problem can be confined
to the faithful irreducible maximal quotient. Cross-factor fixation on
that literal quotient feeds the original projection contradiction.

The separate refinement application uses the proved diagonal reduction
to n = 2 and both action transports before applying the original module
alternatives consumer. The quotient classification and refined F.9
classification remain explicit obligations, not theorems of this module.

Source: Aschbacher–Smith, 13.8.16(1), printed pp.952–953.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.SourceRecognition
open SourceCompletion TransvectionRecognition.Component.ModelExtension
open ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
open ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}
  (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
  (h : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
  (hF9all : ∀ J ∈ Source.Hz (one L T V₁) T G₁ M,
    (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ J).Hypothesis)
  (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
  (hcomm : ⁅V₃, G₁.pCoreIn 2⁆ ≠ ⊥)
  (hsource : SolvableExclusion.Residual.Source1339 L (one L T V₁) (plus L T V₁) T M V V₁)
  (hH : H ∈ Source.Hz (one L T V₁) T G₁ M)
  (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
  (hgen : conjugateSpanBy K (T : Subgroup G) ⊔ (one L T V₁ ⊔ (T : Subgroup G)) = H)
  (hmoving : conjugateSpanBy K (T : Subgroup G) ≠ K)
include d h hF9all hcentral hcomm hsource hH hKH hK hgen hmoving

/-- Orthogonal recognition on the actual maximal central quotient already
recognizes the whole source module. The central-cover kernel is eliminated
here; recognition of the quotient remains a separate obligation. -/
theorem source_orthogonal_of_central_quotient {n : ℕ} (hn : 2 ≤ n)
    (hmodel : ClassicalGroup.IsPSL (Source.starImage H K) 2 (2 ^ n))
    [IsElementaryAbelian 2 (Source.UH H V₃)]
    (ρ : Representation (ZMod 2) (Source.Hstar H) (SourceSpace H V₃ V₁))
    (hρ : IsSourceAction H V₃ V₁ ρ)
    (W : Subrepresentation ρ)
    (hc : W.toSubmodule = fixedSpace ρ
      (Source.starImage H (conjugateSpanBy K (T : Subgroup G))))
    (hm : HasOrthogonalFourOrbit W.quotientRepresentation
      (Source.starImage H (conjugateSpanBy K (T : Subgroup G)))) :
    W = ⊥ ∧ HasOrthogonalFourOrbit ρ
      (Source.starImage H (conjugateSpanBy K (T : Subgroup G))) := by
  exact orthogonal_quotient_is_whole ρ _ W hc.le
    (Original.moved_eq_top d h hF9all hcentral hcomm hsource
      hH hKH hK hmoving hn hmodel hgen ρ hρ) hm

end CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.SourceRecognition

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.SourceRecognition
open F918Sections.Refinement

/-- The refined source output gives the literal quotient or fixed-field
whole-module alternative. This transport does not assert the refinement. -/
theorem alternatives_of_fieldFour_refinement
    {D U : Type*} [Group D] [AddCommGroup U] [Module (ZMod 2) U] [Nontrivial U]
    (ρ : Representation (ZMod 2) D U) (A N : Subgroup D) (t : D)
    (h : Conclusion ρ A N t 2) :
    HasCrossFactorQuotient ρ A (A.conjBy t⁻¹) ∨ HasOrthogonalFourOrbit ρ N := by
  cases h with
  | factors h =>
    exact Or.inl (crossFactorQuotient_of_crossFixation ρ A _ h.first_fixed h.second_fixed)
  | orthogonal F hF identification =>
    exact Or.inr (orthogonalFour_of_identification ρ N hF identification)

open SourceCompletion TransvectionRecognition.Component.ModelExtension
open ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
open ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}
  (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
  (h : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
  (hF9all : ∀ J ∈ Source.Hz (one L T V₁) T G₁ M,
    (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ J).Hypothesis)
  (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
  (hcomm : ⁅V₃, G₁.pCoreIn 2⁆ ≠ ⊥)
  (hsource : SolvableExclusion.Residual.Source1339 L (one L T V₁) (plus L T V₁) T M V V₁)
  (hH : H ∈ Source.Hz (one L T V₁) T G₁ M)
  (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
  (hgen : conjugateSpanBy K (T : Subgroup G) ⊔ (one L T V₁ ⊔ (T : Subgroup G)) = H)
  (hmoving : conjugateSpanBy K (T : Subgroup G) ≠ K)
include d h hF9all hcentral hcomm hsource hH hKH hK hgen hmoving

/-- Literal application to the original projection contradiction. The only
module input here is the refined F.9.18(5) output, which still needs its
field-four source proof; the field degree and both action transports are
proved from the original data. -/
theorem source_orthogonal_of_refinement {n : ℕ} (hn : 2 ≤ n)
    (hmodel : ClassicalGroup.IsPSL (Source.starImage H K) 2 (2 ^ n))
    [IsElementaryAbelian 2 (Source.UH H V₃)]
    (ρ : Representation (ZMod 2) (Source.Hstar H) (SourceSpace H V₃ V₁))
    (hρ : IsSourceAction H V₃ V₁ ρ)
    {t : G} (ht : t ∈ T) (htn : t ∉ normalizer (K : Set G))
    (hrefined : Conclusion ρ (Source.starImage H K)
      (Source.starImage H (conjugateSpanBy K (T : Subgroup G)))
      (QuotientGroup.mk' (pCore 2 H) ⟨t,hH.1.2 (show t ∈ one L T V₁ ⊔ (T : Subgroup G) from (show (T : Subgroup G) ≤ one L T V₁ ⊔ (T : Subgroup G) from le_sup_right) ht)⟩) n) :
    HasOrthogonalFourOrbit ρ
      (Source.starImage H (conjugateSpanBy K (T : Subgroup G))) := by
  have hn2 := (Original.diagonal_cosets d h hF9all hcentral hcomm hsource
    hH hKH hK hgen hmoving hn hmodel ht htn).1
  have hseed := seed_ne_bot H V₃ V₁ (not_le_of_gt (hF9all H hH).point_lt)
  have hnU : Nontrivial (SourceSpace H V₃ V₁) := by
    by_contra! hz
    let : Subsingleton (SourceSpace H V₃ V₁) := hz
    exact hseed (Submodule.eq_bot_of_subsingleton)
  let : Nontrivial (SourceSpace H V₃ V₁) := hnU
  have halt := alternatives_of_fieldFour_refinement ρ _ _ _ (hn2 ▸ hrefined)
  rw [source_star_inverse_conjugate d h hF9all hcentral hcomm hsource hH hKH hK hmoving ht] at halt
  exact Original.orthogonal_of_module_alternatives d h hF9all hcentral hcomm hsource
    hH hKH hK hgen hmoving hn hmodel ρ hρ ht htn halt

end CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.SourceRecognition

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.SourceRecognition
open SourceCompletion TransvectionRecognition.Component.ModelExtension
open ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
open ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}
  (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
  (h : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
  (hF9all : ∀ J ∈ Source.Hz (one L T V₁) T G₁ M,
    (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ J).Hypothesis)
  (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
  (hcomm : ⁅V₃, G₁.pCoreIn 2⁆ ≠ ⊥)
  (hsource : SolvableExclusion.Residual.Source1339 L (one L T V₁) (plus L T V₁) T M V V₁)
  (hH : H ∈ Source.Hz (one L T V₁) T G₁ M)
  (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
  (hgen : conjugateSpanBy K (T : Subgroup G) ⊔ (one L T V₁ ⊔ (T : Subgroup G)) = H)
  (hmoving : conjugateSpanBy K (T : Subgroup G) ≠ K)
include d h hF9all hcentral hcomm hsource hH hKH hK hgen hmoving

/-- The remaining recognition can be confined to a faithful irreducible
literal quotient. Cross-factor fixation on it gives the source projection
contradiction. An orthogonal identification forces the central branch and
lifts to the entire source module by the commuting cubic argument.
No classification of that quotient is assumed or asserted. -/
theorem exists_source_quotient_reduction {n : ℕ} (hn : 2 ≤ n)
    (hmodel : ClassicalGroup.IsPSL (Source.starImage H K) 2 (2 ^ n))
    [IsElementaryAbelian 2 (Source.UH H V₃)]
    (ρ : Representation (ZMod 2) (Source.Hstar H) (SourceSpace H V₃ V₁))
    (hρ : IsSourceAction H V₃ V₁ ρ)
    {t : G} (ht : t ∈ T) (htn : t ∉ normalizer (K : Set G)) :
    ∃ W : Subrepresentation ρ, W ≠ ⊤ ∧
      W.quotientRepresentation.IsIrreducible ∧
      Function.Injective W.quotientRepresentation ∧
      (sourceSeedSpace H V₃ V₁).map W.toSubmodule.mkQ ≠ ⊥ ∧
      (((subspaceCommutator W.quotientRepresentation ⊤ (Source.starImage H K) ≤
            fixedSpace W.quotientRepresentation (Source.starImage H (K.conjBy t)) ∧
          subspaceCommutator W.quotientRepresentation ⊤ (Source.starImage H (K.conjBy t)) ≤
            fixedSpace W.quotientRepresentation (Source.starImage H K)) ∨
        HasOrthogonalFourOrbit W.quotientRepresentation
          (Source.starImage H (conjugateSpanBy K (T : Subgroup G)))) →
      HasOrthogonalFourOrbit ρ
        (Source.starImage H (conjugateSpanBy K (T : Subgroup G)))) := by
  obtain ⟨W,hW,hirr,hfaith,hseed,halt⟩ := source_central_kernel_dichotomy
    d h hF9all hcentral hcomm hsource hH hKH hK hgen hmoving hn hmodel ρ hρ
  refine ⟨W,hW,hirr,hfaith,hseed,?_⟩
  rintro (⟨ha,hb⟩ | hm)
  · exact Original.orthogonal_of_module_alternatives d h hF9all hcentral hcomm hsource
      hH hKH hK hgen hmoving hn hmodel ρ hρ ht htn (Or.inl ⟨W,hW,ha,hb⟩)
  · rcases halt with hff | ⟨hc,_⟩
    · obtain ⟨F,hF,hfin,hchar,a,_,_,ha,_⟩ := exists_source_exchangedActor
        d h hF9all hcentral hcomm hsource hH hKH hK hgen hmoving hn hmodel ht htn
      let : a.orbit.Normal := a.orbit_normal
      have hnot := orthogonal_image_not_ff W.quotientRepresentation a.orbit (ha.symm ▸ hm)
      exact (hnot hff.2).elim
    · exact (source_orthogonal_of_central_quotient d h hF9all hcentral hcomm hsource
        hH hKH hK hgen hmoving hn hmodel ρ hρ W hc hm).2

end CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.SourceRecognition
