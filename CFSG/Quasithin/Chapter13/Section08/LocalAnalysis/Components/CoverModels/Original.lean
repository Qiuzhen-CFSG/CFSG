module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.CoverModels.SourceApplication
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.Solvable.Original
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.QuasisimpleContaining

/-!
# The concrete component catalogue on the original source quotient

The point normalizer is two-local, so the original simple-QTKE hypothesis
gives SQTK for H. Passage through its two-core preserves the odd-rank
bound and the proper-K catalogue. The actual A.3.6 theorem therefore
classifies the quasisimple component K* as simple or a central triple
cover. The existing cover recognition identifies the concrete carriers.

Only the F.9.18 model clause and the Suzuki exclusion remain in the
catalogue implication; neither SQTK, quasisimplicity, A.3.6 nor cover
recognition is an extra premise. F.9.18 and 13.8.16 must still be proved
before this conditional implication establishes 13.8.17.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
A.3.6, printed p.43; F.9.18(4), pp.325–326; 13.8.15–17, pp.952–953.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section08.Components.CoverModels
open SourceCompletion TransvectionRecognition.Component.ModelExtension
open ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement

variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}
  (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
  (hH : H ∈ Source.Hz (one L T V₁) T G₁ M)

include d hH in
/-- The literal quotient H/O₂(H) inherits the full known-simple SQTK
hypothesis from the original point normalizer. -/
theorem original_star_sqtk : IsSQTK KnownSimple.IsKnownSimple (Source.Hstar H) := by
  have hp : IsPGroup 2 V₁ := IsPGroup.of_card (n := 1) (by simpa using d.line_card)
  have hn : V₁ ≠ ⊥ := by
    intro he
    have hc := d.line_card
    rw [he, card_bot] at hc
    contradiction
  have hloc : IsTwoLocal (normalizer (V₁ : Set G)) := ⟨V₁, hn, hp, rfl⟩
  have hHN : H ≤ normalizer (V₁ : Set G) := d.first_normalizer ▸ hH.2.1
  have hsq := (IsSQTK.equiv (subgroupOfEquivOfLe hHN)).mp
    ((d.counterexample.qtke.twoLocal_sqtk hloc).subgroup (H.subgroupOf (normalizer (V₁ : Set G))))
  exact ⟨LocalFitting.star_odd_rank d hH, hsq.isKGroup.quotient (pCore 2 H)⟩

variable
  (h : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
  (hF9all : ∀ J ∈ Source.Hz (one L T V₁) T G₁ M,
    (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ J).Hypothesis)
  (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
  (hcomm : ⁅V₃, G₁.pCoreIn 2⁆ ≠ ⊥)
  (hsource : SolvableExclusion.Residual.Source1339 L (one L T V₁) (plus L T V₁) T M V V₁)
  (hK : (K.subgroupOf H).IsCComponent)

include d hH h hF9all hcentral hcomm hsource hK in
/-- The original finite component has a concrete catalogue model or is
Suzuki, conditional only on the still-required F.9.18 model clause. -/
theorem original_catalogue_or_suzuki
    (hF : Models.F918Models (Source.starImage H K)) :
    Models.ComponentModelOrSuzuki (Source.starImage H K) := by
  let : IsQuasisimple (Source.starImage H K) :=
    (SolvableSource.component_fitting_source d h hF9all hcentral hcomm hsource hH K hK).2
  have hA := ChapterA.Section03.SourceEmbeddings.quasisimple_containing_component_models_knownSimple
    (original_star_sqtk d hH) (pCore_quotient_pCore_eq_bot 2) (starImage_isCComponent H K hK)
  apply SourceApplication.classified_of_source hF
  exact hA.elim (fun hs => Or.inl hs.1) Or.inr

include d hH h hF9all hcentral hcomm hsource hK in
/-- Apply 13.8.16's intrinsic quotient exclusion to K* via its actual
quotient equivalence. All central-cover inputs have been discharged. -/
theorem original_catalogue (hKH : K ≤ H)
    (hF : Models.F918Models (Source.starImage H K))
    (hno : ∀ m : ℕ, 1 ≤ m → ¬ Nonempty ((K ⧸ pCore 2 K) ≃*
      BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)) :
    Models.ComponentModel (Source.starImage H K) := by
  apply (original_catalogue_or_suzuki d hH h hF9all hcentral hcomm hsource hK hF).of_no_suzuki
  intro m hm he
  exact hno m hm (he.map ((componentStarEquiv H K hKH hK).trans ·))

end CFSG.Quasithin.Chapter13.Section08.Components.CoverModels
