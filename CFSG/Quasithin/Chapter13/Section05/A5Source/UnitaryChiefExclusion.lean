module
public import CFSG.Quasithin.Chapter13.Section05.A5Source.ChiefSieveApplication
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Catalogue.SourceUnitary

/-!
# The original A₅ chief sieve with the unitary row excluded

Keep the component and configuration chosen by the original source sieve.
On every noncentral irreducible chief image, its actual marked involution
excludes the remaining natural unitary row. The existing full catalogue and
seven exclusions are retained, with this eighth exclusion attached to the
same action. Only the original earlier A.3.12 and normal-branch 13.5.17 inputs
remain explicit; neither a new actor nor a model-exclusion premise is assumed.

Source: Aschbacher–Smith 13.5.21, printed pp.923–924, especially condition (iii)
and the subsequent B.4.5 action-row elimination.
-/

public section
open Subgroup Theory.GroupTheory
open BenderSuzuki.MatrixGroups
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section05.A5Source
open Section06.TerminalContradiction.Ratio Section08
open ComponentReduction Recognition Recognition.Configuration Recognition.Catalogue
open Representation Representation.BinaryOffender
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G} [IsElementaryAbelian 2 V]
  (d : Context T L V V₁ V₂ V₃)
  (hA312 : ∀ (Y : Type u) [Group Y] [Finite Y],
    IsSQTK KnownSimple.IsKnownSimple Y → pCore 2 Y = ⊥ → ∀ (S : Sylow 2 Y) (B : Subgroup Y),
    B ∈ ChapterA.Section03.localCComponents S → Chapter1.Section02.A312Conclusion B)
  (hH : H ∈ Source.Hz (residualCentralizer L V₁) (T : Subgroup G)
    (centralizer (V₁ : Set G)) (normalizer (L : Set G)))
  (hU : ¬ IsMulCommutative (Source.UH H V₃))
  (h17 : ∀ J ∈ Source.Hz (residualCentralizer L V₁) (T : Subgroup G)
    (centralizer (V₁ : Set G)) (normalizer (L : Set G)),
    ¬ IsMulCommutative (Source.UH J V₃) → ((residualCentralizer L V₁).subgroupOf J).Normal →
      ClassicalGroup.IsPSU G 4 2 ∨ ClassicalGroup.IsPSL G 4 3)
  (hnot : ¬ ModelConclusion G 5)
include d hA312 hH hU h17 hnot

/-- The same selected component has the full chief sieve and no natural
unitary row; the marked source witness is discharged internally. -/
theorem source_component_chief_sieve_with_unitary_exclusion :
    let D : ChapterF.Section09.Setup G := ⟨T, L, V, V₃, V₁, H⟩
    let hf : D.Hypothesis := (source13_5_7 d hA312 hH).f9Hypothesis
    let := Action.point_normal D hf
    let := Action.quotient_elementary D hf
    ∃ K : Subgroup G, ∃ s : Selected D K,
      let := componentCentralizer_normal s hf
        (selected_star_local_normalization s hf d.hypothesis.qtke hH.1.1)
      SourceConfiguration s hf D.L₁ le_rfl ∧
        ∀ U N : Subrepresentation (representation D K hf),
          ¬ component D K ≤ (chiefRepresentation D K hf U N).ker →
          IsIrreducible (chiefRepresentation D K hf U N) →
          ChiefSieve (imageRepresentation (chiefRepresentation D K hf U N)) ∧
            ∀ (F : BinaryField) (n : ℕ), 2 ≤ n → F.degree = 2 * n →
              ∀ J : HermitianForm 3 F.Carrier,
                ¬ UnitaryChiefAction (imageRepresentation (chiefRepresentation D K hf U N)) F J := by
  intro D hf
  let := Action.point_normal D hf
  let := Action.quotient_elementary D hf
  obtain ⟨K, s, hc, hsieve⟩ := source_component_chief_sieve d hA312 hH hU h17 hnot
  let := componentCentralizer_normal s hf
    (selected_star_local_normalization s hf d.hypothesis.qtke hH.1.1)
  refine ⟨K, s, hc, ?_⟩
  intro U N hn hirr
  exact ⟨hsieve U N hn hirr,
    source_chief_not_unitary D K hf s d.hypothesis.qtke hH.1.1
      d.third_index hU d.module_card U N hn hirr⟩

end CFSG.Quasithin.Chapter13.Section05.A5Source
