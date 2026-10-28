module
public import CFSG.Quasithin.Chapter13.Section05.A5Source.NormalRecognition
public import CFSG.Quasithin.Chapter13.Section05.A5Source.UnitaryChiefExclusion
public import CFSG.Quasithin.Chapter13.Section05.A5Source.ComponentStructure

/-!
# The original A₅ chief sieve after normal-branch recognition

The source theorem 13.5.17 supplies every normal-branch recognition call in
the component selection. The same selected component therefore carries the
full marked chief sieve and the unitary-row exclusion, with only the genuine
earlier A.3.12 input retained. This is the original nonnormal-case input to
13.5.21; its later component-model reconstruction remains separate.
Source: Aschbacher--Smith13.5.17--21, printed pp.922--924.
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
  (hnot : ¬ ModelConclusion G 5)
include d hA312 hH hU hnot

/-- The source chief sieve with the normal-branch recognition input discharged. -/
theorem source_component_chief_sieve_complete :
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
  exact source_component_chief_sieve_with_unitary_exclusion d hA312 hH hU
    (fun J hJ hu hn => source13_5_17 d hA312 hJ hu hn) hnot

/-- The original selected component is simple and contains the original local
residual; its normality is proved in the same ambient H. -/
theorem source_exists_simple_component_complete :
    let D : ChapterF.Section09.Setup G := ⟨T,L,V,V₃,V₁,H⟩
    let hf : D.Hypothesis := (source13_5_7 d hA312 hH).f9Hypothesis
    ∃ K : Subgroup G, ∃ s : Selected D K,
      let := componentCentralizer_normal s hf
        (selected_star_local_normalization s hf d.hypothesis.qtke hH.1.1)
      SourceConfiguration s hf D.L₁ le_rfl ∧ center (Source.starImage H K) = ⊥ ∧
        IsSimpleGroup (Source.starImage H K) ∧
          residualCentralizer L V₁ ≤ K ∧ (K.subgroupOf H).Normal := by
  exact source_exists_simple_component d hA312 hH hU
    (fun J hJ hu hn => source13_5_17 d hA312 hJ hu hn) hnot

end CFSG.Quasithin.Chapter13.Section05.A5Source
