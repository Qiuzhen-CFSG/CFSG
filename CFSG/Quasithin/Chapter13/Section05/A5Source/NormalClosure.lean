module
public import CFSG.Quasithin.Chapter13.Section05.A5Source.SourceF9
public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.Initial

/-!
# The original locally normal A₅ closure

The source context constructs F.9.1 and proves V₃=[V,L₁]. Hence relative
normality of L₁ inside H implies U_H=[U_H,L₁], places U_H in O₂(L₁),
and identifies L₁∩O₂(H). The same equality descends under the literal
tilde map used in13.5.14; no block or recognition conclusion is assumed.
These are the first deductions of13.5.15 and the commutator premise
for13.5.14(1). The later block construction remains a separate theorem.
Source: Aschbacher–Smith13.5.14–15, printed pp.919–920.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section05.A5Source
open Section06.TerminalContradiction.Ratio Section08
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G} [IsElementaryAbelian 2 V]
  (d : Context T L V V₁ V₂ V₃)
  (hA312 : ∀ (Y : Type u) [Group Y] [Finite Y],
    IsSQTK KnownSimple.IsKnownSimple Y → pCore 2 Y = ⊥ → ∀ (S : Sylow 2 Y) (B : Subgroup Y),
    B ∈ ChapterA.Section03.localCComponents S → Chapter1.Section02.A312Conclusion B)
  (hH : H ∈ Source.Hz (residualCentralizer L V₁) (T : Subgroup G)
    (centralizer (V₁ : Set G)) (normalizer (L : Set G)))
  (hn : ((residualCentralizer L V₁).subgroupOf H).Normal)
include d hA312 hH hn

/-- Original13.5.15's initial reduction on the same H-closure and residual. -/
theorem normal_closure_reduction :
    Source.UH H V₃ = ⁅Source.UH H V₃,residualCentralizer L V₁⁆ ∧
      Source.UH H V₃ ≤ (residualCentralizer L V₁).pCoreIn 2 ∧
      Source.UH H V₃ ≤ L := by
  let D : ChapterF.Section09.Setup G := ⟨T,L,V,V₃,V₁,H⟩
  have hf : D.Hypothesis := (source13_5_7 d hA312 hH).f9Hypothesis
  change D.UH = ⁅D.UH,D.L₁⁆ ∧ D.UH ≤ D.L₁.pCoreIn 2 ∧ D.UH ≤ D.L
  exact NormalBranch.closure_reduction hf d.third_eq_commutator hn

/-- The exact commutator premise for the marked block construction in13.5.14. -/
theorem normal_closure_tilde :
    let D : ChapterF.Section09.Setup G := ⟨T,L,V,V₃,V₁,H⟩
    D.tilde D.UH = ⁅D.tilde D.UH,D.tilde D.L₁⁆ := by
  let D : ChapterF.Section09.Setup G := ⟨T,L,V,V₃,V₁,H⟩
  have hf : D.Hypothesis := (source13_5_7 d hA312 hH).f9Hypothesis
  exact NormalBranch.tilde_closure_commutator hf d.third_eq_commutator hn

/-- The original residual's kernel in H/O₂(H) is its own two-core. -/
theorem normal_residual_core_intersection :
    residualCentralizer L V₁ ⊓ Source.QH H = (residualCentralizer L V₁).pCoreIn 2 := by
  let D : ChapterF.Section09.Setup G := ⟨T,L,V,V₃,V₁,H⟩
  have hf : D.Hypothesis := (source13_5_7 d hA312 hH).f9Hypothesis
  change D.L₁ ⊓ D.QH = D.L₁.pCoreIn 2
  exact NormalBranch.local_core_intersection hf hn

end CFSG.Quasithin.Chapter13.Section05.A5Source
