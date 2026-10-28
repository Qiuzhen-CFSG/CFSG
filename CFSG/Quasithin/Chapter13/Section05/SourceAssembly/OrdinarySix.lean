module

public import CFSG.Quasithin.Chapter13.Section05.SourceAssembly.NaturalSixContext
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.OriginalSix.SourceElimination

/-!
# Positive recognition in the prepared ordinary A₆ branch

Negating U₄(3) turns the original natural-action data into the existing
counterexample configuration. The source maximality clause supplies
Hypothesis 12.2.1, and the completed normal and nonnormal arguments make
the literal seed closure under G₁ abelian, a contradiction.

This removes the counterexample exclusion from the recognition statement.
The ordinary quotient marking and the earlier maximality clause remain
explicit: a central quotient A₆ alone also permits the triple-cover case.
Preparation and that remaining case belong to the full 13.5.12 assembly.
Source: Aschbacher–Smith, 13.5.12 and 13.5.16–25, printed pp.918–925.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section05.SourceAssembly
open Section08.SourceCompletion
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ : Subgroup G}
  (d : NaturalSixContext T L V V₁ V₂ V₃ M G₁)
include d

/-- The positive ordinary-A₆ recognition, on the original point normalizer. -/
theorem ordinary_six_isPSU
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (hmax : L ∈ Chapter1.LStar G (T : Subgroup G))
    (hU : ¬ IsMulCommutative (conjugateSpanBy V₃ G₁)) :
    ClassicalGroup.IsPSU G 4 3 := by
  by_contra hnot
  let D : ChapterF.Section09.Setup G := ⟨T,L,V,V₃,V₁,G₁⟩
  have heq : G₁ = D.Gz := d.first_normalizer.trans
    (le_antisymm (normalizer_le_centralizer_of_card_two V₁ d.line_card)
      (Subgroup.centralizer_le_normalizer _))
  have d' : NaturalSetup D.T D.L D.V D.V₁ V₂ D.Vplus M D.Gz :=
    heq ▸ d.toNaturalSetup hnot
  have hf := (Chapter1.Section02.Adequate.mem_faithfulLocalComponents_iff T L).mp
    d.hypothesis.local_component
  have h1221 : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L :=
    ⟨d.hypothesis.qtke,⟨hmax,hf.2⟩,IsQuasisimple.of_mulEquiv e.symm⟩
  have ha := ComponentReduction.OriginalSix.source_point_seed_abelian d' e h1221
  change IsMulCommutative (conjugateSpanBy V₃ D.Gz) at ha
  exact hU (heq.symm ▸ ha)

/-- Clause (2) of 13.5.12 after ordinary-six preparation and maximality. -/
theorem ordinary_six_modelConclusion
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (hmax : L ∈ Chapter1.LStar G (T : Subgroup G))
    (hU : ¬ IsMulCommutative (conjugateSpanBy V₃ G₁)) : ModelConclusion G 6 :=
  Or.inr ⟨rfl,ordinary_six_isPSU d e hmax hU⟩

omit d in
/-- The literal Section 13.7 seed span is abelian under the existing source
counterexample, with only the earlier ordinary maximality clause supplied. -/
theorem ordinary_six_counterexample_seed_abelian
    (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (hmax : L ∈ Chapter1.LStar G (T : Subgroup G)) :
    IsMulCommutative (conjugateSpanBy V₃ G₁) := by
  by_contra hU
  exact d.counterexample.no_unitary_four
    (ordinary_six_isPSU (NaturalSixContext.ofNaturalSetup d) e hmax hU)

end CFSG.Quasithin.Chapter13.Section05.SourceAssembly
