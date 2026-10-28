module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.ReplacementModule
public import Theory.GroupTheory.ConjugateSpanNormalClosure
public import Theory.GroupTheory.PResidual.NormalGenerator

/-!
# Residual movement of the literal replacement span

Under the contrary core-intersection normality in 6.4, the full Borel
normalizes Q_delta and supplements X. Thus Q_delta normally generates X
internally and supplements O²(X), without a Sylow assumption. If O²(X)
fixed V=<Z_delta^X>, then both factors would fix the seed Z_delta, forcing
all of V to be central in X, contrary to amalgam faithfulness.

This proves residual movement in both neighboring-center branches. It
does not assert vanishing fixed space on the whole replacement span;
central summands must be removed on a literal section.

Source: DGS, Groups and Graphs (1985), 6.4, pp.120--121; the corrected
module hypotheses of 5.12, pp.113--115.
-/

public noncomputable section
open Subgroup Theory.GroupTheory.AmalgamGraph
namespace CFSG.Quasithin.ChapterF.Source.DGS85
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}
/-- The opposite core normally generates its closure internally, using the full Borel supplement. -/
theorem source_core_closure_self_generated (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (i : Fin 2)
    (hn : P (other i) ≤ normalizer (↑((P i).pCoreIn 2 ⊓ (P (other i)).pCoreIn 2) : Set G)) :
    let X := conjugateSpanBy ((P i).pCoreIn 2) (P (other i))
    normalClosure (((P i).pCoreIn 2).subgroupOf X : Set X) = ⊤ := by
  let X := conjugateSpanBy ((P i).pCoreIn 2) (P (other i))
  apply map_injective X.subtype_injective
  rw [map_normalClosure_eq_conjugateSpanBy_range,map_subgroupOf_eq_of_le
    (le_conjugateSpanBy _ _),range_subtype,←MonoidHom.range_eq_map,range_subtype]
  have hBP : B ≤ P i := le_sup_right.trans (Classical.choice (h.local_data i)).supplement.le
  have hnA : B ≤ normalizer ((P i).pCoreIn 2 : Set G) :=
    hBP.trans ((P i).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 (P i))))
  have hnX : B ≤ normalizer (X : Set G) :=
    (le_sup_right.trans (Classical.choice (h.local_data (other i))).supplement.le).trans
      (le_normalizer_conjugateSpanBy _ _)
  have he := conjugateSpanBy_sup_of_normalizes_seed ((P i).pCoreIn 2) X B hnA hnX
  rw [core_closure_sup_borel_of_inter_normal h hB i hn] at he
  exact he.symm

/-- The original core supplements the two-residual before any Sylow recognition. -/
theorem source_core_closure_residual_supplement (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (i : Fin 2)
    (hn : P (other i) ≤ normalizer (↑((P i).pCoreIn 2 ⊓ (P (other i)).pCoreIn 2) : Set G)) :
    let X := conjugateSpanBy ((P i).pCoreIn 2) (P (other i))
    (pResidual 2 X).map X.subtype ⊔ (P i).pCoreIn 2 = X := by
  let X := conjugateSpanBy ((P i).pCoreIn 2) (P (other i))
  let := (Classical.choice (h.local_data (other i))).finite_P
  have hXP : X ≤ P (other i) := conjugateSpanBy_le_self
    ((source_core_le_borel (Classical.choice (h.local_data i))).trans
      (le_sup_right.trans (Classical.choice (h.local_data (other i))).supplement.le))
  let : Finite X := Finite.of_injective (inclusion hXP) (inclusion_injective _)
  have he := congrArg (Subgroup.map X.subtype)
    (pResidual_sup_eq_top_of_normalClosure (((P i).pCoreIn 2).subgroupOf X)
      (source_core_closure_self_generated h hB i hn) (p := 2))
  rwa [Subgroup.map_sup,map_subgroupOf_eq_of_le (le_conjugateSpanBy _ _),
    ←MonoidHom.range_eq_map,range_subtype] at he

/-- The actual replacement span has nontrivial two-residual action in both neighboring-center branches. -/
theorem source_replacement_residual_not_central (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (i : Fin 2)
    (hn : P (other i) ≤ normalizer (↑((P i).pCoreIn 2 ⊓ (P (other i)).pCoreIn 2) : Set G)) :
    let X := conjugateSpanBy ((P i).pCoreIn 2) (P (other i))
    let V := conjugateSpanBy (sylowCenterSpan (P i)) X
    ¬ V ≤ centralizer ((pResidual 2 X).map X.subtype : Set G) := by
  let X := conjugateSpanBy ((P i).pCoreIn 2) (P (other i))
  let Z := sylowCenterSpan (P i)
  let V := conjugateSpanBy Z X
  change ¬ V ≤ centralizer ((pResidual 2 X).map X.subtype : Set G)
  intro hc
  have hZQ : Z ≤ centralizer ((P i).pCoreIn 2 : Set G) := by
    intro z hz
    exact ((mem_omegaCenterIn_iff _ _).mp
      (sylowCenterSpan_le_coreOmega _ (source_core_selfCentralizing
        (Classical.choice (h.local_data i))) hz)).2.1
  have hZX : Z ≤ centralizer (X : Set G) := by
    change Z ≤ centralizer (conjugateSpanBy ((P i).pCoreIn 2) (P (other i)) : Set G)
    rw [←source_core_closure_residual_supplement h hB i hn]
    exact le_centralizer_iff.mp (sup_le
      (le_centralizer_iff.mp ((le_conjugateSpanBy Z X).trans hc))
      (le_centralizer_iff.mp hZQ))
  exact source_replacement_span_not_central h hB i hn
    (conjugateSpanBy_le hZX (X.le_normalizer.trans (normalizer_le_normalizer_centralizer X)))
end CFSG.Quasithin.ChapterF.Source.DGS85
