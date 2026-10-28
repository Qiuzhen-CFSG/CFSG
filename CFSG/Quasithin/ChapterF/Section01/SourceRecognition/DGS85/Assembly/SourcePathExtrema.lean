module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.SourceParameter

/-!
# Packaging the strict source path parameters

The strict branch of DGS (10.10) has `r = 6` and `s = 7`. This module
converts regularity through length six, nonregularity from length seven, and
attaining witnesses to the literal source extrema. The odd stabilizer
conclusion remains separate because the source obtains it from the local
residual and Cartan action.

Source: DGS, *Groups and Graphs* (1985), (10.10), printed p.164.
-/

public noncomputable section
open Subgroup SimpleGraph SimpleGraph.Walk
open Subgroup.CosetGeometry.RankTwo
open Theory.GroupTheory.WeakBNPair.RegularTree
namespace CFSG.Quasithin.ChapterF.Source.DGS85
open NoncommutingProfile

variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

/-- Strict `(10.10)` path extrema from the source-local regularity calculation.
The path convention includes the permitted closed source paths. -/
theorem source_path_parameters_six_seven
    (hreg : ∀ {a b : Vertex (family P)}
      (p : (graph (family P)).Walk a b),
      IsSourcePath p → p.length ≤ 6 → PathRegular p)
    (hbad : ∀ {a b : Vertex (family P)}
      (p : (graph (family P)).Walk a b),
      IsSourcePath p → 7 ≤ p.length → ¬ PathRegular p)
    (hodd : ∀ {a b : Vertex (family P)}
      (p : (graph (family P)).Walk a b),
      IsSourcePath p → 7 ≤ p.length →
        Odd (Nat.card (pathFixer (X := G) p)))
    (hreg6 : ∃ a b : Vertex (family P),
      ∃ p : (graph (family P)).Walk a b,
        p.IsPath ∧ p.length = 6 ∧ PathRegular p)
    (hbad7 : ∃ a b : Vertex (family P),
      ∃ p : (graph (family P)).Walk a b,
        IsSourcePath p ∧ p.length = 7 ∧ ¬ PathRegular p) :
    HasSourcePathParameters (P := P) 6 7 ∧
      ∀ {a b : Vertex (family P)}
        (p : (graph (family P)).Walk a b),
        IsSourcePath p → 7 ≤ p.length →
          Odd (Nat.card (pathFixer (X := G) p)) := by
  refine ⟨?_, hodd⟩
  constructor
  · obtain ⟨a, b, p, hp, hl, hr⟩ := hreg6
    refine ⟨⟨a, b, p, Or.inl hp, hl, hr⟩, ?_⟩
    rintro n ⟨u, v, q, hq, hql, hqr⟩
    by_cases hn : n ≤ 6
    · exact hn
    · exact False.elim (hbad q hq (by omega) hqr)
  · obtain ⟨a, b, p, hp, hl, hn⟩ := hbad7
    refine ⟨⟨a, b, p, hp, hl, hn⟩, ?_⟩
    rintro n ⟨u, v, q, hq, hql, hqr⟩
    by_cases hn : n < 7
    · exact False.elim (hqr (hreg q hq (by omega)))
    · omega

/-- The literal source minimum is seven once the source path extrema are known. -/
theorem sourceS_eq_seven_of_path_parameters_six_seven
    (h : LocallyRankOneTriple P B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i),
      (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (hp : HasSourcePathParameters (P := P) 6 7) :
    sourceS (P := P) = 7 := by
  exact (sourceS_spec h hS).2.unique hp.2

end CFSG.Quasithin.ChapterF.Source.DGS85
