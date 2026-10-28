module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Fusion.PositiveFixedSpace.MonomialExclusion.Standard.ReferenceBound.Coverage.Contracts

/-!
# Exhaustiveness of the marked hexacode column table

An involution consists of fixed points and disjoint transpositions. At
each step we choose the image of the least unassigned index; involutivity
determines its partner and excludes every previously used image. This
gives 76 leaves (26 fixing zero, and ten for each other image of zero).
Each leaf is either definitionally one of the sixteen existing candidates
or fails the literal hexacode decoder tests, as checked by `decide`.

All reductions are bounded by one concrete column map. The generator in
`Columns/source/generate.py` only writes proof syntax; neither its
enumeration nor its choice of candidate indices is trusted.

Source context: Aschbacher, *Sporadic Groups* (1994), Lemma 49.5,
pp.283–284, and the root-four convention on p.269. The definitions of
the code and marked maps are the existing attributed ATLAS model.
-/

open Atlas.Codes
@[expose] public section
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.Fusion.ReferenceBound.Coverage

private def liftColumn (f : Fin 6 → Fin 6) (i : HexIndex) : HexIndex :=
  hexIndexEquiv.symm (f (hexIndexEquiv i))

/-- A previously paired index cannot be the image of a fresh index. -/
private theorem image_ne (f : Fin 6 → Fin 6) (hi : Function.Involutive f)
    {i j k : Fin 6} (hj : f j = k) (hk : k ≠ i) : f i ≠ j := by
  intro hij
  apply hk
  simpa only [hij, hj] using hi i

private theorem image_zero_0 (f : Fin 6 → Fin 6)
    (hi : Function.Involutive f) (hc : ColumnChecks (liftColumn f))
    (h0 : f 0 = 0) : ∃ q : Fin 16, liftColumn f = columnCandidate q := by
  have hn0 := image_ne f hi h0 (by decide : (0 : Fin 6) ≠ 1)
  have choices : f 1 = 1 ∨ f 1 = 2 ∨ f 1 = 3 ∨ f 1 = 4 ∨ f 1 = 5 := by omega
  rcases choices with h1 | h1 | h1 | h1 | h1
  · have hn0 := image_ne f hi h0 (by decide : (0 : Fin 6) ≠ 2)
    have hn1 := image_ne f hi h1 (by decide : (1 : Fin 6) ≠ 2)
    have choices : f 2 = 2 ∨ f 2 = 3 ∨ f 2 = 4 ∨ f 2 = 5 := by omega
    rcases choices with h2 | h2 | h2 | h2
    · have hn0 := image_ne f hi h0 (by decide : (0 : Fin 6) ≠ 3)
      have hn1 := image_ne f hi h1 (by decide : (1 : Fin 6) ≠ 3)
      have hn2 := image_ne f hi h2 (by decide : (2 : Fin 6) ≠ 3)
      have choices : f 3 = 3 ∨ f 3 = 4 ∨ f 3 = 5 := by omega
      rcases choices with h3 | h3 | h3
      · have hn0 := image_ne f hi h0 (by decide : (0 : Fin 6) ≠ 4)
        have hn1 := image_ne f hi h1 (by decide : (1 : Fin 6) ≠ 4)
        have hn2 := image_ne f hi h2 (by decide : (2 : Fin 6) ≠ 4)
        have hn3 := image_ne f hi h3 (by decide : (3 : Fin 6) ≠ 4)
        have choices : f 4 = 4 ∨ f 4 = 5 := by omega
        rcases choices with h4 | h4
        · have hn0 := image_ne f hi h0 (by decide : (0 : Fin 6) ≠ 5)
          have hn1 := image_ne f hi h1 (by decide : (1 : Fin 6) ≠ 5)
          have hn2 := image_ne f hi h2 (by decide : (2 : Fin 6) ≠ 5)
          have hn3 := image_ne f hi h3 (by decide : (3 : Fin 6) ≠ 5)
          have hn4 := image_ne f hi h4 (by decide : (4 : Fin 6) ≠ 5)
          have choices : f 5 = 5 := by omega
          have h5 := choices
          have he : f = ![0,1,2,3,4,5] := by
            funext i
            fin_cases i <;> assumption
          refine ⟨0, ?_⟩
          rw [he]
          decide
        · have h5 : f 5 = 4 := by simpa only [h4] using hi 4
          have he : f = ![0,1,2,3,5,4] := by
            funext i
            fin_cases i <;> assumption
          rw [he] at hc
          exfalso
          exact (by decide : ¬ ColumnChecks (liftColumn ![0,1,2,3,5,4])) hc
      · have h4 : f 4 = 3 := by simpa only [h3] using hi 3
        have hn0 := image_ne f hi h0 (by decide : (0 : Fin 6) ≠ 5)
        have hn1 := image_ne f hi h1 (by decide : (1 : Fin 6) ≠ 5)
        have hn2 := image_ne f hi h2 (by decide : (2 : Fin 6) ≠ 5)
        have hn3 := image_ne f hi h3 (by decide : (4 : Fin 6) ≠ 5)
        have hn4 := image_ne f hi h4 (by decide : (3 : Fin 6) ≠ 5)
        have choices : f 5 = 5 := by omega
        have h5 := choices
        have he : f = ![0,1,2,4,3,5] := by
          funext i
          fin_cases i <;> assumption
        rw [he] at hc
        exfalso
        exact (by decide : ¬ ColumnChecks (liftColumn ![0,1,2,4,3,5])) hc
      · have h5 : f 5 = 3 := by simpa only [h3] using hi 3
        have hn0 := image_ne f hi h0 (by decide : (0 : Fin 6) ≠ 4)
        have hn1 := image_ne f hi h1 (by decide : (1 : Fin 6) ≠ 4)
        have hn2 := image_ne f hi h2 (by decide : (2 : Fin 6) ≠ 4)
        have hn3 := image_ne f hi h3 (by decide : (5 : Fin 6) ≠ 4)
        have hn5 := image_ne f hi h5 (by decide : (3 : Fin 6) ≠ 4)
        have choices : f 4 = 4 := by omega
        have h4 := choices
        have he : f = ![0,1,2,5,4,3] := by
          funext i
          fin_cases i <;> assumption
        rw [he] at hc
        exfalso
        exact (by decide : ¬ ColumnChecks (liftColumn ![0,1,2,5,4,3])) hc
    · have h3 : f 3 = 2 := by simpa only [h2] using hi 2
      have hn0 := image_ne f hi h0 (by decide : (0 : Fin 6) ≠ 4)
      have hn1 := image_ne f hi h1 (by decide : (1 : Fin 6) ≠ 4)
      have hn2 := image_ne f hi h2 (by decide : (3 : Fin 6) ≠ 4)
      have hn3 := image_ne f hi h3 (by decide : (2 : Fin 6) ≠ 4)
      have choices : f 4 = 4 ∨ f 4 = 5 := by omega
      rcases choices with h4 | h4
      · have hn0 := image_ne f hi h0 (by decide : (0 : Fin 6) ≠ 5)
        have hn1 := image_ne f hi h1 (by decide : (1 : Fin 6) ≠ 5)
        have hn2 := image_ne f hi h2 (by decide : (3 : Fin 6) ≠ 5)
        have hn3 := image_ne f hi h3 (by decide : (2 : Fin 6) ≠ 5)
        have hn4 := image_ne f hi h4 (by decide : (4 : Fin 6) ≠ 5)
        have choices : f 5 = 5 := by omega
        have h5 := choices
        have he : f = ![0,1,3,2,4,5] := by
          funext i
          fin_cases i <;> assumption
        rw [he] at hc
        exfalso
        exact (by decide : ¬ ColumnChecks (liftColumn ![0,1,3,2,4,5])) hc
      · have h5 : f 5 = 4 := by simpa only [h4] using hi 4
        have he : f = ![0,1,3,2,5,4] := by
          funext i
          fin_cases i <;> assumption
        rw [he] at hc
        exfalso
        exact (by decide : ¬ ColumnChecks (liftColumn ![0,1,3,2,5,4])) hc
    · have h4 : f 4 = 2 := by simpa only [h2] using hi 2
      have hn0 := image_ne f hi h0 (by decide : (0 : Fin 6) ≠ 3)
      have hn1 := image_ne f hi h1 (by decide : (1 : Fin 6) ≠ 3)
      have hn2 := image_ne f hi h2 (by decide : (4 : Fin 6) ≠ 3)
      have hn4 := image_ne f hi h4 (by decide : (2 : Fin 6) ≠ 3)
      have choices : f 3 = 3 ∨ f 3 = 5 := by omega
      rcases choices with h3 | h3
      · have hn0 := image_ne f hi h0 (by decide : (0 : Fin 6) ≠ 5)
        have hn1 := image_ne f hi h1 (by decide : (1 : Fin 6) ≠ 5)
        have hn2 := image_ne f hi h2 (by decide : (4 : Fin 6) ≠ 5)
        have hn3 := image_ne f hi h3 (by decide : (3 : Fin 6) ≠ 5)
        have hn4 := image_ne f hi h4 (by decide : (2 : Fin 6) ≠ 5)
        have choices : f 5 = 5 := by omega
        have h5 := choices
        have he : f = ![0,1,4,3,2,5] := by
          funext i
          fin_cases i <;> assumption
        rw [he] at hc
        exfalso
        exact (by decide : ¬ ColumnChecks (liftColumn ![0,1,4,3,2,5])) hc
      · have h5 : f 5 = 3 := by simpa only [h3] using hi 3
        have he : f = ![0,1,4,5,2,3] := by
          funext i
          fin_cases i <;> assumption
        refine ⟨1, ?_⟩
        rw [he]
        decide
    · have h5 : f 5 = 2 := by simpa only [h2] using hi 2
      have hn0 := image_ne f hi h0 (by decide : (0 : Fin 6) ≠ 3)
      have hn1 := image_ne f hi h1 (by decide : (1 : Fin 6) ≠ 3)
      have hn2 := image_ne f hi h2 (by decide : (5 : Fin 6) ≠ 3)
      have hn5 := image_ne f hi h5 (by decide : (2 : Fin 6) ≠ 3)
      have choices : f 3 = 3 ∨ f 3 = 4 := by omega
      rcases choices with h3 | h3
      · have hn0 := image_ne f hi h0 (by decide : (0 : Fin 6) ≠ 4)
        have hn1 := image_ne f hi h1 (by decide : (1 : Fin 6) ≠ 4)
        have hn2 := image_ne f hi h2 (by decide : (5 : Fin 6) ≠ 4)
        have hn3 := image_ne f hi h3 (by decide : (3 : Fin 6) ≠ 4)
        have hn5 := image_ne f hi h5 (by decide : (2 : Fin 6) ≠ 4)
        have choices : f 4 = 4 := by omega
        have h4 := choices
        have he : f = ![0,1,5,3,4,2] := by
          funext i
          fin_cases i <;> assumption
        rw [he] at hc
        exfalso
        exact (by decide : ¬ ColumnChecks (liftColumn ![0,1,5,3,4,2])) hc
      · have h4 : f 4 = 3 := by simpa only [h3] using hi 3
        have he : f = ![0,1,5,4,3,2] := by
          funext i
          fin_cases i <;> assumption
        rw [he] at hc
        exfalso
        exact (by decide : ¬ ColumnChecks (liftColumn ![0,1,5,4,3,2])) hc
  · have h2 : f 2 = 1 := by simpa only [h1] using hi 1
    have hn0 := image_ne f hi h0 (by decide : (0 : Fin 6) ≠ 3)
    have hn1 := image_ne f hi h1 (by decide : (2 : Fin 6) ≠ 3)
    have hn2 := image_ne f hi h2 (by decide : (1 : Fin 6) ≠ 3)
    have choices : f 3 = 3 ∨ f 3 = 4 ∨ f 3 = 5 := by omega
    rcases choices with h3 | h3 | h3
    · have hn0 := image_ne f hi h0 (by decide : (0 : Fin 6) ≠ 4)
      have hn1 := image_ne f hi h1 (by decide : (2 : Fin 6) ≠ 4)
      have hn2 := image_ne f hi h2 (by decide : (1 : Fin 6) ≠ 4)
      have hn3 := image_ne f hi h3 (by decide : (3 : Fin 6) ≠ 4)
      have choices : f 4 = 4 ∨ f 4 = 5 := by omega
      rcases choices with h4 | h4
      · have hn0 := image_ne f hi h0 (by decide : (0 : Fin 6) ≠ 5)
        have hn1 := image_ne f hi h1 (by decide : (2 : Fin 6) ≠ 5)
        have hn2 := image_ne f hi h2 (by decide : (1 : Fin 6) ≠ 5)
        have hn3 := image_ne f hi h3 (by decide : (3 : Fin 6) ≠ 5)
        have hn4 := image_ne f hi h4 (by decide : (4 : Fin 6) ≠ 5)
        have choices : f 5 = 5 := by omega
        have h5 := choices
        have he : f = ![0,2,1,3,4,5] := by
          funext i
          fin_cases i <;> assumption
        rw [he] at hc
        exfalso
        exact (by decide : ¬ ColumnChecks (liftColumn ![0,2,1,3,4,5])) hc
      · have h5 : f 5 = 4 := by simpa only [h4] using hi 4
        have he : f = ![0,2,1,3,5,4] := by
          funext i
          fin_cases i <;> assumption
        rw [he] at hc
        exfalso
        exact (by decide : ¬ ColumnChecks (liftColumn ![0,2,1,3,5,4])) hc
    · have h4 : f 4 = 3 := by simpa only [h3] using hi 3
      have hn0 := image_ne f hi h0 (by decide : (0 : Fin 6) ≠ 5)
      have hn1 := image_ne f hi h1 (by decide : (2 : Fin 6) ≠ 5)
      have hn2 := image_ne f hi h2 (by decide : (1 : Fin 6) ≠ 5)
      have hn3 := image_ne f hi h3 (by decide : (4 : Fin 6) ≠ 5)
      have hn4 := image_ne f hi h4 (by decide : (3 : Fin 6) ≠ 5)
      have choices : f 5 = 5 := by omega
      have h5 := choices
      have he : f = ![0,2,1,4,3,5] := by
        funext i
        fin_cases i <;> assumption
      refine ⟨2, ?_⟩
      rw [he]
      decide
    · have h5 : f 5 = 3 := by simpa only [h3] using hi 3
      have hn0 := image_ne f hi h0 (by decide : (0 : Fin 6) ≠ 4)
      have hn1 := image_ne f hi h1 (by decide : (2 : Fin 6) ≠ 4)
      have hn2 := image_ne f hi h2 (by decide : (1 : Fin 6) ≠ 4)
      have hn3 := image_ne f hi h3 (by decide : (5 : Fin 6) ≠ 4)
      have hn5 := image_ne f hi h5 (by decide : (3 : Fin 6) ≠ 4)
      have choices : f 4 = 4 := by omega
      have h4 := choices
      have he : f = ![0,2,1,5,4,3] := by
        funext i
        fin_cases i <;> assumption
      rw [he] at hc
      exfalso
      exact (by decide : ¬ ColumnChecks (liftColumn ![0,2,1,5,4,3])) hc
  · have h3 : f 3 = 1 := by simpa only [h1] using hi 1
    have hn0 := image_ne f hi h0 (by decide : (0 : Fin 6) ≠ 2)
    have hn1 := image_ne f hi h1 (by decide : (3 : Fin 6) ≠ 2)
    have hn3 := image_ne f hi h3 (by decide : (1 : Fin 6) ≠ 2)
    have choices : f 2 = 2 ∨ f 2 = 4 ∨ f 2 = 5 := by omega
    rcases choices with h2 | h2 | h2
    · have hn0 := image_ne f hi h0 (by decide : (0 : Fin 6) ≠ 4)
      have hn1 := image_ne f hi h1 (by decide : (3 : Fin 6) ≠ 4)
      have hn2 := image_ne f hi h2 (by decide : (2 : Fin 6) ≠ 4)
      have hn3 := image_ne f hi h3 (by decide : (1 : Fin 6) ≠ 4)
      have choices : f 4 = 4 ∨ f 4 = 5 := by omega
      rcases choices with h4 | h4
      · have hn0 := image_ne f hi h0 (by decide : (0 : Fin 6) ≠ 5)
        have hn1 := image_ne f hi h1 (by decide : (3 : Fin 6) ≠ 5)
        have hn2 := image_ne f hi h2 (by decide : (2 : Fin 6) ≠ 5)
        have hn3 := image_ne f hi h3 (by decide : (1 : Fin 6) ≠ 5)
        have hn4 := image_ne f hi h4 (by decide : (4 : Fin 6) ≠ 5)
        have choices : f 5 = 5 := by omega
        have h5 := choices
        have he : f = ![0,3,2,1,4,5] := by
          funext i
          fin_cases i <;> assumption
        rw [he] at hc
        exfalso
        exact (by decide : ¬ ColumnChecks (liftColumn ![0,3,2,1,4,5])) hc
      · have h5 : f 5 = 4 := by simpa only [h4] using hi 4
        have he : f = ![0,3,2,1,5,4] := by
          funext i
          fin_cases i <;> assumption
        refine ⟨3, ?_⟩
        rw [he]
        decide
    · have h4 : f 4 = 2 := by simpa only [h2] using hi 2
      have hn0 := image_ne f hi h0 (by decide : (0 : Fin 6) ≠ 5)
      have hn1 := image_ne f hi h1 (by decide : (3 : Fin 6) ≠ 5)
      have hn2 := image_ne f hi h2 (by decide : (4 : Fin 6) ≠ 5)
      have hn3 := image_ne f hi h3 (by decide : (1 : Fin 6) ≠ 5)
      have hn4 := image_ne f hi h4 (by decide : (2 : Fin 6) ≠ 5)
      have choices : f 5 = 5 := by omega
      have h5 := choices
      have he : f = ![0,3,4,1,2,5] := by
        funext i
        fin_cases i <;> assumption
      rw [he] at hc
      exfalso
      exact (by decide : ¬ ColumnChecks (liftColumn ![0,3,4,1,2,5])) hc
    · have h5 : f 5 = 2 := by simpa only [h2] using hi 2
      have hn0 := image_ne f hi h0 (by decide : (0 : Fin 6) ≠ 4)
      have hn1 := image_ne f hi h1 (by decide : (3 : Fin 6) ≠ 4)
      have hn2 := image_ne f hi h2 (by decide : (5 : Fin 6) ≠ 4)
      have hn3 := image_ne f hi h3 (by decide : (1 : Fin 6) ≠ 4)
      have hn5 := image_ne f hi h5 (by decide : (2 : Fin 6) ≠ 4)
      have choices : f 4 = 4 := by omega
      have h4 := choices
      have he : f = ![0,3,5,1,4,2] := by
        funext i
        fin_cases i <;> assumption
      rw [he] at hc
      exfalso
      exact (by decide : ¬ ColumnChecks (liftColumn ![0,3,5,1,4,2])) hc
  · have h4 : f 4 = 1 := by simpa only [h1] using hi 1
    have hn0 := image_ne f hi h0 (by decide : (0 : Fin 6) ≠ 2)
    have hn1 := image_ne f hi h1 (by decide : (4 : Fin 6) ≠ 2)
    have hn4 := image_ne f hi h4 (by decide : (1 : Fin 6) ≠ 2)
    have choices : f 2 = 2 ∨ f 2 = 3 ∨ f 2 = 5 := by omega
    rcases choices with h2 | h2 | h2
    · have hn0 := image_ne f hi h0 (by decide : (0 : Fin 6) ≠ 3)
      have hn1 := image_ne f hi h1 (by decide : (4 : Fin 6) ≠ 3)
      have hn2 := image_ne f hi h2 (by decide : (2 : Fin 6) ≠ 3)
      have hn4 := image_ne f hi h4 (by decide : (1 : Fin 6) ≠ 3)
      have choices : f 3 = 3 ∨ f 3 = 5 := by omega
      rcases choices with h3 | h3
      · have hn0 := image_ne f hi h0 (by decide : (0 : Fin 6) ≠ 5)
        have hn1 := image_ne f hi h1 (by decide : (4 : Fin 6) ≠ 5)
        have hn2 := image_ne f hi h2 (by decide : (2 : Fin 6) ≠ 5)
        have hn3 := image_ne f hi h3 (by decide : (3 : Fin 6) ≠ 5)
        have hn4 := image_ne f hi h4 (by decide : (1 : Fin 6) ≠ 5)
        have choices : f 5 = 5 := by omega
        have h5 := choices
        have he : f = ![0,4,2,3,1,5] := by
          funext i
          fin_cases i <;> assumption
        rw [he] at hc
        exfalso
        exact (by decide : ¬ ColumnChecks (liftColumn ![0,4,2,3,1,5])) hc
      · have h5 : f 5 = 3 := by simpa only [h3] using hi 3
        have he : f = ![0,4,2,5,1,3] := by
          funext i
          fin_cases i <;> assumption
        rw [he] at hc
        exfalso
        exact (by decide : ¬ ColumnChecks (liftColumn ![0,4,2,5,1,3])) hc
    · have h3 : f 3 = 2 := by simpa only [h2] using hi 2
      have hn0 := image_ne f hi h0 (by decide : (0 : Fin 6) ≠ 5)
      have hn1 := image_ne f hi h1 (by decide : (4 : Fin 6) ≠ 5)
      have hn2 := image_ne f hi h2 (by decide : (3 : Fin 6) ≠ 5)
      have hn3 := image_ne f hi h3 (by decide : (2 : Fin 6) ≠ 5)
      have hn4 := image_ne f hi h4 (by decide : (1 : Fin 6) ≠ 5)
      have choices : f 5 = 5 := by omega
      have h5 := choices
      have he : f = ![0,4,3,2,1,5] := by
        funext i
        fin_cases i <;> assumption
      rw [he] at hc
      exfalso
      exact (by decide : ¬ ColumnChecks (liftColumn ![0,4,3,2,1,5])) hc
    · have h5 : f 5 = 2 := by simpa only [h2] using hi 2
      have hn0 := image_ne f hi h0 (by decide : (0 : Fin 6) ≠ 3)
      have hn1 := image_ne f hi h1 (by decide : (4 : Fin 6) ≠ 3)
      have hn2 := image_ne f hi h2 (by decide : (5 : Fin 6) ≠ 3)
      have hn4 := image_ne f hi h4 (by decide : (1 : Fin 6) ≠ 3)
      have hn5 := image_ne f hi h5 (by decide : (2 : Fin 6) ≠ 3)
      have choices : f 3 = 3 := by omega
      have h3 := choices
      have he : f = ![0,4,5,3,1,2] := by
        funext i
        fin_cases i <;> assumption
      refine ⟨4, ?_⟩
      rw [he]
      decide
  · have h5 : f 5 = 1 := by simpa only [h1] using hi 1
    have hn0 := image_ne f hi h0 (by decide : (0 : Fin 6) ≠ 2)
    have hn1 := image_ne f hi h1 (by decide : (5 : Fin 6) ≠ 2)
    have hn5 := image_ne f hi h5 (by decide : (1 : Fin 6) ≠ 2)
    have choices : f 2 = 2 ∨ f 2 = 3 ∨ f 2 = 4 := by omega
    rcases choices with h2 | h2 | h2
    · have hn0 := image_ne f hi h0 (by decide : (0 : Fin 6) ≠ 3)
      have hn1 := image_ne f hi h1 (by decide : (5 : Fin 6) ≠ 3)
      have hn2 := image_ne f hi h2 (by decide : (2 : Fin 6) ≠ 3)
      have hn5 := image_ne f hi h5 (by decide : (1 : Fin 6) ≠ 3)
      have choices : f 3 = 3 ∨ f 3 = 4 := by omega
      rcases choices with h3 | h3
      · have hn0 := image_ne f hi h0 (by decide : (0 : Fin 6) ≠ 4)
        have hn1 := image_ne f hi h1 (by decide : (5 : Fin 6) ≠ 4)
        have hn2 := image_ne f hi h2 (by decide : (2 : Fin 6) ≠ 4)
        have hn3 := image_ne f hi h3 (by decide : (3 : Fin 6) ≠ 4)
        have hn5 := image_ne f hi h5 (by decide : (1 : Fin 6) ≠ 4)
        have choices : f 4 = 4 := by omega
        have h4 := choices
        have he : f = ![0,5,2,3,4,1] := by
          funext i
          fin_cases i <;> assumption
        rw [he] at hc
        exfalso
        exact (by decide : ¬ ColumnChecks (liftColumn ![0,5,2,3,4,1])) hc
      · have h4 : f 4 = 3 := by simpa only [h3] using hi 3
        have he : f = ![0,5,2,4,3,1] := by
          funext i
          fin_cases i <;> assumption
        rw [he] at hc
        exfalso
        exact (by decide : ¬ ColumnChecks (liftColumn ![0,5,2,4,3,1])) hc
    · have h3 : f 3 = 2 := by simpa only [h2] using hi 2
      have hn0 := image_ne f hi h0 (by decide : (0 : Fin 6) ≠ 4)
      have hn1 := image_ne f hi h1 (by decide : (5 : Fin 6) ≠ 4)
      have hn2 := image_ne f hi h2 (by decide : (3 : Fin 6) ≠ 4)
      have hn3 := image_ne f hi h3 (by decide : (2 : Fin 6) ≠ 4)
      have hn5 := image_ne f hi h5 (by decide : (1 : Fin 6) ≠ 4)
      have choices : f 4 = 4 := by omega
      have h4 := choices
      have he : f = ![0,5,3,2,4,1] := by
        funext i
        fin_cases i <;> assumption
      refine ⟨5, ?_⟩
      rw [he]
      decide
    · have h4 : f 4 = 2 := by simpa only [h2] using hi 2
      have hn0 := image_ne f hi h0 (by decide : (0 : Fin 6) ≠ 3)
      have hn1 := image_ne f hi h1 (by decide : (5 : Fin 6) ≠ 3)
      have hn2 := image_ne f hi h2 (by decide : (4 : Fin 6) ≠ 3)
      have hn4 := image_ne f hi h4 (by decide : (2 : Fin 6) ≠ 3)
      have hn5 := image_ne f hi h5 (by decide : (1 : Fin 6) ≠ 3)
      have choices : f 3 = 3 := by omega
      have h3 := choices
      have he : f = ![0,5,4,3,2,1] := by
        funext i
        fin_cases i <;> assumption
      rw [he] at hc
      exfalso
      exact (by decide : ¬ ColumnChecks (liftColumn ![0,5,4,3,2,1])) hc

private theorem image_zero_1 (f : Fin 6 → Fin 6)
    (hi : Function.Involutive f) (hc : ColumnChecks (liftColumn f))
    (h0 : f 0 = 1) : ∃ q : Fin 16, liftColumn f = columnCandidate q := by
  have h1 : f 1 = 0 := by simpa only [h0] using hi 0
  have hn0 := image_ne f hi h0 (by decide : (1 : Fin 6) ≠ 2)
  have hn1 := image_ne f hi h1 (by decide : (0 : Fin 6) ≠ 2)
  have choices : f 2 = 2 ∨ f 2 = 3 ∨ f 2 = 4 ∨ f 2 = 5 := by omega
  rcases choices with h2 | h2 | h2 | h2
  · have hn0 := image_ne f hi h0 (by decide : (1 : Fin 6) ≠ 3)
    have hn1 := image_ne f hi h1 (by decide : (0 : Fin 6) ≠ 3)
    have hn2 := image_ne f hi h2 (by decide : (2 : Fin 6) ≠ 3)
    have choices : f 3 = 3 ∨ f 3 = 4 ∨ f 3 = 5 := by omega
    rcases choices with h3 | h3 | h3
    · have hn0 := image_ne f hi h0 (by decide : (1 : Fin 6) ≠ 4)
      have hn1 := image_ne f hi h1 (by decide : (0 : Fin 6) ≠ 4)
      have hn2 := image_ne f hi h2 (by decide : (2 : Fin 6) ≠ 4)
      have hn3 := image_ne f hi h3 (by decide : (3 : Fin 6) ≠ 4)
      have choices : f 4 = 4 ∨ f 4 = 5 := by omega
      rcases choices with h4 | h4
      · have hn0 := image_ne f hi h0 (by decide : (1 : Fin 6) ≠ 5)
        have hn1 := image_ne f hi h1 (by decide : (0 : Fin 6) ≠ 5)
        have hn2 := image_ne f hi h2 (by decide : (2 : Fin 6) ≠ 5)
        have hn3 := image_ne f hi h3 (by decide : (3 : Fin 6) ≠ 5)
        have hn4 := image_ne f hi h4 (by decide : (4 : Fin 6) ≠ 5)
        have choices : f 5 = 5 := by omega
        have h5 := choices
        have he : f = ![1,0,2,3,4,5] := by
          funext i
          fin_cases i <;> assumption
        rw [he] at hc
        exfalso
        exact (by decide : ¬ ColumnChecks (liftColumn ![1,0,2,3,4,5])) hc
      · have h5 : f 5 = 4 := by simpa only [h4] using hi 4
        have he : f = ![1,0,2,3,5,4] := by
          funext i
          fin_cases i <;> assumption
        rw [he] at hc
        exfalso
        exact (by decide : ¬ ColumnChecks (liftColumn ![1,0,2,3,5,4])) hc
    · have h4 : f 4 = 3 := by simpa only [h3] using hi 3
      have hn0 := image_ne f hi h0 (by decide : (1 : Fin 6) ≠ 5)
      have hn1 := image_ne f hi h1 (by decide : (0 : Fin 6) ≠ 5)
      have hn2 := image_ne f hi h2 (by decide : (2 : Fin 6) ≠ 5)
      have hn3 := image_ne f hi h3 (by decide : (4 : Fin 6) ≠ 5)
      have hn4 := image_ne f hi h4 (by decide : (3 : Fin 6) ≠ 5)
      have choices : f 5 = 5 := by omega
      have h5 := choices
      have he : f = ![1,0,2,4,3,5] := by
        funext i
        fin_cases i <;> assumption
      rw [he] at hc
      exfalso
      exact (by decide : ¬ ColumnChecks (liftColumn ![1,0,2,4,3,5])) hc
    · have h5 : f 5 = 3 := by simpa only [h3] using hi 3
      have hn0 := image_ne f hi h0 (by decide : (1 : Fin 6) ≠ 4)
      have hn1 := image_ne f hi h1 (by decide : (0 : Fin 6) ≠ 4)
      have hn2 := image_ne f hi h2 (by decide : (2 : Fin 6) ≠ 4)
      have hn3 := image_ne f hi h3 (by decide : (5 : Fin 6) ≠ 4)
      have hn5 := image_ne f hi h5 (by decide : (3 : Fin 6) ≠ 4)
      have choices : f 4 = 4 := by omega
      have h4 := choices
      have he : f = ![1,0,2,5,4,3] := by
        funext i
        fin_cases i <;> assumption
      refine ⟨6, ?_⟩
      rw [he]
      decide
  · have h3 : f 3 = 2 := by simpa only [h2] using hi 2
    have hn0 := image_ne f hi h0 (by decide : (1 : Fin 6) ≠ 4)
    have hn1 := image_ne f hi h1 (by decide : (0 : Fin 6) ≠ 4)
    have hn2 := image_ne f hi h2 (by decide : (3 : Fin 6) ≠ 4)
    have hn3 := image_ne f hi h3 (by decide : (2 : Fin 6) ≠ 4)
    have choices : f 4 = 4 ∨ f 4 = 5 := by omega
    rcases choices with h4 | h4
    · have hn0 := image_ne f hi h0 (by decide : (1 : Fin 6) ≠ 5)
      have hn1 := image_ne f hi h1 (by decide : (0 : Fin 6) ≠ 5)
      have hn2 := image_ne f hi h2 (by decide : (3 : Fin 6) ≠ 5)
      have hn3 := image_ne f hi h3 (by decide : (2 : Fin 6) ≠ 5)
      have hn4 := image_ne f hi h4 (by decide : (4 : Fin 6) ≠ 5)
      have choices : f 5 = 5 := by omega
      have h5 := choices
      have he : f = ![1,0,3,2,4,5] := by
        funext i
        fin_cases i <;> assumption
      rw [he] at hc
      exfalso
      exact (by decide : ¬ ColumnChecks (liftColumn ![1,0,3,2,4,5])) hc
    · have h5 : f 5 = 4 := by simpa only [h4] using hi 4
      have he : f = ![1,0,3,2,5,4] := by
        funext i
        fin_cases i <;> assumption
      rw [he] at hc
      exfalso
      exact (by decide : ¬ ColumnChecks (liftColumn ![1,0,3,2,5,4])) hc
  · have h4 : f 4 = 2 := by simpa only [h2] using hi 2
    have hn0 := image_ne f hi h0 (by decide : (1 : Fin 6) ≠ 3)
    have hn1 := image_ne f hi h1 (by decide : (0 : Fin 6) ≠ 3)
    have hn2 := image_ne f hi h2 (by decide : (4 : Fin 6) ≠ 3)
    have hn4 := image_ne f hi h4 (by decide : (2 : Fin 6) ≠ 3)
    have choices : f 3 = 3 ∨ f 3 = 5 := by omega
    rcases choices with h3 | h3
    · have hn0 := image_ne f hi h0 (by decide : (1 : Fin 6) ≠ 5)
      have hn1 := image_ne f hi h1 (by decide : (0 : Fin 6) ≠ 5)
      have hn2 := image_ne f hi h2 (by decide : (4 : Fin 6) ≠ 5)
      have hn3 := image_ne f hi h3 (by decide : (3 : Fin 6) ≠ 5)
      have hn4 := image_ne f hi h4 (by decide : (2 : Fin 6) ≠ 5)
      have choices : f 5 = 5 := by omega
      have h5 := choices
      have he : f = ![1,0,4,3,2,5] := by
        funext i
        fin_cases i <;> assumption
      refine ⟨7, ?_⟩
      rw [he]
      decide
    · have h5 : f 5 = 3 := by simpa only [h3] using hi 3
      have he : f = ![1,0,4,5,2,3] := by
        funext i
        fin_cases i <;> assumption
      rw [he] at hc
      exfalso
      exact (by decide : ¬ ColumnChecks (liftColumn ![1,0,4,5,2,3])) hc
  · have h5 : f 5 = 2 := by simpa only [h2] using hi 2
    have hn0 := image_ne f hi h0 (by decide : (1 : Fin 6) ≠ 3)
    have hn1 := image_ne f hi h1 (by decide : (0 : Fin 6) ≠ 3)
    have hn2 := image_ne f hi h2 (by decide : (5 : Fin 6) ≠ 3)
    have hn5 := image_ne f hi h5 (by decide : (2 : Fin 6) ≠ 3)
    have choices : f 3 = 3 ∨ f 3 = 4 := by omega
    rcases choices with h3 | h3
    · have hn0 := image_ne f hi h0 (by decide : (1 : Fin 6) ≠ 4)
      have hn1 := image_ne f hi h1 (by decide : (0 : Fin 6) ≠ 4)
      have hn2 := image_ne f hi h2 (by decide : (5 : Fin 6) ≠ 4)
      have hn3 := image_ne f hi h3 (by decide : (3 : Fin 6) ≠ 4)
      have hn5 := image_ne f hi h5 (by decide : (2 : Fin 6) ≠ 4)
      have choices : f 4 = 4 := by omega
      have h4 := choices
      have he : f = ![1,0,5,3,4,2] := by
        funext i
        fin_cases i <;> assumption
      rw [he] at hc
      exfalso
      exact (by decide : ¬ ColumnChecks (liftColumn ![1,0,5,3,4,2])) hc
    · have h4 : f 4 = 3 := by simpa only [h3] using hi 3
      have he : f = ![1,0,5,4,3,2] := by
        funext i
        fin_cases i <;> assumption
      rw [he] at hc
      exfalso
      exact (by decide : ¬ ColumnChecks (liftColumn ![1,0,5,4,3,2])) hc

private theorem image_zero_2 (f : Fin 6 → Fin 6)
    (hi : Function.Involutive f) (hc : ColumnChecks (liftColumn f))
    (h0 : f 0 = 2) : ∃ q : Fin 16, liftColumn f = columnCandidate q := by
  have h2 : f 2 = 0 := by simpa only [h0] using hi 0
  have hn0 := image_ne f hi h0 (by decide : (2 : Fin 6) ≠ 1)
  have hn2 := image_ne f hi h2 (by decide : (0 : Fin 6) ≠ 1)
  have choices : f 1 = 1 ∨ f 1 = 3 ∨ f 1 = 4 ∨ f 1 = 5 := by omega
  rcases choices with h1 | h1 | h1 | h1
  · have hn0 := image_ne f hi h0 (by decide : (2 : Fin 6) ≠ 3)
    have hn1 := image_ne f hi h1 (by decide : (1 : Fin 6) ≠ 3)
    have hn2 := image_ne f hi h2 (by decide : (0 : Fin 6) ≠ 3)
    have choices : f 3 = 3 ∨ f 3 = 4 ∨ f 3 = 5 := by omega
    rcases choices with h3 | h3 | h3
    · have hn0 := image_ne f hi h0 (by decide : (2 : Fin 6) ≠ 4)
      have hn1 := image_ne f hi h1 (by decide : (1 : Fin 6) ≠ 4)
      have hn2 := image_ne f hi h2 (by decide : (0 : Fin 6) ≠ 4)
      have hn3 := image_ne f hi h3 (by decide : (3 : Fin 6) ≠ 4)
      have choices : f 4 = 4 ∨ f 4 = 5 := by omega
      rcases choices with h4 | h4
      · have hn0 := image_ne f hi h0 (by decide : (2 : Fin 6) ≠ 5)
        have hn1 := image_ne f hi h1 (by decide : (1 : Fin 6) ≠ 5)
        have hn2 := image_ne f hi h2 (by decide : (0 : Fin 6) ≠ 5)
        have hn3 := image_ne f hi h3 (by decide : (3 : Fin 6) ≠ 5)
        have hn4 := image_ne f hi h4 (by decide : (4 : Fin 6) ≠ 5)
        have choices : f 5 = 5 := by omega
        have h5 := choices
        have he : f = ![2,1,0,3,4,5] := by
          funext i
          fin_cases i <;> assumption
        rw [he] at hc
        exfalso
        exact (by decide : ¬ ColumnChecks (liftColumn ![2,1,0,3,4,5])) hc
      · have h5 : f 5 = 4 := by simpa only [h4] using hi 4
        have he : f = ![2,1,0,3,5,4] := by
          funext i
          fin_cases i <;> assumption
        refine ⟨8, ?_⟩
        rw [he]
        decide
    · have h4 : f 4 = 3 := by simpa only [h3] using hi 3
      have hn0 := image_ne f hi h0 (by decide : (2 : Fin 6) ≠ 5)
      have hn1 := image_ne f hi h1 (by decide : (1 : Fin 6) ≠ 5)
      have hn2 := image_ne f hi h2 (by decide : (0 : Fin 6) ≠ 5)
      have hn3 := image_ne f hi h3 (by decide : (4 : Fin 6) ≠ 5)
      have hn4 := image_ne f hi h4 (by decide : (3 : Fin 6) ≠ 5)
      have choices : f 5 = 5 := by omega
      have h5 := choices
      have he : f = ![2,1,0,4,3,5] := by
        funext i
        fin_cases i <;> assumption
      rw [he] at hc
      exfalso
      exact (by decide : ¬ ColumnChecks (liftColumn ![2,1,0,4,3,5])) hc
    · have h5 : f 5 = 3 := by simpa only [h3] using hi 3
      have hn0 := image_ne f hi h0 (by decide : (2 : Fin 6) ≠ 4)
      have hn1 := image_ne f hi h1 (by decide : (1 : Fin 6) ≠ 4)
      have hn2 := image_ne f hi h2 (by decide : (0 : Fin 6) ≠ 4)
      have hn3 := image_ne f hi h3 (by decide : (5 : Fin 6) ≠ 4)
      have hn5 := image_ne f hi h5 (by decide : (3 : Fin 6) ≠ 4)
      have choices : f 4 = 4 := by omega
      have h4 := choices
      have he : f = ![2,1,0,5,4,3] := by
        funext i
        fin_cases i <;> assumption
      rw [he] at hc
      exfalso
      exact (by decide : ¬ ColumnChecks (liftColumn ![2,1,0,5,4,3])) hc
  · have h3 : f 3 = 1 := by simpa only [h1] using hi 1
    have hn0 := image_ne f hi h0 (by decide : (2 : Fin 6) ≠ 4)
    have hn1 := image_ne f hi h1 (by decide : (3 : Fin 6) ≠ 4)
    have hn2 := image_ne f hi h2 (by decide : (0 : Fin 6) ≠ 4)
    have hn3 := image_ne f hi h3 (by decide : (1 : Fin 6) ≠ 4)
    have choices : f 4 = 4 ∨ f 4 = 5 := by omega
    rcases choices with h4 | h4
    · have hn0 := image_ne f hi h0 (by decide : (2 : Fin 6) ≠ 5)
      have hn1 := image_ne f hi h1 (by decide : (3 : Fin 6) ≠ 5)
      have hn2 := image_ne f hi h2 (by decide : (0 : Fin 6) ≠ 5)
      have hn3 := image_ne f hi h3 (by decide : (1 : Fin 6) ≠ 5)
      have hn4 := image_ne f hi h4 (by decide : (4 : Fin 6) ≠ 5)
      have choices : f 5 = 5 := by omega
      have h5 := choices
      have he : f = ![2,3,0,1,4,5] := by
        funext i
        fin_cases i <;> assumption
      refine ⟨9, ?_⟩
      rw [he]
      decide
    · have h5 : f 5 = 4 := by simpa only [h4] using hi 4
      have he : f = ![2,3,0,1,5,4] := by
        funext i
        fin_cases i <;> assumption
      rw [he] at hc
      exfalso
      exact (by decide : ¬ ColumnChecks (liftColumn ![2,3,0,1,5,4])) hc
  · have h4 : f 4 = 1 := by simpa only [h1] using hi 1
    have hn0 := image_ne f hi h0 (by decide : (2 : Fin 6) ≠ 3)
    have hn1 := image_ne f hi h1 (by decide : (4 : Fin 6) ≠ 3)
    have hn2 := image_ne f hi h2 (by decide : (0 : Fin 6) ≠ 3)
    have hn4 := image_ne f hi h4 (by decide : (1 : Fin 6) ≠ 3)
    have choices : f 3 = 3 ∨ f 3 = 5 := by omega
    rcases choices with h3 | h3
    · have hn0 := image_ne f hi h0 (by decide : (2 : Fin 6) ≠ 5)
      have hn1 := image_ne f hi h1 (by decide : (4 : Fin 6) ≠ 5)
      have hn2 := image_ne f hi h2 (by decide : (0 : Fin 6) ≠ 5)
      have hn3 := image_ne f hi h3 (by decide : (3 : Fin 6) ≠ 5)
      have hn4 := image_ne f hi h4 (by decide : (1 : Fin 6) ≠ 5)
      have choices : f 5 = 5 := by omega
      have h5 := choices
      have he : f = ![2,4,0,3,1,5] := by
        funext i
        fin_cases i <;> assumption
      rw [he] at hc
      exfalso
      exact (by decide : ¬ ColumnChecks (liftColumn ![2,4,0,3,1,5])) hc
    · have h5 : f 5 = 3 := by simpa only [h3] using hi 3
      have he : f = ![2,4,0,5,1,3] := by
        funext i
        fin_cases i <;> assumption
      rw [he] at hc
      exfalso
      exact (by decide : ¬ ColumnChecks (liftColumn ![2,4,0,5,1,3])) hc
  · have h5 : f 5 = 1 := by simpa only [h1] using hi 1
    have hn0 := image_ne f hi h0 (by decide : (2 : Fin 6) ≠ 3)
    have hn1 := image_ne f hi h1 (by decide : (5 : Fin 6) ≠ 3)
    have hn2 := image_ne f hi h2 (by decide : (0 : Fin 6) ≠ 3)
    have hn5 := image_ne f hi h5 (by decide : (1 : Fin 6) ≠ 3)
    have choices : f 3 = 3 ∨ f 3 = 4 := by omega
    rcases choices with h3 | h3
    · have hn0 := image_ne f hi h0 (by decide : (2 : Fin 6) ≠ 4)
      have hn1 := image_ne f hi h1 (by decide : (5 : Fin 6) ≠ 4)
      have hn2 := image_ne f hi h2 (by decide : (0 : Fin 6) ≠ 4)
      have hn3 := image_ne f hi h3 (by decide : (3 : Fin 6) ≠ 4)
      have hn5 := image_ne f hi h5 (by decide : (1 : Fin 6) ≠ 4)
      have choices : f 4 = 4 := by omega
      have h4 := choices
      have he : f = ![2,5,0,3,4,1] := by
        funext i
        fin_cases i <;> assumption
      rw [he] at hc
      exfalso
      exact (by decide : ¬ ColumnChecks (liftColumn ![2,5,0,3,4,1])) hc
    · have h4 : f 4 = 3 := by simpa only [h3] using hi 3
      have he : f = ![2,5,0,4,3,1] := by
        funext i
        fin_cases i <;> assumption
      rw [he] at hc
      exfalso
      exact (by decide : ¬ ColumnChecks (liftColumn ![2,5,0,4,3,1])) hc

private theorem image_zero_3 (f : Fin 6 → Fin 6)
    (hi : Function.Involutive f) (hc : ColumnChecks (liftColumn f))
    (h0 : f 0 = 3) : ∃ q : Fin 16, liftColumn f = columnCandidate q := by
  have h3 : f 3 = 0 := by simpa only [h0] using hi 0
  have hn0 := image_ne f hi h0 (by decide : (3 : Fin 6) ≠ 1)
  have hn3 := image_ne f hi h3 (by decide : (0 : Fin 6) ≠ 1)
  have choices : f 1 = 1 ∨ f 1 = 2 ∨ f 1 = 4 ∨ f 1 = 5 := by omega
  rcases choices with h1 | h1 | h1 | h1
  · have hn0 := image_ne f hi h0 (by decide : (3 : Fin 6) ≠ 2)
    have hn1 := image_ne f hi h1 (by decide : (1 : Fin 6) ≠ 2)
    have hn3 := image_ne f hi h3 (by decide : (0 : Fin 6) ≠ 2)
    have choices : f 2 = 2 ∨ f 2 = 4 ∨ f 2 = 5 := by omega
    rcases choices with h2 | h2 | h2
    · have hn0 := image_ne f hi h0 (by decide : (3 : Fin 6) ≠ 4)
      have hn1 := image_ne f hi h1 (by decide : (1 : Fin 6) ≠ 4)
      have hn2 := image_ne f hi h2 (by decide : (2 : Fin 6) ≠ 4)
      have hn3 := image_ne f hi h3 (by decide : (0 : Fin 6) ≠ 4)
      have choices : f 4 = 4 ∨ f 4 = 5 := by omega
      rcases choices with h4 | h4
      · have hn0 := image_ne f hi h0 (by decide : (3 : Fin 6) ≠ 5)
        have hn1 := image_ne f hi h1 (by decide : (1 : Fin 6) ≠ 5)
        have hn2 := image_ne f hi h2 (by decide : (2 : Fin 6) ≠ 5)
        have hn3 := image_ne f hi h3 (by decide : (0 : Fin 6) ≠ 5)
        have hn4 := image_ne f hi h4 (by decide : (4 : Fin 6) ≠ 5)
        have choices : f 5 = 5 := by omega
        have h5 := choices
        have he : f = ![3,1,2,0,4,5] := by
          funext i
          fin_cases i <;> assumption
        rw [he] at hc
        exfalso
        exact (by decide : ¬ ColumnChecks (liftColumn ![3,1,2,0,4,5])) hc
      · have h5 : f 5 = 4 := by simpa only [h4] using hi 4
        have he : f = ![3,1,2,0,5,4] := by
          funext i
          fin_cases i <;> assumption
        rw [he] at hc
        exfalso
        exact (by decide : ¬ ColumnChecks (liftColumn ![3,1,2,0,5,4])) hc
    · have h4 : f 4 = 2 := by simpa only [h2] using hi 2
      have hn0 := image_ne f hi h0 (by decide : (3 : Fin 6) ≠ 5)
      have hn1 := image_ne f hi h1 (by decide : (1 : Fin 6) ≠ 5)
      have hn2 := image_ne f hi h2 (by decide : (4 : Fin 6) ≠ 5)
      have hn3 := image_ne f hi h3 (by decide : (0 : Fin 6) ≠ 5)
      have hn4 := image_ne f hi h4 (by decide : (2 : Fin 6) ≠ 5)
      have choices : f 5 = 5 := by omega
      have h5 := choices
      have he : f = ![3,1,4,0,2,5] := by
        funext i
        fin_cases i <;> assumption
      rw [he] at hc
      exfalso
      exact (by decide : ¬ ColumnChecks (liftColumn ![3,1,4,0,2,5])) hc
    · have h5 : f 5 = 2 := by simpa only [h2] using hi 2
      have hn0 := image_ne f hi h0 (by decide : (3 : Fin 6) ≠ 4)
      have hn1 := image_ne f hi h1 (by decide : (1 : Fin 6) ≠ 4)
      have hn2 := image_ne f hi h2 (by decide : (5 : Fin 6) ≠ 4)
      have hn3 := image_ne f hi h3 (by decide : (0 : Fin 6) ≠ 4)
      have hn5 := image_ne f hi h5 (by decide : (2 : Fin 6) ≠ 4)
      have choices : f 4 = 4 := by omega
      have h4 := choices
      have he : f = ![3,1,5,0,4,2] := by
        funext i
        fin_cases i <;> assumption
      refine ⟨10, ?_⟩
      rw [he]
      decide
  · have h2 : f 2 = 1 := by simpa only [h1] using hi 1
    have hn0 := image_ne f hi h0 (by decide : (3 : Fin 6) ≠ 4)
    have hn1 := image_ne f hi h1 (by decide : (2 : Fin 6) ≠ 4)
    have hn2 := image_ne f hi h2 (by decide : (1 : Fin 6) ≠ 4)
    have hn3 := image_ne f hi h3 (by decide : (0 : Fin 6) ≠ 4)
    have choices : f 4 = 4 ∨ f 4 = 5 := by omega
    rcases choices with h4 | h4
    · have hn0 := image_ne f hi h0 (by decide : (3 : Fin 6) ≠ 5)
      have hn1 := image_ne f hi h1 (by decide : (2 : Fin 6) ≠ 5)
      have hn2 := image_ne f hi h2 (by decide : (1 : Fin 6) ≠ 5)
      have hn3 := image_ne f hi h3 (by decide : (0 : Fin 6) ≠ 5)
      have hn4 := image_ne f hi h4 (by decide : (4 : Fin 6) ≠ 5)
      have choices : f 5 = 5 := by omega
      have h5 := choices
      have he : f = ![3,2,1,0,4,5] := by
        funext i
        fin_cases i <;> assumption
      rw [he] at hc
      exfalso
      exact (by decide : ¬ ColumnChecks (liftColumn ![3,2,1,0,4,5])) hc
    · have h5 : f 5 = 4 := by simpa only [h4] using hi 4
      have he : f = ![3,2,1,0,5,4] := by
        funext i
        fin_cases i <;> assumption
      rw [he] at hc
      exfalso
      exact (by decide : ¬ ColumnChecks (liftColumn ![3,2,1,0,5,4])) hc
  · have h4 : f 4 = 1 := by simpa only [h1] using hi 1
    have hn0 := image_ne f hi h0 (by decide : (3 : Fin 6) ≠ 2)
    have hn1 := image_ne f hi h1 (by decide : (4 : Fin 6) ≠ 2)
    have hn3 := image_ne f hi h3 (by decide : (0 : Fin 6) ≠ 2)
    have hn4 := image_ne f hi h4 (by decide : (1 : Fin 6) ≠ 2)
    have choices : f 2 = 2 ∨ f 2 = 5 := by omega
    rcases choices with h2 | h2
    · have hn0 := image_ne f hi h0 (by decide : (3 : Fin 6) ≠ 5)
      have hn1 := image_ne f hi h1 (by decide : (4 : Fin 6) ≠ 5)
      have hn2 := image_ne f hi h2 (by decide : (2 : Fin 6) ≠ 5)
      have hn3 := image_ne f hi h3 (by decide : (0 : Fin 6) ≠ 5)
      have hn4 := image_ne f hi h4 (by decide : (1 : Fin 6) ≠ 5)
      have choices : f 5 = 5 := by omega
      have h5 := choices
      have he : f = ![3,4,2,0,1,5] := by
        funext i
        fin_cases i <;> assumption
      refine ⟨11, ?_⟩
      rw [he]
      decide
    · have h5 : f 5 = 2 := by simpa only [h2] using hi 2
      have he : f = ![3,4,5,0,1,2] := by
        funext i
        fin_cases i <;> assumption
      rw [he] at hc
      exfalso
      exact (by decide : ¬ ColumnChecks (liftColumn ![3,4,5,0,1,2])) hc
  · have h5 : f 5 = 1 := by simpa only [h1] using hi 1
    have hn0 := image_ne f hi h0 (by decide : (3 : Fin 6) ≠ 2)
    have hn1 := image_ne f hi h1 (by decide : (5 : Fin 6) ≠ 2)
    have hn3 := image_ne f hi h3 (by decide : (0 : Fin 6) ≠ 2)
    have hn5 := image_ne f hi h5 (by decide : (1 : Fin 6) ≠ 2)
    have choices : f 2 = 2 ∨ f 2 = 4 := by omega
    rcases choices with h2 | h2
    · have hn0 := image_ne f hi h0 (by decide : (3 : Fin 6) ≠ 4)
      have hn1 := image_ne f hi h1 (by decide : (5 : Fin 6) ≠ 4)
      have hn2 := image_ne f hi h2 (by decide : (2 : Fin 6) ≠ 4)
      have hn3 := image_ne f hi h3 (by decide : (0 : Fin 6) ≠ 4)
      have hn5 := image_ne f hi h5 (by decide : (1 : Fin 6) ≠ 4)
      have choices : f 4 = 4 := by omega
      have h4 := choices
      have he : f = ![3,5,2,0,4,1] := by
        funext i
        fin_cases i <;> assumption
      rw [he] at hc
      exfalso
      exact (by decide : ¬ ColumnChecks (liftColumn ![3,5,2,0,4,1])) hc
    · have h4 : f 4 = 2 := by simpa only [h2] using hi 2
      have he : f = ![3,5,4,0,2,1] := by
        funext i
        fin_cases i <;> assumption
      rw [he] at hc
      exfalso
      exact (by decide : ¬ ColumnChecks (liftColumn ![3,5,4,0,2,1])) hc

private theorem image_zero_4 (f : Fin 6 → Fin 6)
    (hi : Function.Involutive f) (hc : ColumnChecks (liftColumn f))
    (h0 : f 0 = 4) : ∃ q : Fin 16, liftColumn f = columnCandidate q := by
  have h4 : f 4 = 0 := by simpa only [h0] using hi 0
  have hn0 := image_ne f hi h0 (by decide : (4 : Fin 6) ≠ 1)
  have hn4 := image_ne f hi h4 (by decide : (0 : Fin 6) ≠ 1)
  have choices : f 1 = 1 ∨ f 1 = 2 ∨ f 1 = 3 ∨ f 1 = 5 := by omega
  rcases choices with h1 | h1 | h1 | h1
  · have hn0 := image_ne f hi h0 (by decide : (4 : Fin 6) ≠ 2)
    have hn1 := image_ne f hi h1 (by decide : (1 : Fin 6) ≠ 2)
    have hn4 := image_ne f hi h4 (by decide : (0 : Fin 6) ≠ 2)
    have choices : f 2 = 2 ∨ f 2 = 3 ∨ f 2 = 5 := by omega
    rcases choices with h2 | h2 | h2
    · have hn0 := image_ne f hi h0 (by decide : (4 : Fin 6) ≠ 3)
      have hn1 := image_ne f hi h1 (by decide : (1 : Fin 6) ≠ 3)
      have hn2 := image_ne f hi h2 (by decide : (2 : Fin 6) ≠ 3)
      have hn4 := image_ne f hi h4 (by decide : (0 : Fin 6) ≠ 3)
      have choices : f 3 = 3 ∨ f 3 = 5 := by omega
      rcases choices with h3 | h3
      · have hn0 := image_ne f hi h0 (by decide : (4 : Fin 6) ≠ 5)
        have hn1 := image_ne f hi h1 (by decide : (1 : Fin 6) ≠ 5)
        have hn2 := image_ne f hi h2 (by decide : (2 : Fin 6) ≠ 5)
        have hn3 := image_ne f hi h3 (by decide : (3 : Fin 6) ≠ 5)
        have hn4 := image_ne f hi h4 (by decide : (0 : Fin 6) ≠ 5)
        have choices : f 5 = 5 := by omega
        have h5 := choices
        have he : f = ![4,1,2,3,0,5] := by
          funext i
          fin_cases i <;> assumption
        rw [he] at hc
        exfalso
        exact (by decide : ¬ ColumnChecks (liftColumn ![4,1,2,3,0,5])) hc
      · have h5 : f 5 = 3 := by simpa only [h3] using hi 3
        have he : f = ![4,1,2,5,0,3] := by
          funext i
          fin_cases i <;> assumption
        rw [he] at hc
        exfalso
        exact (by decide : ¬ ColumnChecks (liftColumn ![4,1,2,5,0,3])) hc
    · have h3 : f 3 = 2 := by simpa only [h2] using hi 2
      have hn0 := image_ne f hi h0 (by decide : (4 : Fin 6) ≠ 5)
      have hn1 := image_ne f hi h1 (by decide : (1 : Fin 6) ≠ 5)
      have hn2 := image_ne f hi h2 (by decide : (3 : Fin 6) ≠ 5)
      have hn3 := image_ne f hi h3 (by decide : (2 : Fin 6) ≠ 5)
      have hn4 := image_ne f hi h4 (by decide : (0 : Fin 6) ≠ 5)
      have choices : f 5 = 5 := by omega
      have h5 := choices
      have he : f = ![4,1,3,2,0,5] := by
        funext i
        fin_cases i <;> assumption
      refine ⟨12, ?_⟩
      rw [he]
      decide
    · have h5 : f 5 = 2 := by simpa only [h2] using hi 2
      have hn0 := image_ne f hi h0 (by decide : (4 : Fin 6) ≠ 3)
      have hn1 := image_ne f hi h1 (by decide : (1 : Fin 6) ≠ 3)
      have hn2 := image_ne f hi h2 (by decide : (5 : Fin 6) ≠ 3)
      have hn4 := image_ne f hi h4 (by decide : (0 : Fin 6) ≠ 3)
      have hn5 := image_ne f hi h5 (by decide : (2 : Fin 6) ≠ 3)
      have choices : f 3 = 3 := by omega
      have h3 := choices
      have he : f = ![4,1,5,3,0,2] := by
        funext i
        fin_cases i <;> assumption
      rw [he] at hc
      exfalso
      exact (by decide : ¬ ColumnChecks (liftColumn ![4,1,5,3,0,2])) hc
  · have h2 : f 2 = 1 := by simpa only [h1] using hi 1
    have hn0 := image_ne f hi h0 (by decide : (4 : Fin 6) ≠ 3)
    have hn1 := image_ne f hi h1 (by decide : (2 : Fin 6) ≠ 3)
    have hn2 := image_ne f hi h2 (by decide : (1 : Fin 6) ≠ 3)
    have hn4 := image_ne f hi h4 (by decide : (0 : Fin 6) ≠ 3)
    have choices : f 3 = 3 ∨ f 3 = 5 := by omega
    rcases choices with h3 | h3
    · have hn0 := image_ne f hi h0 (by decide : (4 : Fin 6) ≠ 5)
      have hn1 := image_ne f hi h1 (by decide : (2 : Fin 6) ≠ 5)
      have hn2 := image_ne f hi h2 (by decide : (1 : Fin 6) ≠ 5)
      have hn3 := image_ne f hi h3 (by decide : (3 : Fin 6) ≠ 5)
      have hn4 := image_ne f hi h4 (by decide : (0 : Fin 6) ≠ 5)
      have choices : f 5 = 5 := by omega
      have h5 := choices
      have he : f = ![4,2,1,3,0,5] := by
        funext i
        fin_cases i <;> assumption
      rw [he] at hc
      exfalso
      exact (by decide : ¬ ColumnChecks (liftColumn ![4,2,1,3,0,5])) hc
    · have h5 : f 5 = 3 := by simpa only [h3] using hi 3
      have he : f = ![4,2,1,5,0,3] := by
        funext i
        fin_cases i <;> assumption
      rw [he] at hc
      exfalso
      exact (by decide : ¬ ColumnChecks (liftColumn ![4,2,1,5,0,3])) hc
  · have h3 : f 3 = 1 := by simpa only [h1] using hi 1
    have hn0 := image_ne f hi h0 (by decide : (4 : Fin 6) ≠ 2)
    have hn1 := image_ne f hi h1 (by decide : (3 : Fin 6) ≠ 2)
    have hn3 := image_ne f hi h3 (by decide : (1 : Fin 6) ≠ 2)
    have hn4 := image_ne f hi h4 (by decide : (0 : Fin 6) ≠ 2)
    have choices : f 2 = 2 ∨ f 2 = 5 := by omega
    rcases choices with h2 | h2
    · have hn0 := image_ne f hi h0 (by decide : (4 : Fin 6) ≠ 5)
      have hn1 := image_ne f hi h1 (by decide : (3 : Fin 6) ≠ 5)
      have hn2 := image_ne f hi h2 (by decide : (2 : Fin 6) ≠ 5)
      have hn3 := image_ne f hi h3 (by decide : (1 : Fin 6) ≠ 5)
      have hn4 := image_ne f hi h4 (by decide : (0 : Fin 6) ≠ 5)
      have choices : f 5 = 5 := by omega
      have h5 := choices
      have he : f = ![4,3,2,1,0,5] := by
        funext i
        fin_cases i <;> assumption
      rw [he] at hc
      exfalso
      exact (by decide : ¬ ColumnChecks (liftColumn ![4,3,2,1,0,5])) hc
    · have h5 : f 5 = 2 := by simpa only [h2] using hi 2
      have he : f = ![4,3,5,1,0,2] := by
        funext i
        fin_cases i <;> assumption
      rw [he] at hc
      exfalso
      exact (by decide : ¬ ColumnChecks (liftColumn ![4,3,5,1,0,2])) hc
  · have h5 : f 5 = 1 := by simpa only [h1] using hi 1
    have hn0 := image_ne f hi h0 (by decide : (4 : Fin 6) ≠ 2)
    have hn1 := image_ne f hi h1 (by decide : (5 : Fin 6) ≠ 2)
    have hn4 := image_ne f hi h4 (by decide : (0 : Fin 6) ≠ 2)
    have hn5 := image_ne f hi h5 (by decide : (1 : Fin 6) ≠ 2)
    have choices : f 2 = 2 ∨ f 2 = 3 := by omega
    rcases choices with h2 | h2
    · have hn0 := image_ne f hi h0 (by decide : (4 : Fin 6) ≠ 3)
      have hn1 := image_ne f hi h1 (by decide : (5 : Fin 6) ≠ 3)
      have hn2 := image_ne f hi h2 (by decide : (2 : Fin 6) ≠ 3)
      have hn4 := image_ne f hi h4 (by decide : (0 : Fin 6) ≠ 3)
      have hn5 := image_ne f hi h5 (by decide : (1 : Fin 6) ≠ 3)
      have choices : f 3 = 3 := by omega
      have h3 := choices
      have he : f = ![4,5,2,3,0,1] := by
        funext i
        fin_cases i <;> assumption
      refine ⟨13, ?_⟩
      rw [he]
      decide
    · have h3 : f 3 = 2 := by simpa only [h2] using hi 2
      have he : f = ![4,5,3,2,0,1] := by
        funext i
        fin_cases i <;> assumption
      rw [he] at hc
      exfalso
      exact (by decide : ¬ ColumnChecks (liftColumn ![4,5,3,2,0,1])) hc

private theorem image_zero_5 (f : Fin 6 → Fin 6)
    (hi : Function.Involutive f) (hc : ColumnChecks (liftColumn f))
    (h0 : f 0 = 5) : ∃ q : Fin 16, liftColumn f = columnCandidate q := by
  have h5 : f 5 = 0 := by simpa only [h0] using hi 0
  have hn0 := image_ne f hi h0 (by decide : (5 : Fin 6) ≠ 1)
  have hn5 := image_ne f hi h5 (by decide : (0 : Fin 6) ≠ 1)
  have choices : f 1 = 1 ∨ f 1 = 2 ∨ f 1 = 3 ∨ f 1 = 4 := by omega
  rcases choices with h1 | h1 | h1 | h1
  · have hn0 := image_ne f hi h0 (by decide : (5 : Fin 6) ≠ 2)
    have hn1 := image_ne f hi h1 (by decide : (1 : Fin 6) ≠ 2)
    have hn5 := image_ne f hi h5 (by decide : (0 : Fin 6) ≠ 2)
    have choices : f 2 = 2 ∨ f 2 = 3 ∨ f 2 = 4 := by omega
    rcases choices with h2 | h2 | h2
    · have hn0 := image_ne f hi h0 (by decide : (5 : Fin 6) ≠ 3)
      have hn1 := image_ne f hi h1 (by decide : (1 : Fin 6) ≠ 3)
      have hn2 := image_ne f hi h2 (by decide : (2 : Fin 6) ≠ 3)
      have hn5 := image_ne f hi h5 (by decide : (0 : Fin 6) ≠ 3)
      have choices : f 3 = 3 ∨ f 3 = 4 := by omega
      rcases choices with h3 | h3
      · have hn0 := image_ne f hi h0 (by decide : (5 : Fin 6) ≠ 4)
        have hn1 := image_ne f hi h1 (by decide : (1 : Fin 6) ≠ 4)
        have hn2 := image_ne f hi h2 (by decide : (2 : Fin 6) ≠ 4)
        have hn3 := image_ne f hi h3 (by decide : (3 : Fin 6) ≠ 4)
        have hn5 := image_ne f hi h5 (by decide : (0 : Fin 6) ≠ 4)
        have choices : f 4 = 4 := by omega
        have h4 := choices
        have he : f = ![5,1,2,3,4,0] := by
          funext i
          fin_cases i <;> assumption
        rw [he] at hc
        exfalso
        exact (by decide : ¬ ColumnChecks (liftColumn ![5,1,2,3,4,0])) hc
      · have h4 : f 4 = 3 := by simpa only [h3] using hi 3
        have he : f = ![5,1,2,4,3,0] := by
          funext i
          fin_cases i <;> assumption
        refine ⟨14, ?_⟩
        rw [he]
        decide
    · have h3 : f 3 = 2 := by simpa only [h2] using hi 2
      have hn0 := image_ne f hi h0 (by decide : (5 : Fin 6) ≠ 4)
      have hn1 := image_ne f hi h1 (by decide : (1 : Fin 6) ≠ 4)
      have hn2 := image_ne f hi h2 (by decide : (3 : Fin 6) ≠ 4)
      have hn3 := image_ne f hi h3 (by decide : (2 : Fin 6) ≠ 4)
      have hn5 := image_ne f hi h5 (by decide : (0 : Fin 6) ≠ 4)
      have choices : f 4 = 4 := by omega
      have h4 := choices
      have he : f = ![5,1,3,2,4,0] := by
        funext i
        fin_cases i <;> assumption
      rw [he] at hc
      exfalso
      exact (by decide : ¬ ColumnChecks (liftColumn ![5,1,3,2,4,0])) hc
    · have h4 : f 4 = 2 := by simpa only [h2] using hi 2
      have hn0 := image_ne f hi h0 (by decide : (5 : Fin 6) ≠ 3)
      have hn1 := image_ne f hi h1 (by decide : (1 : Fin 6) ≠ 3)
      have hn2 := image_ne f hi h2 (by decide : (4 : Fin 6) ≠ 3)
      have hn4 := image_ne f hi h4 (by decide : (2 : Fin 6) ≠ 3)
      have hn5 := image_ne f hi h5 (by decide : (0 : Fin 6) ≠ 3)
      have choices : f 3 = 3 := by omega
      have h3 := choices
      have he : f = ![5,1,4,3,2,0] := by
        funext i
        fin_cases i <;> assumption
      rw [he] at hc
      exfalso
      exact (by decide : ¬ ColumnChecks (liftColumn ![5,1,4,3,2,0])) hc
  · have h2 : f 2 = 1 := by simpa only [h1] using hi 1
    have hn0 := image_ne f hi h0 (by decide : (5 : Fin 6) ≠ 3)
    have hn1 := image_ne f hi h1 (by decide : (2 : Fin 6) ≠ 3)
    have hn2 := image_ne f hi h2 (by decide : (1 : Fin 6) ≠ 3)
    have hn5 := image_ne f hi h5 (by decide : (0 : Fin 6) ≠ 3)
    have choices : f 3 = 3 ∨ f 3 = 4 := by omega
    rcases choices with h3 | h3
    · have hn0 := image_ne f hi h0 (by decide : (5 : Fin 6) ≠ 4)
      have hn1 := image_ne f hi h1 (by decide : (2 : Fin 6) ≠ 4)
      have hn2 := image_ne f hi h2 (by decide : (1 : Fin 6) ≠ 4)
      have hn3 := image_ne f hi h3 (by decide : (3 : Fin 6) ≠ 4)
      have hn5 := image_ne f hi h5 (by decide : (0 : Fin 6) ≠ 4)
      have choices : f 4 = 4 := by omega
      have h4 := choices
      have he : f = ![5,2,1,3,4,0] := by
        funext i
        fin_cases i <;> assumption
      refine ⟨15, ?_⟩
      rw [he]
      decide
    · have h4 : f 4 = 3 := by simpa only [h3] using hi 3
      have he : f = ![5,2,1,4,3,0] := by
        funext i
        fin_cases i <;> assumption
      rw [he] at hc
      exfalso
      exact (by decide : ¬ ColumnChecks (liftColumn ![5,2,1,4,3,0])) hc
  · have h3 : f 3 = 1 := by simpa only [h1] using hi 1
    have hn0 := image_ne f hi h0 (by decide : (5 : Fin 6) ≠ 2)
    have hn1 := image_ne f hi h1 (by decide : (3 : Fin 6) ≠ 2)
    have hn3 := image_ne f hi h3 (by decide : (1 : Fin 6) ≠ 2)
    have hn5 := image_ne f hi h5 (by decide : (0 : Fin 6) ≠ 2)
    have choices : f 2 = 2 ∨ f 2 = 4 := by omega
    rcases choices with h2 | h2
    · have hn0 := image_ne f hi h0 (by decide : (5 : Fin 6) ≠ 4)
      have hn1 := image_ne f hi h1 (by decide : (3 : Fin 6) ≠ 4)
      have hn2 := image_ne f hi h2 (by decide : (2 : Fin 6) ≠ 4)
      have hn3 := image_ne f hi h3 (by decide : (1 : Fin 6) ≠ 4)
      have hn5 := image_ne f hi h5 (by decide : (0 : Fin 6) ≠ 4)
      have choices : f 4 = 4 := by omega
      have h4 := choices
      have he : f = ![5,3,2,1,4,0] := by
        funext i
        fin_cases i <;> assumption
      rw [he] at hc
      exfalso
      exact (by decide : ¬ ColumnChecks (liftColumn ![5,3,2,1,4,0])) hc
    · have h4 : f 4 = 2 := by simpa only [h2] using hi 2
      have he : f = ![5,3,4,1,2,0] := by
        funext i
        fin_cases i <;> assumption
      rw [he] at hc
      exfalso
      exact (by decide : ¬ ColumnChecks (liftColumn ![5,3,4,1,2,0])) hc
  · have h4 : f 4 = 1 := by simpa only [h1] using hi 1
    have hn0 := image_ne f hi h0 (by decide : (5 : Fin 6) ≠ 2)
    have hn1 := image_ne f hi h1 (by decide : (4 : Fin 6) ≠ 2)
    have hn4 := image_ne f hi h4 (by decide : (1 : Fin 6) ≠ 2)
    have hn5 := image_ne f hi h5 (by decide : (0 : Fin 6) ≠ 2)
    have choices : f 2 = 2 ∨ f 2 = 3 := by omega
    rcases choices with h2 | h2
    · have hn0 := image_ne f hi h0 (by decide : (5 : Fin 6) ≠ 3)
      have hn1 := image_ne f hi h1 (by decide : (4 : Fin 6) ≠ 3)
      have hn2 := image_ne f hi h2 (by decide : (2 : Fin 6) ≠ 3)
      have hn4 := image_ne f hi h4 (by decide : (1 : Fin 6) ≠ 3)
      have hn5 := image_ne f hi h5 (by decide : (0 : Fin 6) ≠ 3)
      have choices : f 3 = 3 := by omega
      have h3 := choices
      have he : f = ![5,4,2,3,1,0] := by
        funext i
        fin_cases i <;> assumption
      rw [he] at hc
      exfalso
      exact (by decide : ¬ ColumnChecks (liftColumn ![5,4,2,3,1,0])) hc
    · have h3 : f 3 = 2 := by simpa only [h2] using hi 2
      have he : f = ![5,4,3,2,1,0] := by
        funext i
        fin_cases i <;> assumption
      rw [he] at hc
      exfalso
      exact (by decide : ¬ ColumnChecks (liftColumn ![5,4,3,2,1,0])) hc

/-- Every involutive column map satisfying the actual generator equations
is one of the sixteen entries, in the original `hexIndexEquiv` convention. -/
theorem columnCoverage : ColumnCoverage := by
  intro pi hc
  let f : Fin 6 → Fin 6 := fun i => hexIndexEquiv (pi (hexIndexEquiv.symm i))
  have hi : Function.Involutive f := by
    intro i
    change hexIndexEquiv (pi (hexIndexEquiv.symm
      (hexIndexEquiv (pi (hexIndexEquiv.symm i))))) = i
    rw [Equiv.symm_apply_apply, hc.1, Equiv.apply_symm_apply]
  have he : liftColumn f = pi := by
    funext i
    simp only [liftColumn, f, Equiv.symm_apply_apply]
  have hc' : ColumnChecks (liftColumn f) := by rw [he]; exact hc
  have h : ∃ q : Fin 16, liftColumn f = columnCandidate q := by
    have choices : f 0 = 0 ∨ f 0 = 1 ∨ f 0 = 2 ∨ f 0 = 3 ∨ f 0 = 4 ∨ f 0 = 5 := by omega
    rcases choices with h0 | h0 | h0 | h0 | h0 | h0
    · exact image_zero_0 f hi hc' h0
    · exact image_zero_1 f hi hc' h0
    · exact image_zero_2 f hi hc' h0
    · exact image_zero_3 f hi hc' h0
    · exact image_zero_4 f hi hc' h0
    · exact image_zero_5 f hi hc' h0
  obtain ⟨q, hq⟩ := h
  exact ⟨q, he.symm.trans hq⟩

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.Fusion.ReferenceBound.Coverage
