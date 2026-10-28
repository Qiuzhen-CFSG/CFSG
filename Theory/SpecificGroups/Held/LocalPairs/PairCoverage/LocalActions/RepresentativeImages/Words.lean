module

public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.LocalActions.Candidates

/-!
# Marked generators for the Held representative planes

These are the two published words generating each literal odd candidate.
The descendants certify their permutation relations before constructing
coordinates. Source: ATLAS HeG1-max3W1/max4W1 and GLS3 Table 5.3p; the GAP
cycle inversion convention is already incorporated in Held's carrier.
-/

@[expose] public section
namespace Held.LocalPairs.PairCoverage.LocalActions.RepresentativeImages

/-- The published odd generators, in their original order. -/
def oddGenerator (i : Bool) (j k : Fin 2) : He :=
  evalLocalWord i (oddWord i j k)

theorem oddGenerator_mem (i : Bool) (j k : Fin 2) :
    oddGenerator i j k ∈ candidateOdd i j :=
  Subgroup.subset_closure ⟨k, rfl⟩

/-- Evaluate a local word after applying the faithful representation. -/
theorem representation_evalLocalWord (i : Bool) (w : List (Bool × ℤ)) :
    representation (evalLocalWord i w) =
      (w.map (fun t => (if t.1 then representation (localWord i) else atlasA) ^ t.2)).prod := by
  induction w with
  | nil => exact map_one representation
  | cons t w hw =>
    change representation ((if t.1 then localWord i else a) ^ t.2 * evalLocalWord i w) = _
    rw [map_mul, map_zpow, hw]
    rcases t with ⟨b, n⟩
    cases b <;> rfl

end Held.LocalPairs.PairCoverage.LocalActions.RepresentativeImages
