module

public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.SylowOvergroups.Tests
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.SylowOvergroups.RepresentativeChecks.Text

/-!
# The local and obstruction branches of the fixed Held tests

This selector records the thirty proposed local rows of the candidate data.
It proves no local membership. All other indices require prime obstructions;
the disjunction over these branches recovers the exact `RepresentativeChecks`.

Source: `../source/representatives.json`, via `source/generate_branches.py`.
-/

namespace Held.LocalPairs.PairCoverage.SylowOvergroups.RepresentativeVerification

@[expose] public def localBranch (j : Fin 4831) : Option Bool :=
  match j.val with
  | 0 | 1 | 2 | 3 | 72 | 73 | 74 | 75 | 76 | 4278 | 4279 | 4280 | 4281 | 4291 | 4292 | 4293 | 4294 => some false
  | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 | 16 => some true
  | _ => none

/-- Membership obligations for precisely the thirty proposed local rows. -/
@[expose] public def LocalChecks : Prop :=
  ∀ (j : Fin 4831) (b : Bool), localBranch j = some b →
    representative j ∈ alignedOvergroup b

/-- Prime-order obstructions for every remaining representative. -/
@[expose] public def ObstructionChecks : Prop :=
  ∀ j : Fin 4831, localBranch j = none → HasPrimeObstruction (representative j)

/-- Both families must be proved before these are the requested tests. -/
public theorem representativeChecks_of_branches (hl : LocalChecks) (ho : ObstructionChecks) :
    RepresentativeChecks := by
  intro j
  cases h : localBranch j with
  | none => exact Or.inr (Or.inr (ho j h))
  | some b =>
    cases b with
    | false => exact Or.inl (hl j false h)
    | true => exact Or.inr (Or.inl (hl j true h))

set_option maxRecDepth 4096 in
/-- The identity row belongs to the literal first overgroup. -/
public theorem representative_zero_mem : representative 0 ∈ alignedOvergroup false := by
  have hw : representativeWord 0 = [] := by
    rw [representativeWord_eq_decodeText]
    rfl
  simpa only [representative, hw, wordEval] using (alignedOvergroup false).one_mem

end Held.LocalPairs.PairCoverage.SylowOvergroups.RepresentativeVerification
