module
public import Theory.SpecificGroups.Tits.MinimumIndex.ThirteenOvergroups.PairGeneration.Representatives

/-!
# Two kernel-checked whole-group thirteen-pair generators

Recover the actual standard generators from the pairs at fixed representatives
6 and 7. The latter is a nontrivial 122-letter representative and provides a
measured example for the remaining finite certificate. Only points 0, 1, 2
need checking, by `Words.recoveryTest_sound` and its certified ambient base.
Signed exponents avoid expanding inverses into twelfth powers.

Source: primary ATLAS generators; the untrusted recovery words were found by
GAP. See `source/discover_seed.g` and `source/seed-recovery.json`. Lean checks
the resulting word identities independently.
-/

namespace Tits.MinimumIndexThirteen.PairGeneration

private def recoveryA : List (Bool × Int) := [
  (true, 1), (false, 1), (true, 1), (false, 1), (true, 2),
  (false, 3), (true, -2), (false, 1), (true, -2), (false, 1),
  (true, -2), (false, 1), (true, 1), (false, -1), (true, -1),
  (false, 1), (true, 2), (false, -1), (true, 1), (false, -2),
  (true, -1), (false, -4), (true, 1), (false, 2), (true, 1),
  (false, -1)]
private def recoveryB : List (Bool × Int) := [
  (true, -2), (false, -2), (true, 1), (false, -2), (true, 1),
  (false, -2), (true, -1), (false, 6), (true, -1), (false, 1),
  (true, -1), (false, -1), (true, 2), (false, -1), (true, 2),
  (false, -1), (true, 2), (false, -3), (true, -2)]

set_option maxRecDepth 20000 in
private theorem recovery_seven :
    recoveryTest (representativeCode 7) recoveryA 2 = true ∧
    recoveryTest (representativeCode 7) recoveryB 3 = true := by
  decide +kernel

public theorem pairSubgroup_representative_seven_eq_top :
    pairSubgroup (representative 7) = ⊤ :=
  pairSubgroup_eq_top_of_recovery _ recoveryA recoveryB recovery_seven.1 recovery_seven.2


set_option maxRecDepth 20000 in
private theorem recovery_six :
    recoveryTest (representativeCode 6) [(false, -1), (true, -1), (false, -1)] 2 = true ∧
    recoveryTest (representativeCode 6) [(false, -1), (true, -1)] 3 = true := by
  decide +kernel

/-- The standard involution and the marked thirteen-generator already generate. -/
public theorem pairSubgroup_representative_six_eq_top :
    pairSubgroup (representative 6) = ⊤ :=
  pairSubgroup_eq_top_of_recovery _ _ _ recovery_six.1 recovery_six.2

/-- Convert a certified whole-group pair into the exact candidate-derived output. -/
public theorem generation_of_pairSubgroup_eq_top {x : Atlas1600Group}
    (hx : pairSubgroup x = ⊤) :
    ∃ (i : Fin 3) (g : Atlas1600Group),
      candidateDerived i ≤ (pairSubgroup x).map (MulAut.conj g).toMonoidHom := by
  refine ⟨0, 1, ?_⟩
  simp [hx]

/-- Three entries of the fixed representative certificate, including its identity case. -/
public theorem representative_seed_cases (k : Fin 3010) (hk : k = 0 ∨ k = 6 ∨ k = 7) :
    representative k ∈ thirteenNormalizer ∨
      ∃ (i : Fin 3) (g : Atlas1600Group),
        candidateDerived i ≤ (pairSubgroup (representative k)).map
          (MulAut.conj g).toMonoidHom := by
  rcases hk with rfl | rfl | rfl
  · exact Or.inl representative_zero_mem
  · exact Or.inr (generation_of_pairSubgroup_eq_top pairSubgroup_representative_six_eq_top)
  · exact Or.inr (generation_of_pairSubgroup_eq_top pairSubgroup_representative_seven_eq_top)

end Tits.MinimumIndexThirteen.PairGeneration
