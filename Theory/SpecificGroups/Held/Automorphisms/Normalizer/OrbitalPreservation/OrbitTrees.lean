module

public import Theory.SpecificGroups.Held.Automorphisms.Normalizer.OrbitalPreservation.Data
public import Theory.SpecificGroups.Held.Model.Transitivity

/-!
# Reachability in the five-component spanning forest

Every edge is a word in Held fixing zero. A kernel check verifies that an
edge decreases depth and preserves the component label. Induction therefore
reaches each vertex from its labeled representative inside the full point
stabilizer. This does not claim generation of that stabilizer.

Source: the exact ATLAS words and reproducible forest in `Data` and
`Source/generate_orbits.py`.
-/

namespace Held.NormalizerGraph.Orbital

public abbrev Stabilizer : Type := ↥(MulAction.stabilizer He (0 : Fin 2058))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem rawGen_fix : ∀ x, rawGen x • (0 : Fin 2058) = 0 := by decide +kernel
private def gen (x : Fin 4) : Stabilizer := ⟨rawGen x, rawGen_fix x⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem tree_valid : ∀ x : Fin 2058, x = rep (color x) ∨
    (depth (parent x) < depth x ∧ color (parent x) = color x ∧
      gen (step x) • parent x = x) := by decide +kernel

public theorem reach (x : Fin 2058) : ∃ g : Stabilizer, g • rep (color x) = x := by
  suffices h : ∀ n : ℕ, ∀ y, depth y = n → ∃ g : Stabilizer, g • rep (color y) = y from
    h (depth x) x rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro y hy
    rcases tree_valid y with he | ⟨hd, hc, hs⟩
    · exact ⟨1, by simpa using he.symm⟩
    · obtain ⟨g, hg⟩ := ih (depth (parent y)) (by omega) (parent y) rfl
      rw [hc] at hg
      exact ⟨gen (step y) * g, by rw [mul_smul, hg, hs]⟩


end Held.NormalizerGraph.Orbital
