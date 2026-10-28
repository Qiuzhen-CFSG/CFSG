module

public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.ElementaryWords
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.ProperInclusions.WordTests
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.FourGroupNormalizers.WordActions
public import Theory.SpecificGroups.Held.LocalPairs.SylowGeometry.Calculations.InnerNormalizer.GraphBound.Basic

/-!
# Fixed points of the second literal Held four-group

The two unchanged row generators have exactly 26 common fixed vertices.
Their common fixed set is the fixed set of their generated ambient subgroup,
so its setwise invariance holds for the full Held normalizer. The finite
check uses the already certified tables for the four representative generators.

Sources: the ATLAS degree-2058 action; GLS3 Table 5.3p; the four-group
inspection in Aschbacher–Smith 15.3.43, printed p.1140.
-/

namespace Held.TwoLocalCandidates.MaximalNormalizerCatalogue.FourGroupNormalizers.RowTwo
open Subgroup ProperInclusions LocalPairs.SylowGeometry.Calculations
open InnerNormalizer.GraphBound WordActions

set_option Elab.async false

@[expose] public def fixedVertices : List (Fin 2058) := [379, 480, 502, 512, 557, 719, 731, 778, 863, 892, 944, 1016, 1282, 1334, 1386, 1444, 1480, 1490, 1613, 1645, 1665, 1672, 1728, 1877, 1912, 1937]

@[expose] public def fixedSet : Finset (Fin 2058) := fixedVertices.toFinset

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private theorem fixed_checked : ∀ x : Fin 2058, x ∈ fixedSet ↔
    fastWord [-3, -4, 2, 1, 2, -4, -2, -1, -3, -2] x = x ∧
      fastWord commonWord x = x := by
  apply checked_forall
  decide +kernel

/-- The certified vertex set is the common fixed set of the actual ambient row. -/
public theorem mem_fixedSet_iff (x : Fin 2058) :
    x ∈ fixedSet ↔ ambient 2 ≤ MulAction.stabilizer He x := by
  rw [ambient_le_iff]
  have hc := fixed_checked x
  rw [fastWord_eq, fastWord_eq] at hc
  refine hc.trans ?_
  constructor
  · rintro ⟨hu, hv⟩ w hw
    simp only [generatorWords, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · exact hu
    · exact hv
  · intro h
    exact ⟨h _ (by simp [generatorWords]), h _ (by simp [generatorWords, commonWord])⟩

/-- Normalizing the row preserves its common fixed vertices. -/
public theorem fixedSet_invariant (g : He) (hg : g ∈ normalizer (ambient 2 : Set He))
    (x : Fin 2058) : g • x ∈ fixedSet ↔ x ∈ fixedSet := by
  have forward (k : He) (hk : k ∈ normalizer (ambient 2 : Set He)) (y : Fin 2058)
      (hy : y ∈ fixedSet) : k • y ∈ fixedSet := by
    apply (mem_fixedSet_iff _).mpr
    intro w hw
    have hc : k⁻¹ * w * k ∈ ambient 2 := by
      simpa only [inv_inv] using (mem_normalizer_iff.mp (inv_mem hk) w).mp hw
    have hf := (mem_fixedSet_iff y).mp hy hc
    change w • (k • y) = k • y
    calc
      w • (k • y) = k • ((k⁻¹ * w * k) • y) := by
        simp only [mul_smul, smul_inv_smul]
      _ = k • y := congrArg (k • ·) hf
  exact ⟨fun h => by simpa only [inv_smul_smul] using forward g⁻¹ (inv_mem hg) (g • x) h,
    forward g hg x⟩

end Held.TwoLocalCandidates.MaximalNormalizerCatalogue.FourGroupNormalizers.RowTwo
