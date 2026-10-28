module

public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryTwo.ExceptionalComparison.OrbitData

/-!
# Checks of the symplectic transvection and orbit certificate

The word `(a⁻¹ b⁻¹)³` is an actual transvection. A checked orbit tree reaches
every nonzero vector of the ternary four-space using the two generators.
Conjugating the seed therefore supplies every parameter-one transvection;
squaring supplies parameter two. Transvection generation then proves that
the pair generates all of Sp₄(3), and that the presented-group homomorphism
surjects onto its literal center quotient.

This discharges the symplectic generation obligation in the exceptional
PSU₄(2)–PSp₄(3) comparison for Aschbacher–Smith I.1.4(1), printed p.408.
The data generator is untrusted; all matrix and orbit assertions are checked
in Lean, and the final generation deduction is structural.
-/

public section
open Matrix.PSp4Three
open Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime
namespace Theory.SpecificGroups.HigherClassicalCovers.UnitaryTwo.ExceptionalComparison

theorem seedPrefix_zero : seedPrefix 0 = 1 := by decide +kernel

theorem seedPrefix_step : ∀ k : Fin 6,
    seedPrefix k.val * symplecticValue (letterValue symplecticGenerator (seedWord[k.val]?)) =
      seedPrefix (k.val+1) := by decide +kernel

theorem seedPrefix_end :
    seedPrefix 6 = (transvection (orbitVector 0) 1).val := by decide +kernel

theorem seed_transvection :
    FreeGroup.lift symplecticGenerator (FreeGroup.mk seedWord) =
      transvection (orbitVector 0) 1 := by
  apply Subtype.ext
  have h := congrArg symplecticValue (wordValue_eq_range symplecticGenerator seedWord)
  rw [map_list_prod, List.map_map] at h
  change symplecticValue (FreeGroup.lift symplecticGenerator (FreeGroup.mk seedWord)) =
    ((List.range 6).map fun k =>
      symplecticValue (letterValue symplecticGenerator (seedWord[k]?))).prod at h
  rw [prefixProduct _ seedPrefix 6 seedPrefix_zero
    (fun k hk => seedPrefix_step ⟨k, hk⟩), seedPrefix_end] at h
  exact h

theorem orbit_parent_lt : ∀ i : Fin 80, i ≠ 0 → (orbitParent i).val < i.val := by
  decide +kernel

theorem orbit_step : ∀ i : Fin 80, i ≠ 0 →
    symplecticGenerator (orbitEdge i) • orbitVector (orbitParent i) = orbitVector i := by
  decide +kernel

theorem orbit_covers : ∀ v : Vector 2 (ZMod 3), v = 0 ∨ ∃ i, orbitVector i = v := by
  decide +kernel

end Theory.SpecificGroups.HigherClassicalCovers.UnitaryTwo.ExceptionalComparison
