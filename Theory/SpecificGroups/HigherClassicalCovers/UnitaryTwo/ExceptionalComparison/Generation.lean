module

public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryTwo.ExceptionalComparison.OrbitChecks

/-!
# Generation of the full symplectic matrix group by the matched pair

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

/-- The two concrete matrices generate the full matrix group, before taking
its center quotient. -/
theorem symplectic_generators_generate :
    Subgroup.closure (Set.range symplecticGenerator) = ⊤ := by
  let H := Subgroup.closure (Set.range symplecticGenerator)
  have hgen (i : Fin 2) : symplecticGenerator i ∈ H :=
    Subgroup.subset_closure ⟨i, rfl⟩
  have hseed : transvection (orbitVector 0) 1 ∈ H := by
    rw [← seed_transvection]
    exact FreeGroup.range_lift_le Subgroup.subset_closure ⟨FreeGroup.mk seedWord, rfl⟩
  have horbit : ∀ n, ∀ hn : n < 80, transvection (orbitVector ⟨n, hn⟩) 1 ∈ H := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hn
      let i : Fin 80 := ⟨n, hn⟩
      by_cases hi : i = 0
      · change transvection (orbitVector i) 1 ∈ H
        simpa only [hi] using hseed
      · have hp : (orbitParent i).val < n := orbit_parent_lt i hi
        have hm := ih (orbitParent i).val hp (orbitParent i).isLt
        change transvection (orbitVector i) 1 ∈ H
        rw [← orbit_step i hi, ← transvection_conjugate]
        exact H.mul_mem (H.mul_mem (hgen _) hm) (H.inv_mem (hgen _))
  have hunit (v : Vector 2 (ZMod 3)) : transvection v 1 ∈ H := by
    rcases orbit_covers v with rfl | ⟨i, rfl⟩
    · simpa only [transvection_zero_vector] using H.one_mem
    · exact horbit i.val i.isLt
  have hall (v : Vector 2 (ZMod 3)) (a : ZMod 3) : transvection v a ∈ H := by
    fin_cases a
    · change transvection v (0 : ZMod 3) ∈ H
      rw [transvection_zero]
      exact H.one_mem
    · exact hunit v
    · change transvection v (1 + 1) ∈ H
      rw [transvection_add]
      exact H.mul_mem (hunit v) (hunit v)
  apply top_unique
  rw [← transvectionGroup_eq_top (n := 2) (F := ZMod 3)]
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨v, a, rfl⟩
  exact hall v a

/-- The checked presentation maps onto the specified projective symplectic
endpoint. No presentation-order assertion is used. -/
theorem toProjectiveSymplectic_surjective : Function.Surjective toProjectiveSymplectic := by
  let π := QuotientGroup.mk' (Subgroup.center
    (Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime.Sp (ZMod 3)))
  have hle : Subgroup.closure (Set.range symplecticGenerator) ≤
      toProjectiveSymplectic.range.comap π := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i, rfl⟩
    exact ⟨PresentedGroup.of i, toProjectiveSymplectic_generator i⟩
  rw [symplectic_generators_generate] at hle
  intro x
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective
    (Subgroup.center (Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime.Sp (ZMod 3))) x
  exact hle (Subgroup.mem_top g)

end Theory.SpecificGroups.HigherClassicalCovers.UnitaryTwo.ExceptionalComparison
