module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Parabolics.Selection.LargerFieldBorel.Reduction
public import Theory.SpecificGroups.SymplecticFour.EvenProjective
public import Theory.SpecificGroups.SymplecticFour.Sylow.ThreeResidualPlacement.OvergroupGeometry

/-!
# Larger-field symplectic Borel containment

The genuine projective symplectic model is isomorphic to Sp₄ in characteristic
two. A proper overgroup P of the intrinsic Sylow normalizer contains that Sylow
subgroup, so the proved root geometry puts P in a conjugate of the full point
or plane parabolic. The solvable subgroup H lies in the same parabolic and
therefore normalizes its Sylow subgroup by the rank-one quotient calculation.
Transport through the actual central quotient equivalence gives the requested
control. No ordinary maximality of P is needed; P may itself be the Borel.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), 15.3.41(2),
printed p.1138, and the first paragraph of the final proof of 15.3.35, p.1139.
-/

public section

open Subgroup Theory.SpecificGroups.SymplecticFour
namespace CFSG.Quasithin.Chapter15.Section03.RankTwo.Parabolics.Selection.LargerFieldBorel

variable {D : Type*} [Group D] [Finite D]

/-- In the actual PSp₄(2ⁿ) model, a solvable Sylow overgroup inside a proper
overgroup of its normalizer normalizes that Sylow subgroup, for n > 1. -/
theorem symplectic_control {n : ℕ} (hn : 1 < n)
    (hmodel : ClassicalGroup.IsPSp D 2 (2 ^ n)) : ParabolicSolvableControl D := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hmodel
  let : CharP F 2 := EvenProjective.charTwo_of_card hF
  have hlarge : 2 < Nat.card F := by
    rw [hF]
    exact (show (2 : ℕ) ^ 1 < 2 ^ n from Nat.pow_lt_pow_right (by decide) hn)
  apply control_of_mulEquiv (e.trans EvenProjective.equiv.symm)
  intro U P H hNP hP hHP hsol hUH
  have hUP : (U : Subgroup (Sp F)) ≤ P :=
    (U : Subgroup (Sp F)).le_normalizer.trans hNP
  obtain ⟨g, hg⟩ :=
    ThreeResidualPlacement.proper_sylow_overgroup_parabolic_cover hlarge U P hUP hP
  apply solvable_conjugate_parabolic_le_normalizer hlarge U H hsol hUH
  exact ⟨g, hg.imp ((map_mono hHP).trans) ((map_mono hHP).trans)⟩

end CFSG.Quasithin.Chapter15.Section03.RankTwo.Parabolics.Selection.LargerFieldBorel
