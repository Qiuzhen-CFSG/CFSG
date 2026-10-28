module

public import Theory.SpecificGroups.PSL3Even.AutomorphismTwoRank.Coverage
public import Theory.SpecificGroups.PSL3Even.AutomorphismTwoRank.Coverage.RootOrientation
public import Theory.SpecificGroups.PSL3Four.CentralCover.ExtendedCentralizer.ResidualAction.ProjectiveFixer.StandardForms

/-!
# Standard forms for the full automorphism group of PSL₃(4)

The proved characteristic-two root orientation discharges the remaining
premise of standard coverage. Specializing to the four-element field gives
linear–field–graph forms for every automorphism of the actual projective
quotient. In particular, this supplies coverage for each marked centralizer.

Source: GLS3, Theorem 2.5.12(a), and the matrix conventions of §2.7,
`refs/KGroup/GLS3/chapter2.tex`. The outer involution types used here are those
in Aschbacher–Smith 16.1.4(4)–(6), printed p.1171.
-/

public section
namespace Matrix.PSL3Four.InnerFamilyNormalizer.QuaternionPlacement
open ExtendedCentralizer.ProjectiveFixer

/-- Every automorphism of the actual PSL₃(4) is standard. -/
theorem standard_eq_top : PSL3.OuterSolvable.standard F = ⊤ := by
  apply PSL3Even.AutomorphismCoverage.standard_eq_top_of_root_orientation
    F (n := 2) (by decide) (by simpa using card_F)
  exact PSL3Even.AutomorphismCoverage.exists_oppositionGraph_preserves_roots_of_charTwo F

/-- Every full automorphism has the explicit matrix, field and graph parameters. -/
theorem exists_standardForm (a : MulAut PSL) : ∃ A σ t, a = standardForm A σ t :=
  ExtendedCentralizer.ProjectiveFixer.exists_standardForm a (by rw [standard_eq_top]; trivial)

/-- Coverage of the full pointwise fixer of the marked E₉, for normalizer consumers. -/
theorem full_fixer_le_standard :
    fixingSubgroup (MulAut PSL) (model : Set PSL) ≤ PSL3.OuterSolvable.standard F := by
  rw [standard_eq_top]
  exact le_top

end Matrix.PSL3Four.InnerFamilyNormalizer.QuaternionPlacement
