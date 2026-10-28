module

public import Theory.Representation.QuadraticFourGroup.CubicSections.FactorInvolutions.Matrix
public import Theory.Representation.QuadraticFourGroup.CubicSections.SplitSection

/-!
# Cubic inverters in the concrete factors

The actual factor `PSL(2, GaloisField 2 n)` has the inverters required by
GLS, volume 2, Theorem 25.14, Step 4 (`refs/KGroup/GLS2/ChapterG.tex`,
lines 888–894). The matrix construction applies to every element, hence
in particular to elements of order three. The theorem retains the source
parameter restriction `1 < n`.
-/

public section

namespace Representation.QuadraticFourGroup

/-- The concrete PSL₂ factors supply the cubic inversion relations in Step 4. -/
theorem factor_hasCubicInverters (n : ℕ) (_hn : 1 < n) : HasCubicInverters (Factor n) := by
  intro x _hx
  exact Matrix.ProjectiveSpecialLinearGroup.exists_inverter_sq_eq_one_of_charTwo x

end Representation.QuadraticFourGroup

end
