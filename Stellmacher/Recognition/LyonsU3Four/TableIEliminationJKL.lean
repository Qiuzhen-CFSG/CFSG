module

public import Stellmacher.Recognition.LyonsU3Four.TableIJArithmetic
public import Stellmacher.Recognition.LyonsU3Four.TableIKArithmetic
public import Stellmacher.Recognition.LyonsU3Four.TableILArithmetic

/-!
# Elimination of Table I cases J, K and L

The three explicit catalogue matrices admit no signed integer degrees satisfying
the degree, positive order, and prime constraints. Signed Galois symmetry first
normalizes the degrees to the printed orbit labels, transporting all three
constraint packages. The matrix equations, signed multiplicity bounds,
congruences, and prime exclusions then give the numerical contradictions.

In K, the equal-degree branch is excluded before the degree-13 prime bound is
used. Thus the identical rows are separated by their degrees, not merely by
their printed labels. L likewise establishes the required degree separation.

Source: R. Lyons, *A Characterization of the Group U₃(4)* (1972), Table I
pp. 375–376 and the elimination pp. 383–384, in
`refs/original/n-group-global/odd-core-rank-two-source/lyons-u3four-1972-ams-wayback.pdf`.
As documented in `TableIMatrices`, J uses the correction `dᵗ = -2` in row 9
required by the Gram identities and the source's derivation on p. 379.
-/

public section
namespace Stellmacher.Recognition.LyonsU3Four

/-- The explicit case J matrix admits no simultaneous degree, order and prime constraints. -/
theorem tableIJ_impossible (degree : Fin (tableIRowCount .J) → ℤ)
    (hd : (tableIData .J ()).DegreeConstraints (tableIPrincipal .J) degree)
    {g c e : ℕ} (ho : (tableIData .J ()).OrderConstraints degree g c e)
    (hp : (tableIData .J ()).PrimeConstraints degree g) : False := by
  obtain ⟨x, hdx, hox, hpx⟩ := EarlyJ.normalize_degree hd ho hp
  exact EarlyJ.impossible_normalized hdx hox hpx

/-- The explicit case K matrix admits no simultaneous degree, order and prime constraints. -/
theorem tableIK_impossible (degree : Fin (tableIRowCount .K) → ℤ)
    (hd : (tableIData .K ()).DegreeConstraints (tableIPrincipal .K) degree)
    {g c e : ℕ} (ho : (tableIData .K ()).OrderConstraints degree g c e)
    (hp : (tableIData .K ()).PrimeConstraints degree g) : False := by
  obtain ⟨x, hdx, hox, hpx⟩ := EarlyK.normalize_degree hd ho hp
  exact EarlyK.impossible_normalized hdx hox hpx

/-- The explicit case L matrix admits no simultaneous degree, order and prime constraints. -/
theorem tableIL_impossible (degree : Fin (tableIRowCount .L) → ℤ)
    (hd : (tableIData .L ()).DegreeConstraints (tableIPrincipal .L) degree)
    {g c e : ℕ} (ho : (tableIData .L ()).OrderConstraints degree g c e)
    (hp : (tableIData .L ()).PrimeConstraints degree g) : False := by
  obtain ⟨x, hdx, hox, hpx⟩ := EarlyL.normalize_degree hd ho hp
  exact EarlyL.impossible_normalized hdx hox hpx

end Stellmacher.Recognition.LyonsU3Four
