module

public import Stellmacher.Recognition.LyonsU3Four.TableIJKLSystems
public import Stellmacher.Recognition.LyonsU3Four.TableIADGArithmetic

/-!
# Degree separation in Table I case K

The two identical two-row orbits cannot have equal degrees. If their common
degree were -13, orthogonality would force degree 26 on the row whose signed
multiplicity requires a positive degree of at least 90. The remaining
equal-degree system is the already proved A/D/G arithmetic contradiction.
Thus Schur's degree-13 bound applies after genuine degree separation.

Source: R. Lyons, *A Characterization of the Group U₃(4)* (1972), case K,
pp. 383–384; the matrix and signed multiplicity are those of Table I.
-/

public section
namespace Stellmacher.Recognition.LyonsU3Four.EarlyK

/-- The equal-degree branch is impossible before any prime bound is used. -/
theorem degrees_ne {x : Fin 8 → ℤ} {g c e : ℕ}
    (hd : data.DegreeConstraints 0 (degree x))
    (ho : data.OrderConstraints (degree x) g c e) : x 2 ≠ x 3 := by
  intro he
  have eqs := equations hd ho
  have hx := degree_bounds hd 2 (by decide)
  have hu := degree_bounds hd 6 (by decide)
  have hv := degree_bounds hd 7 (by decide)
  have hz := degree_bounds hd 5 (by decide)
  have hmX := degree_mod hd 2
  have hmZ := degree_mod hd 5
  change x 2 ≤ -13 ∨ 51 ≤ x 2 at hx
  change x 6 ≤ -63 ∨ 65 ≤ x 6 at hu
  change x 7 ≤ -63 ∨ 65 ≤ x 7 at hv
  change x 5 ≤ -87 ∨ 41 ≤ x 5 at hz
  change (x 2 + -51) % 64 = 0 at hmX
  change (x 5 + 87) % 64 = 0 at hmZ
  have hsmall : x 2 = -13 → x 5 < 0 → x 5 ≤ -343 := by
    intro hh _
    have hs := degree_bounds hd 4 (by decide)
    change x 4 ≤ -38 ∨ 90 ≤ x 4 at hs
    have hsum := eqs.orbit_sum
    omega
  apply tableI_ADG_arithmetic (x 2) (x 6) (x 7) (x 5) hx hu hv hz
    (by omega) (by omega) hsmall
  · have hh := eqs.h₁
    rw [← he] at hh
    linear_combination hh
  · have hh := eqs.h₂
    omega

/-- The first repeated row is separated by its degree under the actual constraints. -/
theorem row_separated_two_of_constraints {x : Fin 8 → ℤ} {g c e : ℕ}
    (hd : data.DegreeConstraints 0 (degree x))
    (ho : data.OrderConstraints (degree x) g c e) :
    data.RowSeparated (degree x) 5 := row_separated_two (degrees_ne hd ho)

/-- The second repeated row is also separated by its degree. -/
theorem row_separated_three_of_constraints {x : Fin 8 → ℤ} {g c e : ℕ}
    (hd : data.DegreeConstraints 0 (degree x))
    (ho : data.OrderConstraints (degree x) g c e) :
    data.RowSeparated (degree x) 7 := row_separated_three (degrees_ne hd ho)

end Stellmacher.Recognition.LyonsU3Four.EarlyK
