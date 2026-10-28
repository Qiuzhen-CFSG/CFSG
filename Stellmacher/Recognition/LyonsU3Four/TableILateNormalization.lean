module
public import Stellmacher.Recognition.LyonsU3Four.TableILateMatrices
public import Stellmacher.Recognition.LyonsU3Four.TableIGaloisNormalization

/-!
# Repeated degree labels in the late cases of Table I

The explicit M, N, P, Q, R, S and T matrices have positive z-values. Their
Galois signs are therefore positive. Each certificate below records a column
rotation from the printed representative and checks that equal rows have the
same rotation step. The general Galois alignment theorem then supplies a
permutation of equal matrix rows on which the printed degree labels are valid.
This preserves all three degree, order and prime constraint packages, including
row separation and the absolute degrees used in the prime bounds.

These results concern an explicitly identified matrix. They do not assert
exhaustive classification or identify the matrix of a `TableIPatternWitness`
from its case tag.
Source: R. Lyons, *A Characterization of the Group U₃(4)*, Trans. Amer. Math.
Soc. 164 (1972), §3 and Table I, pp. 375–377. Local source:
`refs/original/n-group-global/odd-core-rank-two-source/lyons-u3four-1972-ams-wayback.pdf`.
-/

@[expose] public section
namespace Stellmacher.Recognition.LyonsU3Four
open GeneralizedDecompositionData

namespace LateM

/-- The printed labels and their Galois rotation steps, retaining repeated rows. -/
def galoisLabeling : data.GaloisLabeling 0 (Fin 9) where
  label := label
  representative := representative
  step := ![0, 0, 3, 2, 1, 0, 3, 2, 1, 0, 3, 2, 1, 0, 1, 2, 3, 0, 0, 0, 0]
  row_eq := by decide
  step_eq := by decide
  coordinates_injective := by decide
  principal_step := rfl
  principal_representative := rfl

/-- Arbitrary admissible degrees can be aligned with the printed labels. -/
theorem normalize_degree {r : Fin 21 → ℤ} {g c e : ℕ}
    (hd : data.DegreeConstraints 0 r)
    (ho : data.OrderConstraints r g c e)
    (hp : data.PrimeConstraints r g) :
    ∃ x : Fin 9 → ℤ, data.DegreeConstraints 0 (degree x) ∧
      data.OrderConstraints (degree x) g c e ∧
      data.PrimeConstraints (degree x) g := by
  exact galoisLabeling.normalize (by decide) hd ho hp

end LateM

namespace LateN

/-- The printed labels and their Galois rotation steps, retaining repeated rows. -/
def galoisLabeling : data.GaloisLabeling 0 (Fin 9) where
  label := label
  representative := representative
  step := ![0, 0, 3, 2, 1, 0, 3, 2, 1, 0, 1, 2, 3, 0, 1, 2, 3, 0, 0, 0, 0]
  row_eq := by decide
  step_eq := by decide
  coordinates_injective := by decide
  principal_step := rfl
  principal_representative := rfl

/-- Arbitrary admissible degrees can be aligned with the printed labels. -/
theorem normalize_degree {r : Fin 21 → ℤ} {g c e : ℕ}
    (hd : data.DegreeConstraints 0 r)
    (ho : data.OrderConstraints r g c e)
    (hp : data.PrimeConstraints r g) :
    ∃ x : Fin 9 → ℤ, data.DegreeConstraints 0 (degree x) ∧
      data.OrderConstraints (degree x) g c e ∧
      data.PrimeConstraints (degree x) g := by
  exact galoisLabeling.normalize (by decide) hd ho hp

end LateN

namespace LateP

/-- The printed labels and their Galois rotation steps, retaining repeated rows. -/
def galoisLabeling : data.GaloisLabeling 0 (Fin 11) where
  label := label
  representative := representative
  step := ![0, 0, 3, 2, 1, 0, 3, 2, 1, 0, 1, 2, 3, 0, 1, 2, 3, 0, 0, 0, 0, 0, 0]
  row_eq := by decide
  step_eq := by decide
  coordinates_injective := by decide
  principal_step := rfl
  principal_representative := rfl

/-- Arbitrary admissible degrees can be aligned with the printed labels. -/
theorem normalize_degree {r : Fin 23 → ℤ} {g c e : ℕ}
    (hd : data.DegreeConstraints 0 r)
    (ho : data.OrderConstraints r g c e)
    (hp : data.PrimeConstraints r g) :
    ∃ x : Fin 11 → ℤ, data.DegreeConstraints 0 (degree x) ∧
      data.OrderConstraints (degree x) g c e ∧
      data.PrimeConstraints (degree x) g := by
  exact galoisLabeling.normalize (by decide) hd ho hp

end LateP

namespace LateQ

/-- The printed labels and their Galois rotation steps, retaining repeated rows. -/
def galoisLabeling : data.GaloisLabeling 0 (Fin 9) where
  label := label
  representative := representative
  step := ![0, 0, 3, 2, 1, 0, 1, 2, 3, 0, 1, 2, 3, 0, 1, 2, 3, 0, 0, 0, 0]
  row_eq := by decide
  step_eq := by decide
  coordinates_injective := by decide
  principal_step := rfl
  principal_representative := rfl

/-- Arbitrary admissible degrees can be aligned with the printed labels. -/
theorem normalize_degree {r : Fin 21 → ℤ} {g c e : ℕ}
    (hd : data.DegreeConstraints 0 r)
    (ho : data.OrderConstraints r g c e)
    (hp : data.PrimeConstraints r g) :
    ∃ x : Fin 9 → ℤ, data.DegreeConstraints 0 (degree x) ∧
      data.OrderConstraints (degree x) g c e ∧
      data.PrimeConstraints (degree x) g := by
  exact galoisLabeling.normalize (by decide) hd ho hp

end LateQ

namespace LateR

/-- The printed labels and their Galois rotation steps, retaining repeated rows. -/
def galoisLabeling : data.GaloisLabeling 0 (Fin 11) where
  label := label
  representative := representative
  step := ![0, 0, 3, 2, 1, 0, 1, 2, 3, 0, 1, 2, 3, 0, 1, 2, 3, 0, 0, 0, 0, 0, 0]
  row_eq := by decide
  step_eq := by decide
  coordinates_injective := by decide
  principal_step := rfl
  principal_representative := rfl

/-- Arbitrary admissible degrees can be aligned with the printed labels. -/
theorem normalize_degree {r : Fin 23 → ℤ} {g c e : ℕ}
    (hd : data.DegreeConstraints 0 r)
    (ho : data.OrderConstraints r g c e)
    (hp : data.PrimeConstraints r g) :
    ∃ x : Fin 11 → ℤ, data.DegreeConstraints 0 (degree x) ∧
      data.OrderConstraints (degree x) g c e ∧
      data.PrimeConstraints (degree x) g := by
  exact galoisLabeling.normalize (by decide) hd ho hp

end LateR

namespace LateS

/-- The printed labels and their Galois rotation steps, retaining repeated rows. -/
def galoisLabeling : data.GaloisLabeling 0 (Fin 9) where
  label := label
  representative := representative
  step := ![0, 0, 1, 2, 3, 0, 1, 2, 3, 0, 1, 2, 3, 0, 1, 0, 0, 0, 0]
  row_eq := by decide
  step_eq := by decide
  coordinates_injective := by decide
  principal_step := rfl
  principal_representative := rfl

/-- Arbitrary admissible degrees can be aligned with the printed labels. -/
theorem normalize_degree {r : Fin 19 → ℤ} {g c e : ℕ}
    (hd : data.DegreeConstraints 0 r)
    (ho : data.OrderConstraints r g c e)
    (hp : data.PrimeConstraints r g) :
    ∃ x : Fin 9 → ℤ, data.DegreeConstraints 0 (degree x) ∧
      data.OrderConstraints (degree x) g c e ∧
      data.PrimeConstraints (degree x) g := by
  exact galoisLabeling.normalize (by decide) hd ho hp

end LateS

namespace LateT

/-- The printed labels and their Galois rotation steps, retaining repeated rows. -/
def galoisLabeling : data.GaloisLabeling 0 (Fin 7) where
  label := label
  representative := representative
  step := ![0, 0, 1, 2, 3, 0, 1, 2, 3, 0, 3, 2, 1, 0, 1, 0, 0]
  row_eq := by decide
  step_eq := by decide
  coordinates_injective := by decide
  principal_step := rfl
  principal_representative := rfl

/-- Arbitrary admissible degrees can be aligned with the printed labels. -/
theorem normalize_degree {r : Fin 17 → ℤ} {g c e : ℕ}
    (hd : data.DegreeConstraints 0 r)
    (ho : data.OrderConstraints r g c e)
    (hp : data.PrimeConstraints r g) :
    ∃ x : Fin 7 → ℤ, data.DegreeConstraints 0 (degree x) ∧
      data.OrderConstraints (degree x) g c e ∧
      data.PrimeConstraints (degree x) g := by
  exact galoisLabeling.normalize (by decide) hd ho hp

end LateT

end Stellmacher.Recognition.LyonsU3Four
