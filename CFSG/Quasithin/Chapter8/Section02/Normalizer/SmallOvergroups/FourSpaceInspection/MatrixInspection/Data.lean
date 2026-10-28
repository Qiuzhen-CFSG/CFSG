module

public import CFSG.Quasithin.Chapter8.Section02.Normalizer.SmallOvergroups.FourSpaceInspection.MatrixInspection.Raw
public import Mathlib.GroupTheory.Perm.Sign

/-!
# Fourteen candidate double cosets and their cubic words

These four-column matrices and words were found by exhaustive search in the
first four coordinates of the even-weight core. Bit positions increase from
low to high. Word letters are (012), (234), the representative, followed by
their inverses, and words multiply from left to right. `Certificates` checks
the word and cubic identities. `DoubleCosetCoverage` is the separate exhaustive
coverage obligation; listing the representatives does not prove it.

Source: Aschbacher–Smith, proof of 8.2.8(1), printed p.719/PDF p.736.
Search data: parent task's Scratch/FourSpaceInspection/certificates.json.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter8.Section02.Normalizer.SmallOvergroups.FourSpaceInspection.MatrixInspection

def cycleA : Equiv.Perm (Fin 5) := Equiv.swap 0 2 * Equiv.swap 0 1
def cycleB : Equiv.Perm (Fin 5) := Equiv.swap 2 4 * Equiv.swap 2 3

def representative : Fin 14 → Columns :=
  ![![1, 2, 4, 9],
    ![1, 2, 4, 15],
    ![1, 2, 5, 9],
    ![1, 2, 5, 10],
    ![1, 2, 5, 11],
    ![1, 2, 5, 12],
    ![1, 2, 5, 13],
    ![1, 2, 5, 14],
    ![1, 2, 5, 15],
    ![1, 2, 8, 15],
    ![1, 6, 11, 14],
    ![1, 6, 11, 15],
    ![1, 6, 14, 11],
    ![1, 6, 14, 13]]

def representativeInverse : Fin 14 → Columns :=
  ![![1, 2, 4, 9],
    ![1, 2, 4, 15],
    ![1, 2, 5, 9],
    ![1, 2, 5, 10],
    ![1, 2, 5, 11],
    ![1, 2, 5, 13],
    ![1, 2, 5, 12],
    ![1, 2, 5, 15],
    ![1, 2, 5, 14],
    ![1, 2, 15, 4],
    ![1, 15, 13, 10],
    ![1, 14, 12, 11],
    ![1, 15, 13, 6],
    ![1, 13, 15, 6]]

def witnessColumns : Fin 14 → Columns :=
  ![![13, 11, 14, 15],
    ![14, 13, 11, 15],
    ![14, 13, 11, 15],
    ![10, 12, 9, 7],
    ![10, 12, 9, 7],
    ![13, 11, 14, 15],
    ![13, 11, 14, 15],
    ![13, 11, 14, 15],
    ![13, 11, 14, 15],
    ![9, 10, 12, 7],
    ![14, 13, 11, 15],
    ![10, 12, 9, 7],
    ![12, 9, 10, 7],
    ![12, 9, 10, 7]]

def witnessWord : Fin 14 → List (Fin 6) :=
  ![[2, 1, 0, 2, 4, 2, 3, 2, 1],
    [1, 2, 4, 2],
    [2, 1, 0, 2, 0, 4, 0, 2, 1],
    [1, 0, 2, 0, 2, 3, 2],
    [1, 0, 2, 0, 2, 3, 2],
    [1, 0, 2, 4, 3, 2, 1, 2],
    [1, 0, 5, 4, 3, 4, 2, 4],
    [1, 5, 4, 0, 2, 2],
    [1, 2, 4, 0, 2, 2],
    [4, 2],
    [2, 2, 1, 3, 1, 2, 2, 2],
    [1, 5, 0, 5, 0, 2],
    [1, 5, 0, 5, 5, 1],
    [2, 0, 5, 3, 2, 0, 5]]

def generator (i : Fin 14) : Fin 6 → Function.End Bits :=
  ![permuteBits cycleA, permuteBits cycleB, applyMatrix (representative i),
    permuteBits cycleA⁻¹, permuteBits cycleB⁻¹, applyMatrix (representativeInverse i)]

def evaluateWord (i : Fin 14) (w : List (Fin 6)) : Function.End Bits :=
  (w.map (generator i)).prod

/-- Exhaustive coverage obligation, in the four columns used by the search.
The two permutations in a double coset must both be even. -/
def DoubleCosetCoverage : Prop :=
  ∀ c : Columns, Function.Injective (applyMatrix c) →
    (∃ σ : Equiv.Perm (Fin 5), applyMatrix c = permuteBits σ) ∨
    ∃ (i : Fin 14) (σ τ : Equiv.Perm (Fin 5)),
      Equiv.Perm.sign σ = 1 ∧ Equiv.Perm.sign τ = 1 ∧
      applyMatrix c = permuteBits σ * applyMatrix (representative i) * permuteBits τ

/-- Two independent commuting elements of order three, as finite functions. -/
def CubicPair (a b : Function.End Bits) : Prop :=
  a ^ 3 = 1 ∧ b ^ 3 = 1 ∧ a * b = b * a ∧
    a ≠ 1 ∧ b ≠ 1 ∧ b ≠ a ∧ b ≠ a ^ 2

end CFSG.Quasithin.Chapter8.Section02.Normalizer.SmallOvergroups.FourSpaceInspection.MatrixInspection
