module

public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryTwo.Model
public import Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime.Basic


/-!
# Matched matrix generators for the unitary–symplectic comparison

These are two determinant-one isometries of the identity Hermitian form over
`GoldenFour`, and two isometries of Mathlib's literal four-dimensional
symplectic form over `ZMod 3`. Every membership assertion is kernel checked.
The symplectic coordinates are ordered `(e₀,e₁,f₀,f₁)`.

The matrices were found by the untrusted GAP script in `source/discover.g`.
They supply candidate maps for the exceptional comparison
PSU₄(2) ≅ PSp₄(3), used in Aschbacher–Smith I.1.4(1), printed p.408
(`refs/quasithin.pdf`); see also GLS3 §2.2's table of exceptional isomorphisms
and §2.7. No generation or presentation-exactness claim is made here.
-/

open Matrix Atlas.Algebra
open Theory.SpecificGroups.HigherClassicalCovers.UnitaryTwo
@[expose] public section
namespace Theory.SpecificGroups.HigherClassicalCovers.UnitaryTwo.ExceptionalComparison
abbrev F := GoldenFour
def omega : F := ⟨0,1⟩
def unitaryMatrix : Fin 2 → Matrix (Fin 4) (Fin 4) F :=
  ![!![omega,0,0,0; 0,omega^2,0,0; 0,0,omega^2,0; 0,0,0,omega],
    !![omega^2,0,omega^2,omega^2; 1,1,1,0; 0,1,1,1; omega,omega,0,omega]]
theorem unitaryMatrix_checked : ∀ i, star (unitaryMatrix i) * unitaryMatrix i = 1 ∧ unitaryMatrix i * star (unitaryMatrix i) = 1 ∧ (unitaryMatrix i).det = 1 := by
  decide +kernel
def unitaryGenerator (i : Fin 2) : StandardSU :=
  ⟨⟨unitaryMatrix i, star (unitaryMatrix i), (unitaryMatrix_checked i).2.1, (unitaryMatrix_checked i).1⟩, by
    refine (standardForm.mem_specialSubgroup_iff _).mpr ⟨?_, ?_⟩
    · change star (unitaryMatrix i) * 1 * unitaryMatrix i = 1
      simpa using (unitaryMatrix_checked i).1
    · apply Units.ext
      exact (unitaryMatrix_checked i).2.2⟩

def symplecticCoordinate : Fin 2 ⊕ Fin 2 → Fin 4
  | .inl i => i.castAdd 2
  | .inr i => i.natAdd 2

def symplecticFinMatrix : Fin 2 → Matrix (Fin 4) (Fin 4) (ZMod 3) :=
  ![!![0,0,1,0; 0,0,0,1; 2,0,1,0; 0,2,0,1],
    !![2,0,0,0; 2,1,0,1; 2,0,2,2; 0,0,0,1]]
def symplecticMatrix (i : Fin 2) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 3) :=
  (symplecticFinMatrix i).submatrix symplecticCoordinate symplecticCoordinate

theorem symplecticMatrix_checked : ∀ i, symplecticMatrix i * Matrix.J (Fin 2) (ZMod 3) * (symplecticMatrix i)ᵀ = Matrix.J (Fin 2) (ZMod 3) := by
  decide +kernel

def symplecticGenerator (i : Fin 2) : Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime.Sp (ZMod 3) :=
  ⟨symplecticMatrix i, SymplecticGroup.mem_iff.mpr (symplecticMatrix_checked i)⟩
end Theory.SpecificGroups.HigherClassicalCovers.UnitaryTwo.ExceptionalComparison
