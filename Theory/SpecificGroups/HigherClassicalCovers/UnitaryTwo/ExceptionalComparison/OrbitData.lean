module

public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryTwo.ExceptionalComparison.Relations

/-!
# A finite orbit certificate for the symplectic generators

The orbit tree lists all eighty nonzero vectors of the actual ternary
four-space. Each edge is an application of one of the two checked symplectic
matrices. The seed word is `(a⁻¹ b⁻¹)³`, a transvection.
`Generation` checks this data and propagates transvection membership along
the tree. The untrusted producer is `source/generate_orbit.py`.
-/

@[expose] public section
namespace Theory.SpecificGroups.HigherClassicalCovers.UnitaryTwo.ExceptionalComparison

def orbitCode : Fin 80 → ℕ :=
  ![65, 79, 64, 17, 61, 77, 46, 1, 24, 56, 35, 58, 41, 47, 18, 26, 15, 69, 73, 66, 31, 51, 62, 22, 32, 43, 20, 9, 29, 19, 37, 16, 57, 71, 68, 54, 21, 27, 2, 12, 28, 10, 39, 34, 11, 8, 14, 33, 63, 25, 70, 52, 67, 60, 74, 30, 48, 13, 38, 42, 75, 44, 4, 36, 7, 45, 5, 53, 80, 6, 55, 3, 23, 49, 72, 76, 40, 50, 59, 78]

def orbitParent : Fin 80 → Fin 80 :=
  ![0, 0, 0, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 6, 7, 7, 8, 9, 9, 10, 10, 11, 11, 12, 13, 13, 14, 14, 15, 15, 16, 17, 17, 18, 18, 19, 20, 21, 23, 24, 24, 27, 28, 28, 29, 29, 31, 32, 32, 33, 33, 34, 34, 35, 36, 37, 37, 38, 40, 42, 43, 43, 44, 45, 46, 47, 49, 51, 52, 53, 54, 55, 56, 58, 60, 61, 63, 65, 67, 70]

def orbitEdge : Fin 80 → Fin 2 :=
  ![0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0]

def orbitVector (i : Fin 80) : Matrix.PSp4Three.Vector 2 (ZMod 3) :=
  fun j => (orbitCode i / 3 ^ (symplecticCoordinate j).val % 3 : ℕ)

def seedWord : List (Fin 2 × Bool) :=
  [(0,false),(1,false),(0,false),(1,false),(0,false),(1,false)]

def seedPrefixCode : Fin 7 → ℕ :=
  ![14408200, 1605520, 31370770, 34621610, 25469573, 7016367, 26736339]

def seedPrefix (k : ℕ) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 3) :=
  fun i j => (seedPrefixCode (Fin.ofNat 7 k) /
    3 ^ (4*(symplecticCoordinate i).val+(symplecticCoordinate j).val) % 3 : ℕ)

end Theory.SpecificGroups.HigherClassicalCovers.UnitaryTwo.ExceptionalComparison
