module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.MatrixWitness.Products6

/-!
# Symbolic assembly of the six matrix words

The product certificates are assembled with multiplication and power laws.
The resulting expressions have the literal source commutator convention.

Source: the literal ATLAS degree-27 matrices over GF(7) retained in
`CubicExtension/source/`. Generated witnesses are checked by Lean, independently
of the Python generator; see `MatrixWitness/source/README.md`.
-/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.MatrixWitness

open MatrixData

theorem value0 : (matrixA ^ 2) = 1 := by
  calc
    _ = (matrixA ^ 1) * (matrixA ^ 1) := pow_add _ 1 1
    _ = 1 := by
      rw [pow_one]
      exact product0

theorem value1 : (matrixB ^ 2) = inverseB := by
  calc
    _ = (matrixB ^ 1) * (matrixB ^ 1) := pow_add _ 1 1
    _ = inverseB := by
      rw [pow_one]
      exact product1

theorem value2 : (matrixB ^ 3) = 1 := by
  calc
    _ = (matrixB ^ 2) * (matrixB ^ 1) := pow_add _ 2 1
    _ = 1 := by
      rw [pow_one, value1]
      exact product2

theorem value3 : (matrixA * matrixB) = matrix3 := by
  exact product3

theorem value4 : (matrixA * inverseB) = matrix4 := by
  exact product4

theorem value5 : ((matrixA * inverseB) * matrixA) = matrix5 := by
  rw [value4]
  exact product5

theorem value6 : (((matrixA * inverseB) * matrixA) * matrixB) = matrix6 := by
  rw [value5]
  exact product6

theorem value7 : (matrixB * matrixA) = matrix7 := by
  exact product7

theorem value8 : ((matrixB * matrixA) * matrixB) = matrix8 := by
  rw [value7]
  exact product8

theorem value9 : (inverseB * (matrixA * inverseB)) = matrix9 := by
  rw [value4]
  exact product9

theorem value10 : (matrixA * (inverseB * (matrixA * inverseB))) = matrix10 := by
  rw [value9]
  exact product10

theorem value11 : ((matrixA * (inverseB * (matrixA * inverseB))) * matrixA) = matrix11 := by
  rw [value10]
  exact product11

theorem value12 : (((matrixA * (inverseB * (matrixA * inverseB))) * matrixA) * ((matrixB * matrixA) * matrixB)) = matrix12 := by
  rw [value11, value8]
  exact product12

theorem value13 : ((matrixA * matrixB) ^ 2) = matrix13 := by
  calc
    _ = ((matrixA * matrixB) ^ 1) * ((matrixA * matrixB) ^ 1) := pow_add _ 1 1
    _ = matrix13 := by
      rw [pow_one, value3]
      exact product13

theorem value14 : ((matrixA * matrixB) ^ 3) = matrix14 := by
  calc
    _ = ((matrixA * matrixB) ^ 2) * ((matrixA * matrixB) ^ 1) := pow_add _ 2 1
    _ = matrix14 := by
      rw [pow_one, value13, value3]
      exact product14

theorem value15 : ((matrixA * matrixB) ^ 6) = matrix15 := by
  calc
    _ = ((matrixA * matrixB) ^ 3) * ((matrixA * matrixB) ^ 3) := pow_add _ 3 3
    _ = matrix15 := by
      rw [value14]
      exact product15

theorem value16 : ((matrixA * matrixB) ^ 12) = matrix16 := by
  calc
    _ = ((matrixA * matrixB) ^ 6) * ((matrixA * matrixB) ^ 6) := pow_add _ 6 6
    _ = matrix16 := by
      rw [value15]
      exact product16

theorem value17 : ((matrixA * matrixB) ^ 13) = 1 := by
  calc
    _ = ((matrixA * matrixB) ^ 12) * ((matrixA * matrixB) ^ 1) := pow_add _ 12 1
    _ = 1 := by
      rw [pow_one, value16, value3]
      exact product17

theorem value18 : ((((matrixA * inverseB) * matrixA) * matrixB) ^ 2) = matrix18 := by
  calc
    _ = ((((matrixA * inverseB) * matrixA) * matrixB) ^ 1) * ((((matrixA * inverseB) * matrixA) * matrixB) ^ 1) := pow_add _ 1 1
    _ = matrix18 := by
      rw [pow_one, value6]
      exact product18

theorem value19 : ((((matrixA * inverseB) * matrixA) * matrixB) ^ 3) = matrix19 := by
  calc
    _ = ((((matrixA * inverseB) * matrixA) * matrixB) ^ 2) * ((((matrixA * inverseB) * matrixA) * matrixB) ^ 1) := pow_add _ 2 1
    _ = matrix19 := by
      rw [pow_one, value18, value6]
      exact product19

theorem value20 : ((((matrixA * inverseB) * matrixA) * matrixB) ^ 6) = matrix20 := by
  calc
    _ = ((((matrixA * inverseB) * matrixA) * matrixB) ^ 3) * ((((matrixA * inverseB) * matrixA) * matrixB) ^ 3) := pow_add _ 3 3
    _ = matrix20 := by
      rw [value19]
      exact product20

theorem value21 : ((((matrixA * inverseB) * matrixA) * matrixB) ^ 12) = matrix21 := by
  calc
    _ = ((((matrixA * inverseB) * matrixA) * matrixB) ^ 6) * ((((matrixA * inverseB) * matrixA) * matrixB) ^ 6) := pow_add _ 6 6
    _ = matrix21 := by
      rw [value20]
      exact product21

theorem value22 : ((((matrixA * inverseB) * matrixA) * matrixB) ^ 13) = 1 := by
  calc
    _ = ((((matrixA * inverseB) * matrixA) * matrixB) ^ 12) * ((((matrixA * inverseB) * matrixA) * matrixB) ^ 1) := pow_add _ 12 1
    _ = 1 := by
      rw [pow_one, value21, value6]
      exact product22

theorem value23 : ((((matrixA * inverseB) * matrixA) * matrixB) ^ 4) = matrix23 := by
  calc
    _ = ((((matrixA * inverseB) * matrixA) * matrixB) ^ 2) * ((((matrixA * inverseB) * matrixA) * matrixB) ^ 2) := pow_add _ 2 2
    _ = matrix23 := by
      rw [value18]
      exact product23

theorem value24 : (((matrixA * matrixB) ^ 2) * ((((matrixA * inverseB) * matrixA) * matrixB) ^ 4)) = matrix24 := by
  rw [value13, value23]
  exact product24

theorem value25 : ((((matrixA * matrixB) ^ 2) * ((((matrixA * inverseB) * matrixA) * matrixB) ^ 4)) * ((matrixA * matrixB) ^ 3)) = matrix25 := by
  rw [value24, value14]
  exact product25

theorem value26 : ((((matrixA * (inverseB * (matrixA * inverseB))) * matrixA) * ((matrixB * matrixA) * matrixB)) ^ 2) = matrix26 := by
  calc
    _ = ((((matrixA * (inverseB * (matrixA * inverseB))) * matrixA) * ((matrixB * matrixA) * matrixB)) ^ 1) * ((((matrixA * (inverseB * (matrixA * inverseB))) * matrixA) * ((matrixB * matrixA) * matrixB)) ^ 1) := pow_add _ 1 1
    _ = matrix26 := by
      rw [pow_one, value12]
      exact product26

theorem value27 : ((((matrixA * (inverseB * (matrixA * inverseB))) * matrixA) * ((matrixB * matrixA) * matrixB)) ^ 3) = matrix27 := by
  calc
    _ = ((((matrixA * (inverseB * (matrixA * inverseB))) * matrixA) * ((matrixB * matrixA) * matrixB)) ^ 2) * ((((matrixA * (inverseB * (matrixA * inverseB))) * matrixA) * ((matrixB * matrixA) * matrixB)) ^ 1) := pow_add _ 2 1
    _ = matrix27 := by
      rw [pow_one, value26, value12]
      exact product27

theorem value28 : (((((matrixA * matrixB) ^ 2) * ((((matrixA * inverseB) * matrixA) * matrixB) ^ 4)) * ((matrixA * matrixB) ^ 3)) * ((((matrixA * (inverseB * (matrixA * inverseB))) * matrixA) * ((matrixB * matrixA) * matrixB)) ^ 3)) = 1 := by
  rw [value25, value27]
  exact product28

theorem value29 : (((matrixA * matrixB) ^ 3) * (matrixA * inverseB)) = matrix29 := by
  rw [value14, value4]
  exact product29

theorem value30 : ((((matrixA * matrixB) ^ 3) * (matrixA * inverseB)) ^ 2) = matrix30 := by
  calc
    _ = ((((matrixA * matrixB) ^ 3) * (matrixA * inverseB)) ^ 1) * ((((matrixA * matrixB) ^ 3) * (matrixA * inverseB)) ^ 1) := pow_add _ 1 1
    _ = matrix30 := by
      rw [pow_one, value29]
      exact product30

theorem value31 : (((((matrixA * matrixB) ^ 3) * (matrixA * inverseB)) ^ 2) * ((matrixA * matrixB) ^ 2)) = matrix31 := by
  rw [value30, value13]
  exact product31

theorem value32 : ((matrixA * inverseB) ^ 2) = matrix32 := by
  calc
    _ = ((matrixA * inverseB) ^ 1) * ((matrixA * inverseB) ^ 1) := pow_add _ 1 1
    _ = matrix32 := by
      rw [pow_one, value4]
      exact product32

theorem value33 : ((((((matrixA * matrixB) ^ 3) * (matrixA * inverseB)) ^ 2) * ((matrixA * matrixB) ^ 2)) * ((matrixA * inverseB) ^ 2)) = matrix33 := by
  rw [value31, value32]
  exact product33

theorem value34 : (((((((matrixA * matrixB) ^ 3) * (matrixA * inverseB)) ^ 2) * ((matrixA * matrixB) ^ 2)) * ((matrixA * inverseB) ^ 2)) ^ 2) = scalarMatrix := by
  calc
    _ = (((((((matrixA * matrixB) ^ 3) * (matrixA * inverseB)) ^ 2) * ((matrixA * matrixB) ^ 2)) * ((matrixA * inverseB) ^ 2)) ^ 1) * (((((((matrixA * matrixB) ^ 3) * (matrixA * inverseB)) ^ 2) * ((matrixA * matrixB) ^ 2)) * ((matrixA * inverseB) ^ 2)) ^ 1) := pow_add _ 1 1
    _ = scalarMatrix := by
      rw [pow_one, value33]
      exact product34


end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.MatrixWitness
