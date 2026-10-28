module

public import Theory.SpecificGroups.HaradaNorton.MatrixData

/-!
# A cyclic row for the fixed HN representation

Every standard basis row is obtained from row zero by multiplying by the two
ATLAS matrices. For each nonzero row index, the certificate gives a strictly
smaller parent index and a generator whose parent row is that standard basis
row. Kernel reduction verifies the certificate against the original matrices.
Strong induction then proves that a matrix commuting with both generators is
determined by its zeroth row.

Source: the original ATLAS matrices, `../../MatrixSources.md`.
`GenerateCyclicRows.py` selects the witnesses; its computations are not trusted.
-/

namespace HaradaNorton

set_option maxRecDepth 10000

private def rowParent (i : Fin 133) : Fin 133 :=
  (if i.val < 66 then (if i.val < 33 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 1 else 1)) else (if i.val < 6 then (if i.val < 5 then 2 else 3) else (if i.val < 7 then 4 else 4))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 5 else 6) else (if i.val < 11 then 7 else 8)) else (if i.val < 14 then (if i.val < 13 then 8 else 9) else (if i.val < 15 then 9 else 10)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 11 else 12) else (if i.val < 19 then 13 else 14)) else (if i.val < 22 then (if i.val < 21 then 15 else 15) else (if i.val < 23 then 16 else 16))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 17 else 18) else (if i.val < 27 then 18 else 19)) else (if i.val < 30 then (if i.val < 29 then 20 else 21) else (if i.val < 31 then 22 else (if i.val < 32 then 23 else 24)))))) else (if i.val < 49 then (if i.val < 41 then (if i.val < 37 then (if i.val < 35 then (if i.val < 34 then 24 else 25) else (if i.val < 36 then 26 else 27)) else (if i.val < 39 then (if i.val < 38 then 27 else 28) else (if i.val < 40 then 28 else 30))) else (if i.val < 45 then (if i.val < 43 then (if i.val < 42 then 30 else 31) else (if i.val < 44 then 32 else 33)) else (if i.val < 47 then (if i.val < 46 then 34 else 34) else (if i.val < 48 then 35 else 36)))) else (if i.val < 57 then (if i.val < 53 then (if i.val < 51 then (if i.val < 50 then 37 else 38) else (if i.val < 52 then 39 else 40)) else (if i.val < 55 then (if i.val < 54 then 41 else 42) else (if i.val < 56 then 42 else 43))) else (if i.val < 61 then (if i.val < 59 then (if i.val < 58 then 43 else 44) else (if i.val < 60 then 45 else 46)) else (if i.val < 63 then (if i.val < 62 then 47 else 47) else (if i.val < 64 then 48 else (if i.val < 65 then 48 else 49))))))) else (if i.val < 99 then (if i.val < 82 then (if i.val < 74 then (if i.val < 70 then (if i.val < 68 then (if i.val < 67 then 50 else 50) else (if i.val < 69 then 51 else 52)) else (if i.val < 72 then (if i.val < 71 then 52 else 53) else (if i.val < 73 then 54 else 55))) else (if i.val < 78 then (if i.val < 76 then (if i.val < 75 then 56 else 57) else (if i.val < 77 then 58 else 58)) else (if i.val < 80 then (if i.val < 79 then 59 else 59) else (if i.val < 81 then 60 else 61)))) else (if i.val < 90 then (if i.val < 86 then (if i.val < 84 then (if i.val < 83 then 63 else 64) else (if i.val < 85 then 65 else 65)) else (if i.val < 88 then (if i.val < 87 then 66 else 67) else (if i.val < 89 then 70 else 71))) else (if i.val < 94 then (if i.val < 92 then (if i.val < 91 then 71 else 72) else (if i.val < 93 then 72 else 73)) else (if i.val < 96 then (if i.val < 95 then 74 else 74) else (if i.val < 97 then 75 else (if i.val < 98 then 76 else 77)))))) else (if i.val < 116 then (if i.val < 107 then (if i.val < 103 then (if i.val < 101 then (if i.val < 100 then 78 else 79) else (if i.val < 102 then 80 else 80)) else (if i.val < 105 then (if i.val < 104 then 81 else 82) else (if i.val < 106 then 82 else 83))) else (if i.val < 111 then (if i.val < 109 then (if i.val < 108 then 84 else 85) else (if i.val < 110 then 86 else 86)) else (if i.val < 113 then (if i.val < 112 then 88 else 89) else (if i.val < 114 then 90 else (if i.val < 115 then 91 else 93))))) else (if i.val < 124 then (if i.val < 120 then (if i.val < 118 then (if i.val < 117 then 93 else 94) else (if i.val < 119 then 95 else 96)) else (if i.val < 122 then (if i.val < 121 then 97 else 97) else (if i.val < 123 then 98 else 99))) else (if i.val < 128 then (if i.val < 126 then (if i.val < 125 then 99 else 100) else (if i.val < 127 then 101 else 102)) else (if i.val < 130 then (if i.val < 129 then 103 else 104) else (if i.val < 131 then 106 else (if i.val < 132 then 107 else 107))))))))

private def rowUsesA (i : Fin 133) : Bool :=
  (if i.val < 66 then (if i.val < 33 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then false else false) else (if i.val < 3 then true else false)) else (if i.val < 6 then (if i.val < 5 then false else true) else (if i.val < 7 then true else false))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then false else false) else (if i.val < 11 then true else true)) else (if i.val < 14 then (if i.val < 13 then false else true) else (if i.val < 15 then false else false)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then false else true) else (if i.val < 19 then false else true)) else (if i.val < 22 then (if i.val < 21 then true else false) else (if i.val < 23 then true else false))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then false else true) else (if i.val < 27 then false else false)) else (if i.val < 30 then (if i.val < 29 then false else true) else (if i.val < 31 then false else (if i.val < 32 then true else true)))))) else (if i.val < 49 then (if i.val < 41 then (if i.val < 37 then (if i.val < 35 then (if i.val < 34 then false else false) else (if i.val < 36 then true else true)) else (if i.val < 39 then (if i.val < 38 then false else true) else (if i.val < 40 then false else true))) else (if i.val < 45 then (if i.val < 43 then (if i.val < 42 then false else false) else (if i.val < 44 then false else true)) else (if i.val < 47 then (if i.val < 46 then true else false) else (if i.val < 48 then false else false)))) else (if i.val < 57 then (if i.val < 53 then (if i.val < 51 then (if i.val < 50 then true else false) else (if i.val < 52 then true else false)) else (if i.val < 55 then (if i.val < 54 then true else true) else (if i.val < 56 then false else true))) else (if i.val < 61 then (if i.val < 59 then (if i.val < 58 then false else false) else (if i.val < 60 then false else true)) else (if i.val < 63 then (if i.val < 62 then true else false) else (if i.val < 64 then true else (if i.val < 65 then false else false))))))) else (if i.val < 99 then (if i.val < 82 then (if i.val < 74 then (if i.val < 70 then (if i.val < 68 then (if i.val < 67 then true else false) else (if i.val < 69 then false else true)) else (if i.val < 72 then (if i.val < 71 then false else false) else (if i.val < 73 then false else true))) else (if i.val < 78 then (if i.val < 76 then (if i.val < 75 then false else true) else (if i.val < 77 then true else false)) else (if i.val < 80 then (if i.val < 79 then true else false) else (if i.val < 81 then false else false)))) else (if i.val < 90 then (if i.val < 86 then (if i.val < 84 then (if i.val < 83 then false else true) else (if i.val < 85 then true else false)) else (if i.val < 88 then (if i.val < 87 then false else true) else (if i.val < 89 then true else true))) else (if i.val < 94 then (if i.val < 92 then (if i.val < 91 then false else true) else (if i.val < 93 then false else false)) else (if i.val < 96 then (if i.val < 95 then true else false) else (if i.val < 97 then false else (if i.val < 98 then false else true)))))) else (if i.val < 116 then (if i.val < 107 then (if i.val < 103 then (if i.val < 101 then (if i.val < 100 then false else true) else (if i.val < 102 then true else false)) else (if i.val < 105 then (if i.val < 104 then true else true) else (if i.val < 106 then false else false))) else (if i.val < 111 then (if i.val < 109 then (if i.val < 108 then false else true) else (if i.val < 110 then true else false)) else (if i.val < 113 then (if i.val < 112 then false else false) else (if i.val < 114 then true else (if i.val < 115 then false else true))))) else (if i.val < 124 then (if i.val < 120 then (if i.val < 118 then (if i.val < 117 then false else false) else (if i.val < 119 then true else false)) else (if i.val < 122 then (if i.val < 121 then true else false) else (if i.val < 123 then false else true))) else (if i.val < 128 then (if i.val < 126 then (if i.val < 125 then false else false) else (if i.val < 127 then false else true)) else (if i.val < 130 then (if i.val < 129 then false else false) else (if i.val < 131 then false else (if i.val < 132 then true else false))))))))

private instance finAllDecidable (P : Fin 133 → Prop) [DecidablePred P] :
    Decidable (∀ i, P i) := @Nat.decidableForallFin 133 P inferInstance

set_option maxHeartbeats 0 in
private theorem rowParent_spec : ∀ i : Fin 133, i ≠ 0 →
    rowParent i < i ∧ ∀ j : Fin 133,
      (if rowUsesA i then aMatrix else bMatrix) (rowParent i) j =
        if j = i then 1 else 0 := by decide +kernel

/-- Each nonzero basis row has a smaller-index predecessor under a generator. -/
public theorem basisRow_predecessor (i : Fin 133) (hi : i ≠ 0) :
    ∃ p : Fin 133, p < i ∧
      ((∀ j, aMatrix p j = if j = i then 1 else 0) ∨
        (∀ j, bMatrix p j = if j = i then 1 else 0)) := by
  obtain ⟨hp, hrow⟩ := rowParent_spec i hi
  refine ⟨rowParent i, hp, ?_⟩
  cases h : rowUsesA i
  · exact Or.inr (by simpa only [h, Bool.false_eq_true, ↓reduceIte] using hrow)
  · exact Or.inl (by simpa only [h, ↓reduceIte] using hrow)

private theorem row_step (G M N : Matrix133)
    (hM : M * G = G * M) (hN : N * G = G * N)
    (p i : Fin 133) (hG : ∀ j, G p j = if j = i then 1 else 0)
    (hrow : ∀ j, M p j = N p j) (j : Fin 133) : M i j = N i j := by
  calc
    M i j = (G * M) p j := by simp [Matrix.mul_apply, hG]
    _ = (M * G) p j := congrArg (fun T : Matrix133 => T p j) hM.symm
    _ = (N * G) p j := by simp only [Matrix.mul_apply, hrow]
    _ = (G * N) p j := congrArg (fun T : Matrix133 => T p j) hN
    _ = N i j := by simp [Matrix.mul_apply, hG]

/-- The zeroth row determines any matrix in the joint generator commutant. -/
public theorem commuting_matrix_ext_row_zero
    (M N : Matrix133) (haM : M * aMatrix = aMatrix * M)
    (hbM : M * bMatrix = bMatrix * M)
    (haN : N * aMatrix = aMatrix * N)
    (hbN : N * bMatrix = bMatrix * N)
    (hzero : ∀ j, M 0 j = N 0 j) : M = N := by
  apply Matrix.ext
  intro i
  induction i using Fin.strong_induction_on with
  | h i ih =>
    by_cases hi : i = 0
    · exact hi ▸ hzero
    obtain ⟨p, hp, hG | hG⟩ := basisRow_predecessor i hi
    · exact row_step aMatrix M N haM haN p i hG (ih p hp)
    · exact row_step bMatrix M N hbM hbN p i hG (ih p hp)

/-- A commuting matrix whose zeroth row is scalar is that scalar matrix. -/
public theorem commuting_matrix_eq_scalar_of_row_zero
    (M : Matrix133) (ha : M * aMatrix = aMatrix * M)
    (hb : M * bMatrix = bMatrix * M) (c : ZMod 5)
    (hzero : ∀ j, M 0 j = if j = 0 then c else 0) :
    M = c • (1 : Matrix133) := by
  apply commuting_matrix_ext_row_zero M (c • (1 : Matrix133)) ha hb
  · simp only [Matrix.smul_mul, Matrix.mul_smul, one_mul, mul_one]
  · simp only [Matrix.smul_mul, Matrix.mul_smul, one_mul, mul_one]
  · intro j
    simp only [hzero, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    simp only [eq_comm, mul_ite, mul_one, mul_zero]

end HaradaNorton
