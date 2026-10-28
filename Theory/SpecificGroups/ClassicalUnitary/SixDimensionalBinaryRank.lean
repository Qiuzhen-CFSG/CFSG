module

public import Theory.SpecificGroups.ClassicalUnitary.SixDimensionalBinary
public import Theory.GroupTheory.PrimeRankWitness

/-!
# An elementary abelian subgroup of order 27 in U₆(2)

The nonzero elements of GF(4) form a group of order three. We embed three
copies in the fixed projective special unitary carrier by the diagonal matrix
`diag(a, b, c, (abc)⁻¹, 1, 1)`. Its determinant is one and every diagonal entry
has norm one for Frobenius conjugation. A scalar relating two such matrices
must be one, by the last coordinate, so the projective map is injective.
The resulting elementary abelian subgroup proves that the 3-rank is at least
three.

This is the unitary rank input for the Fischer centralizer sections in GLS3,
Table 5.3t (`refs/KGroup/GLS3/Chapter5(sec3-).tex`), used in the sporadic
elimination of Aschbacher--Smith, Lemma A.2.19, printed pp. 40--41.
-/

public section

open BenderSuzuki.MatrixGroups Matrix
namespace Theory.SpecificGroups.U6Two

private theorem units_card : Nat.card Fieldˣ = 3 := by
  rw [Nat.card_units, field_card]

private theorem units_cube (u : Fieldˣ) : u ^ 3 = 1 := by
  simpa only [units_card] using (pow_card_eq_one' (x := u))

private noncomputable def entries (a : Fin 3 → Fieldˣ) : Fin 6 → Fieldˣ :=
  ![a 0, a 1, a 2, (a 0 * a 1 * a 2)⁻¹, 1, 1]

private theorem entries_mul (a b : Fin 3 → Fieldˣ) (i : Fin 6) :
    entries (a * b) i = entries a i * entries b i := by
  fin_cases i <;> simp [entries, mul_comm, mul_left_comm, mul_assoc]

private noncomputable def diagonalGL (a : Fin 3 → Fieldˣ) : GL (Fin 6) Field where
  val := diagonal (fun i => (entries a i : Field))
  inv := diagonal (fun i => ((entries a i)⁻¹ : Field))
  val_inv := by simp [diagonal_mul_diagonal]
  inv_val := by simp [diagonal_mul_diagonal]

private theorem diagonalGL_mul (a b : Fin 3 → Fieldˣ) :
    diagonalGL (a * b) = diagonalGL a * diagonalGL b := by
  apply Units.ext
  change diagonal _ = diagonal _ * diagonal _
  rw [diagonal_mul_diagonal]
  congr 1
  funext i
  simp [entries_mul]

private theorem diagonalGL_mem (a : Fin 3 → Fieldˣ) :
    diagonalGL a ∈ form.specialSubgroup := by
  rw [HermitianForm.mem_specialSubgroup_iff]
  constructor
  · have hadj : form.conjTranspose (diagonalGL a : Matrix (Fin 6) (Fin 6) Field) =
        diagonal (fun i => (entries a i : Field) ^ 2) := by
      ext i j
      by_cases h : i = j
      · subst j
        simp [HermitianForm.conjTranspose, diagonalGL, form, conjugation_apply]
      · simp [HermitianForm.conjTranspose, diagonalGL, form, h, Ne.symm h]
    rw [hadj]
    change diagonal _ * 1 * diagonal _ = 1
    rw [mul_one, diagonal_mul_diagonal, diagonal_eq_one]
    funext i
    have hc := congrArg (fun u : Fieldˣ => (u : Field)) (units_cube (entries a i))
    simpa [pow_succ] using hc
  · apply Units.ext
    rw [GeneralLinearGroup.val_det_apply]
    change (diagonal (fun i => (entries a i : Field))).det = 1
    rw [det_diagonal]
    simp [entries, Fin.prod_univ_succ, ← mul_assoc]

private noncomputable def diagonalSpecial : (Fin 3 → Fieldˣ) →* form.specialSubgroup where
  toFun a := ⟨diagonalGL a, diagonalGL_mem a⟩
  map_one' := by
    apply Subtype.ext
    apply Units.ext
    change diagonal _ = 1
    rw [diagonal_eq_one]
    funext i
    fin_cases i <;> simp [entries]
  map_mul' a b := Subtype.ext (diagonalGL_mul a b)

/-- Three independent norm-one coordinates in the fixed projective SU₆ model. -/
noncomputable def diagonalEmbedding : (Fin 3 → Fieldˣ) →* Carrier :=
  project.comp diagonalSpecial

/-- The fixed last coordinate removes the scalar ambiguity in PGL. -/
theorem diagonalEmbedding_injective : Function.Injective diagonalEmbedding := by
  intro a b h
  have hp : ProjGenLinGroup.mk (diagonalGL a) = ProjGenLinGroup.mk (diagonalGL b) :=
    congrArg Subtype.val h
  obtain ⟨u, hu⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp hp
  have hm := congrArg (fun g : GL (Fin 6) Field => (g : Matrix (Fin 6) (Fin 6) Field)) hu
  change diagonal _ * (GeneralLinearGroup.scalar (Fin 6) u : Matrix (Fin 6) (Fin 6) Field) = diagonal _ at hm
  rw [GeneralLinearGroup.coe_scalar] at hm
  change diagonal _ * diagonal (fun _ => (u : Field)) = diagonal _ at hm
  rw [diagonal_mul_diagonal] at hm
  have hs : u = 1 := by
    apply Units.ext
    have he := congrArg (fun M : Matrix (Fin 6) (Fin 6) Field => M 5 5) hm
    simpa [entries] using he
  subst u
  funext i
  apply Units.ext
  fin_cases i
  · simpa [entries] using congrArg (fun M : Matrix (Fin 6) (Fin 6) Field => M 0 0) hm
  · simpa [entries] using congrArg (fun M : Matrix (Fin 6) (Fin 6) Field => M 1 1) hm
  · simpa [entries] using congrArg (fun M : Matrix (Fin 6) (Fin 6) Field => M 2 2) hm

/-- U₆(2) contains an elementary abelian subgroup of order 27. -/
theorem three_le_primeRank : 3 ≤ primeRank 3 Carrier := by
  apply primeRank_ge_of_elementary_embedding (A := Fin 3 → Fieldˣ) (p := 3)
    (fun a => ?_) (by simp [Nat.card_fun, units_card])
    diagonalEmbedding diagonalEmbedding_injective
  funext i
  exact units_cube (a i)
end Theory.SpecificGroups.U6Two
