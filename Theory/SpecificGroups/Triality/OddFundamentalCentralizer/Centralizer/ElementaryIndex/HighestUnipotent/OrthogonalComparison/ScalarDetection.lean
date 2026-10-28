module
public import Theory.SpecificGroups.Triality.OddFundamentalCentralizer.Centralizer.ElementaryIndex.HighestUnipotent.OrthogonalComparison.Natural

/-!
# Scalar detection on the signed D4 adjoint image

Eight of the signed integral root columns already have scalar commutant.
Three columns multiply, up to sign, to the first coordinate projection;
further root words turn that projection into every matrix unit in its column.
Commuting with these units forces all off-diagonal entries to vanish and all
diagonal entries to agree. The calculation is integral and works over every
commutative coefficient ring.

An elementary isometry fixing the embedded adjoint coordinates therefore acts
as a scalar on the natural eight-space. The existing split scalar-kernel test
uses its quadratic-isometry condition and the vector `e 0 + f 0`, of quadratic
value one, to show that this scalar has square one. Thus its image in the
literal scalar quotient is the identity, including in characteristic three.
No comparison of group models or natural pinning is assumed here.

Sources: GLS3 §§2.4, 2.6–2.7, especially the even-orthogonal root matrices in
`refs/KGroup/GLS3/chapter2.tex`; the triality comparison used in Aschbacher–Smith
A.2.17, printed pp.38–39, in `refs/quasithin.pdf`.
-/

@[expose] public section
noncomputable section
open Matrix
namespace Triality.Standard.OddFundamentalCentralizer.ElementaryIndex.HighestUnipotent.OrthogonalComparison

private theorem root_product : basisMatrix 5 * basisMatrix 17 =
    -single (.inl 0) (.inl 2) (1 : ℤ) := by decide +kernel

private theorem projection_product :
    -(single (.inl 0) (.inl 2) (1 : ℤ)) * basisMatrix 10 =
      -single (.inl 0) (.inl 0) (1 : ℤ) := by decide +kernel

private theorem projection_word : -(basisMatrix 5 * basisMatrix 17 * basisMatrix 10) =
    single (.inl 0) (.inl 0) (1 : ℤ) := by
  rw [root_product, projection_product, neg_neg]

private def columnWord : NaturalIndex → NaturalMatrix ℤ
  | .inl i => ![1, basisMatrix 6, basisMatrix 10, basisMatrix 14] i
  | .inr i => ![-basisMatrix 7 * basisMatrix 6, basisMatrix 7,
      -basisMatrix 11, basisMatrix 15] i

private theorem columnWord_projection (i : NaturalIndex) :
    columnWord i * single (.inl 0) (.inl 0) (1 : ℤ) = single i (.inl 0) 1 := by
  rcases i with i | i <;> fin_cases i <;> decide +kernel

variable {R : Type*} [CommRing R]

private theorem cast_single (i j : NaturalIndex) :
    castMatrix R (single i j (1 : ℤ)) = single i j (1 : R) := by
  change (single i j (1 : ℤ)).map (Int.castRingHom R) = _
  rw [Matrix.map_single, map_one]

private theorem commute_projection (M : NaturalMatrix R)
    (h : ∀ c, Commute M (castMatrix R (basisMatrix c))) :
    Commute M (single (.inl 0) (.inl 0) 1) := by
  have hproj := ((h 5).mul_right (h 17)).mul_right (h 10)
  have he : -(castMatrix R (basisMatrix 5) * castMatrix R (basisMatrix 17) *
      castMatrix R (basisMatrix 10)) = single (.inl 0) (.inl 0) 1 := by
    rw [← map_mul, ← map_mul, ← map_neg, projection_word, cast_single]
  rw [← he]
  exact hproj.neg_right

private theorem commute_columnWord (M : NaturalMatrix R)
    (h : ∀ c, Commute M (castMatrix R (basisMatrix c))) (i : NaturalIndex) :
    Commute M (castMatrix R (columnWord i)) := by
  rcases i with i | i
  · fin_cases i
    · simp [columnWord]
    · simpa [columnWord] using h 6
    · simpa [columnWord] using h 10
    · simpa [columnWord] using h 14
  · fin_cases i
    · simpa [columnWord] using (h 7).neg_right.mul_right (h 6)
    · simpa [columnWord] using h 7
    · simpa [columnWord] using (h 11).neg_right
    · simpa [columnWord] using h 15

private theorem commute_column_single (M : NaturalMatrix R)
    (h : ∀ c, Commute M (castMatrix R (basisMatrix c))) (i : NaturalIndex) :
    Commute M (single i (.inl 0) 1) := by
  have hc := (commute_columnWord M h i).mul_right (commute_projection M h)
  rw [← cast_single, ← map_mul, columnWord_projection, cast_single] at hc
  exact hc

/-- Commuting with the actual signed root columns forces a natural matrix to be scalar. -/
theorem scalar_of_commute_basisMatrix (M : NaturalMatrix R)
    (h : ∀ c, Commute M (castMatrix R (basisMatrix c))) :
    ∃ c : R, M = c • (1 : NaturalMatrix R) := by
  refine ⟨M (.inl 0) (.inl 0), ?_⟩
  ext i j
  by_cases hij : i = j
  · subst j
    simpa using Matrix.diag_eq_of_commute_single (commute_column_single M h i).symm
  · have hz := Matrix.col_eq_zero_of_commute_single
      (commute_column_single M h j).symm hij
    simpa [hij] using hz

open ClassicalOrthogonal
variable (F : Type*) [Field F]

/-- Faithfulness modulo the literal scalar subgroup, tested only on the signed image. -/
theorem scalarDetection : ScalarDetection F := by
  intro x hx
  have hcomm (c : Fin 28) :
      Commute (naturalMatrix F x) (castMatrix F (basisMatrix c)) := by
    change naturalMatrix F x * castMatrix F (basisMatrix c) =
      castMatrix F (basisMatrix c) * naturalMatrix F x
    have hc := hx (Pi.single c 1)
    rw [embedding_single, conjugation_apply] at hc
    have hmul := congrArg (fun M => M * naturalMatrix F x) hc
    simpa only [mul_assoc, ← map_mul, inv_mul_cancel, map_one, mul_one] using hmul
  obtain ⟨c, hc⟩ := scalar_of_commute_basisMatrix (naturalMatrix F x) hcomm
  apply (projectivePlus_scalar_kernel (by decide : 0 < 4) x).mpr
  refine ⟨c, fun v => ?_⟩
  rw [← naturalMatrix_mulVec, hc, Matrix.smul_mulVec, Matrix.one_mulVec]

/-- The requested parameter specialization, including characteristic three and exponent one. -/
theorem scalarDetection_extensionField (P : Parameters) (_hp : Odd P.prime) :
    ScalarDetection (ExtensionField P) := scalarDetection (ExtensionField P)

/-- The projective signed adjoint image detects the identity in the actual quotient. -/
theorem projective_eq_one_of_fixes_embedding (x : POmegaPlus 4 F)
    (hx : ∀ v, projectiveAdjoint F x (embedding F v) = embedding F v) : x = 1 :=
  projective_detect F (scalarDetection F) x hx

end Triality.Standard.OddFundamentalCentralizer.ElementaryIndex.HighestUnipotent.OrthogonalComparison
