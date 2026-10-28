module

public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.GraphFieldFixedResidual.MatrixIdentification.Generators

/-!
# First-column reduction for graph-field fixed matrices

Every graph-field fixed matrix has its first column on the Suzuki ovoid.
Column orthogonality and the Plücker relation recover the omitted exterior-square
coordinate; the wedge identities then give the ovoid equation. If the last
coordinate vanishes, the middle coordinates vanish too. Otherwise a Suzuki root
matrix followed by the Weyl matrix moves the column onto the first coordinate
line. The Tits identity makes this calculation valid also over the binary field.

This supplies the first-column reduction used in identifying the full fixed
matrix subgroup with the concrete Suzuki subgroup.

Source: Aschbacher--Smith, 16.1.4(7), printed p.1171, and the Suzuki matrix
coordinates in Huppert--Blackburn III, XI.3.1--3.3 (upper-triangular convention).
-/

public section

open Matrix BenderSuzuki.MatrixGroups
namespace Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.GraphFieldFixedResidual.MatrixIdentification

/-- The first two columns are orthogonal for the antidiagonal form. -/
private theorem column_orthogonal (m : ℕ) (A : GL (Fin 4) (SuzukiField m))
    (hA : A ∈ fixedMatrixSubgroup m) :
    A.val 0 0 * A.val 3 1 + A.val 3 0 * A.val 0 1 =
      A.val 1 0 * A.val 2 1 + A.val 2 0 * A.val 1 1 := by
  have hsp := (nativeMatrix_symplectic_iff A.val).mpr
    ((mem_fixedMatrixSubgroup_iff m A).mp hA).1
  have htrans := SymplecticGroup.transpose_mem hsp
  have ht : nativeMatrix A.val.transpose ∈ Matrix.symplecticGroup (Fin 2) (SuzukiField m) := by
    simpa only [nativeMatrix, Matrix.transpose_submatrix] using htrans
  have hc : A.val.transpose * suzukiForm * A.val = suzukiForm := by
    simpa only [Matrix.transpose_transpose] using
      (nativeMatrix_symplectic_iff A.val.transpose).mp ht
  have he := congrArg (fun M => M 0 1) hc
  simp [Matrix.mul_apply, Fin.sum_univ_four, suzukiForm] at he
  apply CharTwo.add_eq_zero.mp
  calc
    _ = A.val 3 0 * A.val 0 1 + A.val 2 0 * A.val 1 1 +
        A.val 1 0 * A.val 2 1 + A.val 0 0 * A.val 3 1 := by ring
    _ = 0 := he

/-- The four fixed minor equations force the first column onto the Suzuki ovoid. -/
private theorem column_ovoid (m : ℕ) (a b c d e f g h : SuzukiField m)
    (ho : a * h + d * e = b * g + c * f)
    (h0 : a * f + b * e = suzukiTheta m a)
    (h1 : a * g + c * e = suzukiTheta m b)
    (h2 : b * h + d * f = suzukiTheta m c)
    (h3 : d * g + c * h = suzukiTheta m d) :
    (d = 0 → b = 0 ∧ c = 0) ∧
    (d ≠ 0 → a / d = (c / d) * (b / d) + suzukiTheta m (c / d) * (c / d) ^ 2 +
      suzukiTheta m (b / d)) := by
  let t := a * h + d * e
  -- The Plücker relation recovers the missing minor after applying the Tits map.
  have ht : suzukiTheta m t = a * d + b * c := by
    apply (suzukiTheta m).injective
    rw [suzukiTheta_twice, map_add, map_mul, map_mul, ← h0, ← h1, ← h2, ← h3]
    calc
      t ^ 2 = (a * h + d * e) * (b * g + c * f) := by rw [← ho, pow_two]
      _ = (a * f + b * e) * (d * g + c * h) + (a * g + c * e) * (b * h + d * f) := by
        ring_nf
        simp [CharTwo.ofNat_eq_mod]
  -- The wedge identities for the triples (1,2,3) and (0,1,2).
  have hw1 : b * suzukiTheta m d + c * suzukiTheta m c = d * t := by
    rw [← h3, ← h2]
    change _ = d * (a * h + d * e)
    rw [ho]
    ring_nf
    simp [CharTwo.ofNat_eq_mod]
  have hw0 : a * t + b * suzukiTheta m b + c * suzukiTheta m a = 0 := by
    rw [← h1, ← h0]
    change a * (a * h + d * e) + _ + _ = 0
    rw [ho]
    ring_nf
    simp [CharTwo.ofNat_eq_mod]
  constructor
  · intro hd
    have hc : c = 0 := by
      have hh : c * suzukiTheta m c = 0 := by simpa [hd] using hw1
      rcases mul_eq_zero.mp hh with hh | hh
      · exact hh
      · exact (suzukiTheta m).injective (by simpa using hh)
    have ht0 : t = 0 := (suzukiTheta m).injective (by simpa [hd, hc] using ht)
    have hb : b = 0 := by
      have hh : b * suzukiTheta m b = 0 := by simpa [ht0, hc] using hw0
      rcases mul_eq_zero.mp hh with hh | hh
      · exact hh
      · exact (suzukiTheta m).injective (by simpa using hh)
    exact ⟨hb, hc⟩
  · intro hd
    have htd : suzukiTheta m d ≠ 0 := (map_ne_zero_iff _ (suzukiTheta m).injective).mpr hd
    have hw := congrArg (suzukiTheta m) hw1
    simp only [map_add, map_mul, suzukiTheta_twice, ht] at hw
    have hh : a * d * suzukiTheta m d =
        b * c * suzukiTheta m d + suzukiTheta m c * c ^ 2 + suzukiTheta m b * d ^ 2 := by
      calc
        _ = suzukiTheta m d * (a * d + b * c) + b * c * suzukiTheta m d := by
          ring_nf
          simp [CharTwo.ofNat_eq_mod]
        _ = _ := by rw [← hw]; ring
    simp only [map_div₀]
    field_simp [hd, htd]
    linear_combination hh

/-- A Suzuki matrix moves the first column of any graph-field fixed matrix
onto the first coordinate line, for every parameter including zero. -/
theorem fixed_first_column_reduction (m : ℕ) (A : GL (Fin 4) (SuzukiField m))
    (hA : A ∈ fixedMatrixSubgroup m) :
    ∃ B : GL (Fin 4) (SuzukiField m), B ∈ SuzukiMatrixSubgroup m ∧
      (B * A).val 1 0 = 0 ∧ (B * A).val 2 0 = 0 ∧ (B * A).val 3 0 = 0 := by
  have hfix : coordinateGraph A.val = A.val.map (suzukiTheta m) :=
    ((mem_fixedMatrixSubgroup_iff m A).mp hA).2
  have hf (i : Fin 4) := congrArg (fun M => M i 0) hfix
  have h0 : A.val 0 0 * A.val 1 1 + A.val 1 0 * A.val 0 1 =
      suzukiTheta m (A.val 0 0) := by
    simpa [coordinateGraph, coordinateFirst, coordinateSecond, mul_comm] using hf 0
  have h1 : A.val 0 0 * A.val 2 1 + A.val 2 0 * A.val 0 1 =
      suzukiTheta m (A.val 1 0) := by
    simpa [coordinateGraph, coordinateFirst, coordinateSecond, mul_comm] using hf 1
  have h2 : A.val 1 0 * A.val 3 1 + A.val 3 0 * A.val 1 1 =
      suzukiTheta m (A.val 2 0) := by
    simpa [coordinateGraph, coordinateFirst, coordinateSecond, mul_comm] using hf 2
  have h3 : A.val 3 0 * A.val 2 1 + A.val 2 0 * A.val 3 1 =
      suzukiTheta m (A.val 3 0) := by
    simpa [coordinateGraph, coordinateFirst, coordinateSecond, mul_comm] using hf 3
  obtain ⟨hzero, hnonzero⟩ := column_ovoid m
    (A.val 0 0) (A.val 1 0) (A.val 2 0) (A.val 3 0)
    (A.val 0 1) (A.val 1 1) (A.val 2 1) (A.val 3 1)
    (column_orthogonal m A hA) h0 h1 h2 h3
  by_cases hd : A.val 3 0 = 0
  · obtain ⟨hb, hc⟩ := hzero hd
    exact ⟨1, (SuzukiMatrixSubgroup m).one_mem, by simpa using hb,
      by simpa using hc, by simpa using hd⟩
  · let x := A.val 2 0 / A.val 3 0
    let y := A.val 1 0 / A.val 3 0
    have ha : A.val 0 0 = (x * y + suzukiTheta m x * x ^ 2 + suzukiTheta m y) * A.val 3 0 :=
      (div_eq_iff hd).mp (hnonzero hd)
    have hb : A.val 1 0 = y * A.val 3 0 := (div_eq_iff hd).mp rfl
    have hc : A.val 2 0 = x * A.val 3 0 := (div_eq_iff hd).mp rfl
    refine ⟨SuzukiWeylGL m * SuzukiRootGL m x y, ?_, ?_⟩
    · apply (SuzukiMatrixSubgroup m).mul_mem
      · exact Subgroup.subset_closure (Or.inr (Or.inr rfl))
      · exact Subgroup.subset_closure (Or.inl ⟨x, y, rfl⟩)
    · change ((SuzukiWeylMatrix m * SuzukiRootMatrix m x y) * A.val) 1 0 = 0 ∧
        ((SuzukiWeylMatrix m * SuzukiRootMatrix m x y) * A.val) 2 0 = 0 ∧
        ((SuzukiWeylMatrix m * SuzukiRootMatrix m x y) * A.val) 3 0 = 0
      rw [Matrix.mul_assoc, rootMatrix_eq]
      simp [SuzukiWeylMatrix, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_four]
      rw [ha, hb, hc]
      constructor
      · ring_nf
        simp [CharTwo.ofNat_eq_mod]
      constructor
      · ring_nf
        simp [CharTwo.ofNat_eq_mod]
      · ring_nf
        simp [CharTwo.ofNat_eq_mod]

end Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.GraphFieldFixedResidual.MatrixIdentification
