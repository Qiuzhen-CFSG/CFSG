module
public import Theory.SpecificGroups.Suzuki.SchurEightCover.AtlasModel.MatrixComparison.ActionComparison.Witnesses
/-!
# Faithfulness of the checked row-line action

Compatibility means that `row (p i) * g` is a nonzero scalar multiple of
`row i`. This relation is closed under ordinary products and inverses.
Distinct normalized rows make its permutation coordinate faithful. In the
other direction, the four frame rows and their sum force a matrix fixing
every line to be scalar. The checked field arithmetic excludes every
nonidentity scalar of determinant one.

These lemmas are applied to the simultaneous generated subgroup in
`ActionComparison.lean`; no order or native generation theorem is assumed.
Source: the concrete model comparison for Aschbacher–Smith I.1.1 and
I.1.3(5), printed p.407; numerical attribution in `AtlasModel/source/README.md`.
-/

@[expose] public section
namespace BenderSuzuki.MatrixGroups.SchurEightCover.AtlasModel.MatrixComparison.ActionComparison
open Matrix

/-- Compatibility of an ordinary matrix with the inverse right action on lines. -/
def Compatible (p : Equiv.Perm (Fin 65)) (g : GL8) : Prop :=
  ∀ i, ∃ c : F8, c ≠ 0 ∧ row (p i) ᵥ* (g : Mat) = c • row i

theorem compatible_one : Compatible 1 1 := by
  intro i
  exact ⟨1, one_ne_zero, by simp⟩

theorem Compatible.mul {p q : Equiv.Perm (Fin 65)} {g h : GL8}
    (hp : Compatible p g) (hq : Compatible q h) : Compatible (p * q) (g * h) := by
  intro i
  obtain ⟨c, hc, he⟩ := hp (q i)
  obtain ⟨d, hd, hf⟩ := hq i
  refine ⟨c * d, mul_ne_zero hc hd, ?_⟩
  change row (p (q i)) ᵥ* ((g : Mat) * (h : Mat)) = _
  rw [← vecMul_vecMul, he, smul_vecMul, hf, mul_smul]

theorem Compatible.inv {p : Equiv.Perm (Fin 65)} {g : GL8}
    (hp : Compatible p g) : Compatible p⁻¹ g⁻¹ := by
  intro i
  obtain ⟨c, hc, he⟩ := hp (p⁻¹ i)
  have he' := congrArg (fun v => v ᵥ* ((g⁻¹ : GL8) : Mat)) he
  simp [vecMul_vecMul, smul_vecMul] at he'
  refine ⟨c⁻¹, inv_ne_zero hc, ?_⟩
  have := congrArg (fun v => c⁻¹ • v) he'
  simpa [← mul_smul, hc] using this.symm

theorem pointRow_line_injective {i j : Fin 65} {c : F8}
    (h : pointRow i = c • pointRow j) : i = j := by
  by_cases hi : i = 2
  · by_contra hj
    have hj' : j ≠ 2 := by intro h'; exact hj (hi.trans h'.symm)
    have hc : c = 0 := by
      have h0 := congrFun h 0
      simpa [hi, pointRow_two, pointRow_first j hj'] using h0.symm
    have h3 := congrFun h 3
    simp [hi, pointRow_two, hc] at h3
  · by_cases hj : j = 2
    · have h0 := congrFun h 0
      simp [hj, pointRow_two, pointRow_first i hi] at h0
    · have hc : c = 1 := by
        have h0 := congrFun h 0
        simpa [pointRow_first i hi, pointRow_first j hj] using h0.symm
      exact pointRow_injective (by simpa [hc] using h)

theorem Compatible.perm_eq_one {p : Equiv.Perm (Fin 65)}
    (hp : Compatible p 1) : p = 1 := by
  apply Equiv.ext
  intro i
  obtain ⟨c, _, hc⟩ := hp i
  apply pointEquiv.injective
  apply pointRow_line_injective (c := c)
  simpa [row] using hc

private def frame : Mat := !![1,0,0,0; 1,1,0,1; 0,0,0,1; 1,0,1,1]
private def frameInv : Mat := !![1,0,0,0; 1,1,1,0; 1,0,1,1; 0,0,1,0]
private theorem frame_inv : frameInv * frame = 1 := by decide +kernel
private theorem frame_row (i : Fin 4) : frame i = row (![62,49,25,11] i) := by
  fin_cases i <;> exact (by decide +kernel)
private theorem frame_sum : row 59 = row 62 + row 49 + row 25 + row 11 := by
  rw [row_frame.1, row_frame.2.1, row_frame.2.2.1, row_frame.2.2.2.1,
    row_frame.2.2.2.2]
  decide +kernel

theorem Compatible.scalar {g : GL8} (hg : Compatible 1 g) :
    ∃ c : F8, (g : Mat) = c • (1 : Mat) := by
  obtain ⟨c0, _, h0⟩ := hg 62
  obtain ⟨c1, _, h1⟩ := hg 49
  obtain ⟨c2, _, h2⟩ := hg 25
  obtain ⟨c3, _, h3⟩ := hg 11
  obtain ⟨c5, _, h5⟩ := hg 59
  change row 62 ᵥ* (g : Mat) = c0 • row 62 at h0
  change row 49 ᵥ* (g : Mat) = c1 • row 49 at h1
  change row 25 ᵥ* (g : Mat) = c2 • row 25 at h2
  change row 11 ᵥ* (g : Mat) = c3 • row 11 at h3
  change row 59 ᵥ* (g : Mat) = c5 • row 59 at h5
  have hs : c0 • row 62 + c1 • row 49 + c2 • row 25 + c3 • row 11 =
      c5 • row 59 := by
    rw [← h0, ← h1, ← h2, ← h3, ← add_vecMul, ← add_vecMul, ← add_vecMul,
      ← frame_sum]
    exact h5
  have hc1 : c1 = c5 := by
    simpa [row_frame.1, row_frame.2.1, row_frame.2.2.1,
      row_frame.2.2.2.1, row_frame.2.2.2.2] using congrFun hs 1
  have hc3 : c3 = c5 := by
    simpa [row_frame.1, row_frame.2.1, row_frame.2.2.1,
      row_frame.2.2.2.1, row_frame.2.2.2.2] using congrFun hs 2
  have hc0 : c0 = c5 := by
    simpa [row_frame.1, row_frame.2.1, row_frame.2.2.1,
      row_frame.2.2.2.1, row_frame.2.2.2.2, hc1, hc3, add_assoc,
      CharTwo.add_self_eq_zero] using congrFun hs 0
  have hc2 : c2 = c5 := by
    simpa [row_frame.1, row_frame.2.1, row_frame.2.2.1,
      row_frame.2.2.2.1, row_frame.2.2.2.2, hc1, hc3, add_assoc, add_left_comm,
      CharTwo.add_self_eq_zero] using congrFun hs 3
  have hm : frame * (g : Mat) = c5 • frame := by
    ext i j
    change (frame i ᵥ* (g : Mat)) j = c5 * frame i j
    rw [frame_row]
    fin_cases i
    · exact congrFun (hc0 ▸ h0) j
    · exact congrFun (hc1 ▸ h1) j
    · exact congrFun (hc2 ▸ h2) j
    · exact congrFun (hc3 ▸ h3) j
  refine ⟨c5, ?_⟩
  have := congrArg (fun M : Mat => frameInv * M) hm
  simpa only [← Matrix.mul_assoc, frame_inv, Matrix.one_mul, Matrix.mul_smul,
    frame_inv] using this

theorem Compatible.matrix_eq_one {g : GL8} (hg : Compatible 1 g)
    (hd : (g : Mat).det = 1) : g = 1 := by
  obtain ⟨c, hc⟩ := hg.scalar
  have hpow : c ^ 4 = 1 := by simpa [hc, det_smul] using hd
  have hc1 := fourth_root_one c hpow
  apply Units.ext
  simpa [hc1] using hc
end BenderSuzuki.MatrixGroups.SchurEightCover.AtlasModel.MatrixComparison.ActionComparison
